import { type ChildProcess, spawn } from "node:child_process";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { getProcessStartId } from "../../../src/core/session-lease.js";
import {
	acquireDaemonSupervisorOwnership,
	assertDaemonSupervisorOwnerCurrent,
} from "../../../src/modes/daemon/daemon-supervisor-ownership.js";

// RECORDED-IDENTITY GAPS in the daemon supervisor owner record (#1291, #1148).
//
// Two narrow properties of the recorded identity itself. Both are about the
// record that acquireDaemonSupervisorOwnership mints, not about which process
// wins a race.
//
// (a) assertCurrent (daemon-supervisor-ownership.ts:130-138) compares DISK
//     against MEMORY and nothing else:
//         const current = readOwnerRecord(this.ownerDirectory);
//         if (!current || !sameOwnerRecord(current, this.record)) throw ...;
//     It never re-observes reality. No fresh getProcessStartId(process.pid) is
//     ever compared against this.record.processStartId, even though the file
//     already contains isProcessIdentityAlive (:521-530) and
//     matchesExactProcessIdentity (:532-537) to do exactly that. The record is
//     minted once at :309/:316 and trusted for the rest of the process's life.
//
// (b) The start id is spread CONDITIONALLY at :317:
//         ...(processStartId ? { processStartId } : {}),
//     so when getProcessStartId cannot observe it the field is OMITTED from the
//     record entirely. Every consumer in the file then reads that absence as
//     agreement - isProcessIdentityAlive returns true at :525-527 when
//     identity.processStartId is falsy, and matchesExactProcessIdentity does the
//     same at :536 - which degrades the fence to a bare pid check and reopens
//     the pid-reuse hole the start id exists to close.
//
// SCOPE NOTE for (a). DaemonSupervisorOwnership is constructed in exactly one
// place, :362, inside acquireDaemonSupervisorOwnership, whose sole caller is
// daemon-supervisor.ts. That function mints pid: process.pid (:316) and
// processStartId: getProcessStartId(process.pid) (:309). So the process running
// assertCurrent IS the process named in this.record, and a self-contradicting
// own record cannot arise through the production path. This test constructs it
// deliberately. What it pins is the ABSENCE OF THE CHECK, which is a property of
// assertCurrent regardless of who can reach it - not a user-facing defect.
// Gap (b) needs no such caveat: it is reached whenever `ps` is unavailable.
//
// SAFETY: every fixture is an mkdtemp registry exported through
// PRIME_AGENT_INTERNAL_DAEMON_SUPERVISOR_REGISTRY_DIR for the duration of the
// call and restored immediately afterwards. Nothing here reads, writes,
// connects to or unlinks anything under the developer's live
// $TMPDIR/prime-agent-<uid> tree. The only process signalled is the single idle
// child this file spawns itself.

const REGISTRY_DIR_ENV = "PRIME_AGENT_INTERNAL_DAEMON_SUPERVISOR_REGISTRY_DIR";
const BOGUS_START_ID = "ps:deliberately-not-the-real-start-id";

/**
 * PLATFORM PRECONDITION for gap (b).
 *
 * Gap (b) needs getProcessStartId(process.pid) to genuinely return undefined.
 * getProcessStartId reads /proc/<pid>/stat first (session-lease.ts:147-156) and
 * only falls through to execFileSync("ps", ...) (:158-163) when that read fails,
 * which is the macOS/BSD path. Emptying PATH therefore hides the start id on
 * macOS and does nothing on Linux, where /proc/<pid>/stat always succeeds.
 *
 * A process cannot make its own /proc/<pid>/stat unreadable: procfs rejects
 * chmod with EPERM even for the owning uid, hidepid never hides the reader's own
 * entry, and unmounting or shadowing /proc needs a mount namespace, i.e. root
 * (measured on Ubuntu 24.04 / kernel 6.8: chmod -> EPERM, `unshare -m` -> EPERM,
 * apparmor_restrict_unprivileged_userns=1). So on Linux the fixture cannot be
 * built honestly inside a unit test, and the gap (b) tests skip rather than
 * assert nothing. Gap (a) has no such dependency and runs everywhere.
 *
 * This is detected rather than hardcoded per platform: it directly measures the
 * precondition the fixture needs.
 */
function startIdCanBeHidden(): boolean {
	const previousPath = process.env.PATH;
	process.env.PATH = resolve(tmpdir(), "prime-agent-1291-no-such-bin");
	try {
		return getProcessStartId(process.pid) === undefined;
	} finally {
		if (previousPath === undefined) {
			delete process.env.PATH;
		} else {
			process.env.PATH = previousPath;
		}
	}
}

const CAN_HIDE_START_ID = startIdCanBeHidden();
/** Reads correctly whether the test ran or was skipped. */
const GAP_B_PRECONDITION = "requires an unobservable getProcessStartId; skipped where /proc/<pid>/stat resolves it";

/**
 * assertDaemonSupervisorOwnerCurrent takes no registryDir; it calls
 * defaultDaemonSupervisorRegistryDir() itself (:374), which reads this env var
 * and otherwise falls back to the developer's LIVE socket directory. The env var
 * is the only isolation seam, so it is set immediately before every call into
 * the module and restored immediately after.
 */
async function withRegistryEnv<T>(registryDir: string, action: () => Promise<T>): Promise<T> {
	const previous = process.env[REGISTRY_DIR_ENV];
	process.env[REGISTRY_DIR_ENV] = registryDir;
	try {
		return await action();
	} finally {
		if (previous === undefined) {
			delete process.env[REGISTRY_DIR_ENV];
		} else {
			process.env[REGISTRY_DIR_ENV] = previous;
		}
	}
}

function pidIsAlive(pid: number): boolean {
	try {
		process.kill(pid, 0);
		return true;
	} catch (error) {
		return (error as NodeJS.ErrnoException).code !== "ESRCH";
	}
}

interface IdentityGapFixture {
	root: string;
	registryDir: string;
	generation: string;
	ownerRecordPath: string;
	ownership: Awaited<ReturnType<typeof acquireDaemonSupervisorOwnership>>;
}

async function createIdentityGapFixture(
	generation: string,
	options: { hideStartId: boolean },
): Promise<IdentityGapFixture> {
	const root = mkdtempSync(join(tmpdir(), "prime-agent-1291-identity-"));
	const registryDir = resolve(root, "supervisor-owners");
	const descriptorDir = resolve(root, "descriptors");
	const agentDir = resolve(root, "agent");
	mkdirSync(registryDir, { recursive: true, mode: 0o700 });
	mkdirSync(descriptorDir, { recursive: true, mode: 0o700 });
	mkdirSync(agentDir, { recursive: true, mode: 0o700 });
	const previousPath = process.env.PATH;
	if (options.hideStartId) {
		// HONEST CONSTRUCTION of "getProcessStartId returned undefined at mint
		// time". On macOS and BSD, getProcessStartId falls through to
		// execFileSync("ps", ...) (session-lease.ts:158-163) after
		// /proc/<pid>/stat fails, and resolves "ps" through PATH. Pointing PATH at
		// a directory that does not exist makes that spawn fail with ENOENT, which
		// is precisely the unobservable case - no stub, no mock, no monkey-patch,
		// the real function taking its real failure path.
		process.env.PATH = resolve(root, "no-such-bin");
	}
	try {
		const ownership = await withRegistryEnv(registryDir, () =>
			acquireDaemonSupervisorOwnership({
				socketPath: resolve(root, "daemon.sock"),
				descriptorDir,
				agentDir,
				generation,
				appVersion: "test",
				registryDir,
			}),
		);
		return {
			root,
			registryDir,
			generation,
			ownerRecordPath: resolve(registryDir, `${generation}.owner`, "owner.json"),
			ownership,
		};
	} finally {
		if (previousPath === undefined) {
			delete process.env.PATH;
		} else {
			process.env.PATH = previousPath;
		}
	}
}

describe("supervisor recorded-identity gaps (#1291, #1148)", () => {
	let staleIdentity: IdentityGapFixture;
	let unfenced: IdentityGapFixture | undefined;
	let unfencedRawRecord: Record<string, unknown> | undefined;
	let startIdWasHonestlyUnobservable = false;
	let freshStartId: string | undefined;
	let previousRegistryDirEnv: string | undefined;
	/** A live process that never minted any record: stands in for a recycled pid. */
	let otherHolder: { pid: number; processStartId: string };
	let otherHolderChild: ChildProcess | undefined;

	beforeAll(async () => {
		previousRegistryDirEnv = process.env[REGISTRY_DIR_ENV];
		// A child WE own. Nothing in this file signals any other pid, ever.
		otherHolderChild = spawn(process.execPath, ["-e", "setTimeout(() => {}, 600000)"], { stdio: "ignore" });
		if (otherHolderChild.pid === undefined) {
			throw new Error("failed to spawn the stand-in process for a recycled pid");
		}
		otherHolder = {
			pid: otherHolderChild.pid,
			processStartId: getProcessStartId(otherHolderChild.pid) ?? `ps:other-${otherHolderChild.pid}`,
		};

		// (a) A record whose start id contradicts the live process, agreed on both
		// sides. sameOwnerRecord is satisfied; reality is never consulted.
		staleIdentity = await createIdentityGapFixture(`gen-stale-identity-${process.pid}`, { hideStartId: false });
		staleIdentity.ownership.record.processStartId = BOGUS_START_ID;
		writeFileSync(
			staleIdentity.ownerRecordPath,
			JSON.stringify({ ...staleIdentity.ownership.record, processStartId: BOGUS_START_ID }),
			{ mode: 0o600 },
		);
		freshStartId = getProcessStartId(process.pid);

		// (b) A record minted while the start id was genuinely unobservable. Only
		// constructible where the ps fallback is the sole source of the start id.
		if (CAN_HIDE_START_ID) {
			unfenced = await createIdentityGapFixture(`gen-unfenced-${process.pid}`, { hideStartId: true });
			unfencedRawRecord = JSON.parse(readFileSync(unfenced.ownerRecordPath, "utf8")) as Record<string, unknown>;
			startIdWasHonestlyUnobservable = unfenced.ownership.record.processStartId === undefined;
		}
	}, 120_000);

	afterAll(() => {
		otherHolderChild?.kill("SIGKILL");
		if (staleIdentity) {
			rmSync(staleIdentity.root, { recursive: true, force: true });
		}
		if (unfenced) {
			rmSync(unfenced.root, { recursive: true, force: true });
		}
		if (previousRegistryDirEnv === undefined) {
			delete process.env[REGISTRY_DIR_ENV];
		} else {
			process.env[REGISTRY_DIR_ENV] = previousRegistryDirEnv;
		}
	});

	it("VACUITY GUARD: the fixtures really are what the tests claim", () => {
		// Temp registries only. The developer's live daemon tree is never touched.
		expect(staleIdentity.registryDir.startsWith(tmpdir())).toBe(true);
		if (unfenced) {
			expect(unfenced.registryDir.startsWith(tmpdir())).toBe(true);
			expect(staleIdentity.registryDir).not.toBe(unfenced.registryDir);
		}
		// The stand-in holder is a real live process, and it is not us.
		expect(pidIsAlive(otherHolder.pid)).toBe(true);
		expect(otherHolder.pid).not.toBe(process.pid);
		// The env var is restored after every call into the module.
		expect(process.env[REGISTRY_DIR_ENV]).toBe(previousRegistryDirEnv);
		// PATH is restored after the hidden-start-id acquire.
		expect(getProcessStartId(process.pid)).toBeDefined();
	});

	// GAP (a) ----------------------------------------------------------------

	it("assertCurrent accepts a record whose start id contradicts the live process", async () => {
		// The contradiction is observable to the caller: it simply never looks.
		expect(freshStartId).toBeDefined();
		expect(freshStartId).not.toBe(BOGUS_START_ID);
		expect(staleIdentity.ownership.record.pid).toBe(process.pid);
		expect(staleIdentity.ownership.record.processStartId).toBe(BOGUS_START_ID);
		await expect(staleIdentity.ownership.assertCurrent()).resolves.toBeUndefined();
	});

	// SPEC. assertCurrent must re-observe the identity it claims rather than only
	// comparing disk against a record it minted once. Fails on current main
	// because :130-138 contains no call into the liveness machinery at all.
	// Flips to green exactly when the check is added. Never delete this test.
	it.fails("SPEC: assertCurrent must re-observe getProcessStartId(process.pid)", async () => {
		await expect(staleIdentity.ownership.assertCurrent()).rejects.toThrow();
	});

	// GAP (b) ----------------------------------------------------------------

	// Documents the skip above with the concrete platform fact, so a Linux reader
	// sees why the fixture is absent instead of an unexplained skip.
	it.runIf(!CAN_HIDE_START_ID)(
		"SKIP REASON for gap (b): /proc/<pid>/stat resolves the start id, so it cannot be hidden",
		() => {
			expect(getProcessStartId(process.pid)).toMatch(/^proc:/);
			expect(readFileSync(`/proc/${process.pid}/stat`, "utf8").length).toBeGreaterThan(0);
			// The Linux start id is field 22 of /proc/<pid>/stat, and it is the same
			// string the fence compares, so gap (a) above exercises the real format.
			expect(staleIdentity.ownership.record.processStartId).not.toBe(getProcessStartId(process.pid));
		},
	);

	it.skipIf(!CAN_HIDE_START_ID)(
		`an unobservable start id at mint time yields a record with no identity fence (${GAP_B_PRECONDITION})`,
		async () => {
			const fixture = unfenced;
			const rawRecord = unfencedRawRecord;
			if (!fixture || !rawRecord) {
				throw new Error("gap (b) fixture missing despite the start id being hideable");
			}
			expect(startIdWasHonestlyUnobservable).toBe(true);
			expect(fixture.ownership.record.processStartId).toBeUndefined();
			// Not merely undefined: the conditional spread at :317 omits the key.
			expect(Object.hasOwn(rawRecord, "processStartId")).toBe(false);
			expect(rawRecord.pid).toBe(process.pid);

			// The fence is now strictly weaker, and the real exported checker shows it.
			// Point the record at a pid held by a process that never minted it - the
			// pid-reuse shape - and compare two records that differ ONLY in whether the
			// start id is recorded.
			const withoutStartId = { ...rawRecord, pid: otherHolder.pid } as Record<string, unknown>;
			const withContradictingStartId = { ...withoutStartId, processStartId: BOGUS_START_ID };
			const claim = {
				generation: fixture.generation,
				pid: otherHolder.pid,
				socketPath: fixture.ownership.record.socketPath,
			};

			writeFileSync(fixture.ownerRecordPath, JSON.stringify(withContradictingStartId), { mode: 0o600 });
			await expect(
				withRegistryEnv(fixture.registryDir, () =>
					assertDaemonSupervisorOwnerCurrent({ ...claim, processStartId: BOGUS_START_ID }),
				),
			).rejects.toThrow();

			writeFileSync(fixture.ownerRecordPath, JSON.stringify(withoutStartId), { mode: 0o600 });
			await expect(
				withRegistryEnv(fixture.registryDir, () => assertDaemonSupervisorOwnerCurrent(claim)),
			).resolves.toEqual(expect.any(String));
		},
	);

	// SPEC. acquireDaemonSupervisorOwnership must not mint an owner record with no
	// identity fence. When getProcessStartId cannot observe the start id, a bare
	// pid is not a safe fence, because every consumer in this file reads an absent
	// start id as agreement (:525-527, :536). Fails on current main because :317
	// simply omits the field. Never delete this test.
	//
	// Skipped where the precondition cannot be built: without the skip it would
	// still be red on Linux, but for the wrong reason - the unbuildable fixture
	// rather than the missing fence - which is a vacuous it.fails.
	it.skipIf(!CAN_HIDE_START_ID).fails(
		`SPEC: acquire must not mint an owner record without a process identity fence (${GAP_B_PRECONDITION})`,
		() => {
			expect(startIdWasHonestlyUnobservable).toBe(true);
			expect(unfenced?.ownership.record.processStartId).toBeDefined();
		},
	);
});
