import { type ChildProcess, spawn } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { getProcessStartId } from "../../../src/core/session-lease.js";
import { assertDaemonSupervisorOwnerCurrent } from "../../../src/modes/daemon/daemon-supervisor-ownership.js";

// FINGERPRINT VALIDITY IS TIME-BOUNDED (#1300).
//
// assertDaemonSupervisorOwnerCurrent (daemon-supervisor-ownership.ts:369-390)
// short-circuits the identity re-probe when the caller presents a fingerprint
// equal to the one the record hashes to:
//     const fingerprint = ownerRecordFingerprint(current);
//     if (fingerprint !== validatedFingerprint && !isProcessIdentityAlive(current)) throw;
// The fingerprint hashes the RECORD BYTES. It says nothing about whether the
// process the record names is still the process that minted it. So a caller
// holding a fingerprint validated once keeps passing the fence forever, across
// arbitrary pid reuse, because the record on disk never changes.
//
// The ruling on #1300 is that a validated fingerprint is a TIME-BOUNDED proof:
// a validated-at timestamp enforced inside assertDaemonSupervisorOwnerCurrent,
// where a successful probe renews the window. A background prober is rejected
// unless the synchronous check fast-fails on a validation older than the TTL.
//
// CONSEQUENCE FOR TEST ORACLES. An oracle that scores every fingerprint
// short-circuit as fatal is only accidentally right. The short-circuit is
// correct inside the window and wrong outside it, so the oracle is
// time-dependent. This file therefore asserts three things and not one: the
// short-circuit succeeds where it should (thesis), it succeeds where it must
// not once the recorded identity is contradicted (antithesis, the bug), and it
// must fail once the validation is older than a TTL (spec, red today).
//
// WHY A CACHE EXISTS AT ALL. daemon-mode.ts:340 sets
// SUPERVISOR_FENCE_POLL_MS = 250, so the fence runs four times a second for the
// lifetime of the daemon. The identity probe underneath it is
// getProcessStartId, whose cost is wildly platform-dependent:
//   macOS   execFileSync("ps", ["-p", pid, "-o", "lstart="])
//           median 132.7 ms per call from node (min 127.5, n=100, loaded M-series
//           host). The bare `ps` binary is ~3.8 ms; the rest is node's spawn.
//   Linux   readFileSync("/proc/<pid>/stat") + parse
//           median 0.0090 ms per call (min 0.0088, n=2000, Ubuntu 24.04 / 6.8).
// Four unmemoised probes a second is ~0.5 s/s of spawn on macOS and ~36 us/s on
// Linux. That four-order-of-magnitude gap is the whole tradeoff: the cache is
// load-bearing on macOS and nearly free to drop on Linux, and a TTL is what
// makes the macOS cache safe rather than unbounded.
//
// SAFETY: every call runs against an mkdtemp registry exported through
// PRIME_AGENT_INTERNAL_DAEMON_SUPERVISOR_REGISTRY_DIR and restored immediately
// afterwards; see the isolation vacuity guard below, which proves the function
// reads that directory. Nothing here reads, writes, connects to or unlinks
// anything under the developer's live $TMPDIR/prime-agent-<uid> tree. The only
// process signalled is the single idle child this file spawns itself, checked by
// pid AND process start id immediately before the signal.

const REGISTRY_DIR_ENV = "PRIME_AGENT_INTERNAL_DAEMON_SUPERVISOR_REGISTRY_DIR";
const CONTRADICTING_START_ID = "ps:deliberately-not-this-process-start-id";
/** Arbitrary but concrete, so the spec below names a number rather than a mood. */
const PROPOSED_FINGERPRINT_TTL_MS = 5_000;

interface OwnerRecordShape {
	version: number;
	role: "supervisor";
	token: string;
	generation: string;
	pid: number;
	processStartId?: string;
	socketPath: string;
	descriptorDir: string;
	agentDir: string;
	appVersion: string;
	phase: string;
	createdAt: string;
	updatedAt: string;
}

/**
 * The single isolation seam. assertDaemonSupervisorOwnerCurrent takes no
 * registryDir and calls defaultDaemonSupervisorRegistryDir() itself (:374),
 * which reads this env var and otherwise falls back to the developer's LIVE
 * socket directory.
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

/**
 * readOwnerRecord JSON.parses owner.json and ownerRecordFingerprint (:592)
 * hashes JSON.stringify of the result, so for compact JSON with no reordering
 * the fingerprint is the sha256 of the exact bytes written. That equality is
 * what the isolation guard below checks: a fingerprint the test computed from
 * its own bytes can only come back if the function read the test's file.
 */
function writeOwnerRecord(registryDir: string, record: OwnerRecordShape): string {
	const directory = resolve(registryDir, `${record.generation}.owner`);
	mkdirSync(directory, { recursive: true, mode: 0o700 });
	const bytes = JSON.stringify(record);
	writeFileSync(resolve(directory, "owner.json"), bytes, { mode: 0o600 });
	return createHash("sha256").update(bytes).digest("hex");
}

function pidIsAlive(pid: number): boolean {
	try {
		process.kill(pid, 0);
		return true;
	} catch (error) {
		return (error as NodeJS.ErrnoException).code !== "ESRCH";
	}
}

/**
 * The signature the #1300 ruling requires: the caller states WHEN the
 * fingerprint was validated, and the callee fast-fails when that is older than
 * the TTL. assertDaemonSupervisorOwnerCurrent accepts no such argument today, so
 * this cast is the honest way to state the specification - a function of fewer
 * parameters is assignable here, which is exactly why the spec test below is red:
 * the extra argument is silently ignored.
 */
type TimeBoundedOwnerCheck = (
	owner: { generation: string; pid: number; processStartId?: string; socketPath: string },
	validatedFingerprint?: string,
	validatedAtMs?: number,
) => Promise<string>;

describe("supervisor owner fingerprint validity is time-bounded (#1300)", () => {
	let root: string;
	let registryDir: string;
	let decoyRegistryDir: string;
	let socketPath: string;
	let holderChild: ChildProcess | undefined;
	/** A live process we spawned, standing in for the process a record names. */
	let holder: { pid: number; processStartId: string };
	let previousRegistryDirEnv: string | undefined;

	function baseRecord(generation: string, overrides: Partial<OwnerRecordShape>): OwnerRecordShape {
		const now = new Date().toISOString();
		return {
			version: 1,
			role: "supervisor",
			token: "00000000-0000-4000-8000-000000000000",
			generation,
			pid: holder.pid,
			socketPath,
			descriptorDir: resolve(root, "descriptors"),
			agentDir: resolve(root, "agent"),
			appVersion: "test",
			phase: "owner",
			createdAt: now,
			updatedAt: now,
			...overrides,
		};
	}

	beforeAll(() => {
		previousRegistryDirEnv = process.env[REGISTRY_DIR_ENV];
		root = mkdtempSync(join(tmpdir(), "prime-agent-1300-fingerprint-"));
		registryDir = resolve(root, "supervisor-owners");
		decoyRegistryDir = resolve(root, "decoy-owners");
		socketPath = resolve(root, "daemon.sock");
		mkdirSync(registryDir, { recursive: true, mode: 0o700 });
		mkdirSync(decoyRegistryDir, { recursive: true, mode: 0o700 });

		holderChild = spawn(process.execPath, ["-e", "setTimeout(() => {}, 600000)"], { stdio: "ignore" });
		if (holderChild.pid === undefined) {
			throw new Error("failed to spawn the process that the owner records name");
		}
		const observed = getProcessStartId(holderChild.pid);
		if (!observed) {
			throw new Error("cannot observe the start id of the spawned holder; the fixture would be vacuous");
		}
		holder = { pid: holderChild.pid, processStartId: observed };
	}, 60_000);

	afterAll(() => {
		// Signal only the pid we spawned, and only if it is still the process we
		// spawned: pid AND start id are rechecked immediately before the signal.
		const child = holderChild;
		if (
			child?.pid !== undefined &&
			pidIsAlive(child.pid) &&
			getProcessStartId(child.pid) === holder?.processStartId
		) {
			child.kill("SIGKILL");
		}
		if (root) {
			rmSync(root, { recursive: true, force: true });
		}
		if (previousRegistryDirEnv === undefined) {
			delete process.env[REGISTRY_DIR_ENV];
		} else {
			process.env[REGISTRY_DIR_ENV] = previousRegistryDirEnv;
		}
	});

	// VACUITY GUARDS ---------------------------------------------------------

	it("VACUITY GUARD: the call reads this test's registry and not the developer's live one", async () => {
		const generation = `gen-isolation-${process.pid}`;
		const record = baseRecord(generation, { processStartId: holder.processStartId });
		const expectedFingerprint = writeOwnerRecord(registryDir, record);
		const claim = { generation, pid: holder.pid, processStartId: holder.processStartId, socketPath };

		// POSITIVE: the returned fingerprint is the sha256 of bytes this test wrote,
		// so the function demonstrably read this test's file.
		await expect(withRegistryEnv(registryDir, () => assertDaemonSupervisorOwnerCurrent(claim))).resolves.toBe(
			expectedFingerprint,
		);

		// NEGATIVE: the identical call against an empty decoy finds no record.
		await expect(
			withRegistryEnv(decoyRegistryDir, () => assertDaemonSupervisorOwnerCurrent(claim)),
		).rejects.toThrow();

		// The seam is temp-only and restored.
		expect(registryDir.startsWith(tmpdir())).toBe(true);
		expect(process.env[REGISTRY_DIR_ENV]).toBe(previousRegistryDirEnv);
	});

	it("VACUITY GUARD: the recycled-pid fixture is a live process whose real start id contradicts the record", () => {
		// Pid reuse cannot be forced reliably, so the equivalent is constructed
		// directly: a record naming a process this test spawned and is still alive,
		// carrying a start id that is NOT that process's real one. The fence sees
		// exactly what it would see after a pid was recycled.
		expect(pidIsAlive(holder.pid)).toBe(true);
		expect(holder.pid).not.toBe(process.pid);
		const observed = getProcessStartId(holder.pid);
		expect(observed).toBe(holder.processStartId);
		// The contradiction is observable to anyone who looks.
		expect(observed).not.toBe(CONTRADICTING_START_ID);
	});

	// THESIS -----------------------------------------------------------------

	it("THESIS: a matching fingerprint succeeds when the recorded identity is genuinely alive", async () => {
		const generation = `gen-thesis-${process.pid}`;
		const fingerprint = writeOwnerRecord(
			registryDir,
			baseRecord(generation, { processStartId: holder.processStartId }),
		);
		const claim = { generation, pid: holder.pid, processStartId: holder.processStartId, socketPath };

		// Healthy path with no fingerprint at all: the full probe agrees. This is
		// what proves the antithesis below is not passing through a broken harness.
		await expect(withRegistryEnv(registryDir, () => assertDaemonSupervisorOwnerCurrent(claim))).resolves.toBe(
			fingerprint,
		);

		// And with the matching fingerprint, which is the case the cache exists for.
		await expect(
			withRegistryEnv(registryDir, () => assertDaemonSupervisorOwnerCurrent(claim, fingerprint)),
		).resolves.toBe(fingerprint);
	});

	// ANTITHESIS -------------------------------------------------------------

	it("ANTITHESIS: a matching fingerprint passes the fence even when the recorded identity is dead", async () => {
		const generation = `gen-antithesis-${process.pid}`;
		// pid is alive, but the recorded start id is not that process's: the
		// pid-reuse shape. Every field the first gate compares still agrees, so the
		// outcome turns entirely on the fingerprint short-circuit.
		const fingerprint = writeOwnerRecord(
			registryDir,
			baseRecord(generation, { processStartId: CONTRADICTING_START_ID }),
		);
		const claim = { generation, pid: holder.pid, processStartId: CONTRADICTING_START_ID, socketPath };

		// 1. Matching fingerprint: succeeds. THIS IS THE BUG (#1300). The record
		//    bytes are unchanged, so the hash still matches, and :386 returns before
		//    isProcessIdentityAlive is ever consulted.
		await expect(
			withRegistryEnv(registryDir, () => assertDaemonSupervisorOwnerCurrent(claim, fingerprint)),
		).resolves.toBe(fingerprint);

		// 2. Stale fingerprint: throws. Naming the mechanism - it is the EQUALITY of
		//    the fingerprint that bypasses the probe, not its presence.
		await expect(
			withRegistryEnv(registryDir, () =>
				assertDaemonSupervisorOwnerCurrent(
					claim,
					`${fingerprint.slice(0, -1)}${fingerprint.endsWith("0") ? "1" : "0"}`,
				),
			),
		).rejects.toThrow();

		// 3. No fingerprint: throws. So the probe underneath is working and does
		//    detect the contradiction; the short-circuit is what hides it.
		await expect(withRegistryEnv(registryDir, () => assertDaemonSupervisorOwnerCurrent(claim))).rejects.toThrow();
	});

	// SPEC -------------------------------------------------------------------

	// SPEC. The fingerprint short-circuit must expire. A caller presenting a
	// fingerprint it validated longer ago than the TTL must be re-probed, which is
	// exactly the case the antithesis above shows is unbounded today.
	//
	// THIS SPECIFIES A SIGNATURE CHANGE. assertDaemonSupervisorOwnerCurrent
	// currently takes (owner, validatedFingerprint?) and has no way to learn WHEN
	// the fingerprint was validated, so the third argument below is ignored and the
	// call resolves. It cannot be made to pass without adding the validated-at
	// parameter (or an equivalent, e.g. a caller-held validation handle) and
	// enforcing the TTL inside the function. Flips to green exactly when that
	// lands. Never delete this test.
	it.fails("SPEC: a fingerprint validated longer ago than the TTL must be re-probed", async () => {
		const generation = `gen-ttl-${process.pid}`;
		const fingerprint = writeOwnerRecord(
			registryDir,
			baseRecord(generation, { processStartId: CONTRADICTING_START_ID }),
		);
		const claim = { generation, pid: holder.pid, processStartId: CONTRADICTING_START_ID, socketPath };
		const validatedAtMs = Date.now() - PROPOSED_FINGERPRINT_TTL_MS * 2;

		const checkWithValidatedAt = assertDaemonSupervisorOwnerCurrent as TimeBoundedOwnerCheck;
		await expect(
			withRegistryEnv(registryDir, () => checkWithValidatedAt(claim, fingerprint, validatedAtMs)),
		).rejects.toThrow();
	});
});
