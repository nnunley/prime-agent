import {
	existsSync,
	mkdirSync,
	mkdtempSync,
	readdirSync,
	readFileSync,
	rmSync,
	statSync,
	unlinkSync,
	utimesSync,
	writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import type { DaemonSocketClient } from "../src/modes/daemon/active-session-state.js";
import {
	createDaemonCommandEnvelope,
	type DaemonCommand,
	type DaemonResponse,
} from "../src/modes/daemon/daemon-protocol.js";
import { DaemonSupervisor } from "../src/modes/daemon/daemon-supervisor.js";
import {
	acquireDaemonSupervisorOwnership,
	assertDaemonSupervisorOwnerCurrent,
} from "../src/modes/daemon/daemon-supervisor-ownership.js";
import { MutationDrainLatch } from "../src/modes/daemon/mutation-drain-latch.js";

// Dialectical proofs for the owner-record conflation reported in #1291 / #1148.
//
// daemon-supervisor-ownership.ts assertCurrent():
//     const current = readOwnerRecord(this.ownerDirectory);
//     if (!current || !sameOwnerRecord(current, this.record)) {
//         throw new DaemonSupervisorOwnershipLostError(this.record.generation);
//     }
//
// `!current` (record ABSENT) and `!sameOwnerRecord(...)` (record REPLACED by a
// different generation) are distinct causes with distinct correct responses:
//   ABSENT + our own process identity still alive => the record was destroyed
//     under a healthy owner (the macOS $TMPDIR reaper prunes files after ~3 days
//     while leaving directories and never stopping the daemon; the owner record
//     is the coldest file in the tree because it is only written on ownership
//     change). Correct response: RECOVERABLE - re-assert ownership and continue.
//   REPLACED by another live generation => genuine takeover. Correct response:
//     FATAL - stand down. Today's behaviour is already right for this case.
//
// Incident 2026-08-12T13:54:43Z: prepare_update_restart failed in 1.2s with
// {total:0, restored:0, resumed:0, failed:0}, the daemon was replaced 6 minutes
// later anyway, and the whole session tree was lost behind the message
// "Could not prepare daemon sessions for automatic resume; the previous daemon
// is still running (Daemon supervisor generation <g> no longer owns its
// registry entry)".

const REGISTRY_DIR_ENV = "PRIME_AGENT_INTERNAL_DAEMON_SUPERVISOR_REGISTRY_DIR";

interface OwnershipFixture {
	registryDir: string;
	socketPath: string;
	descriptorDir: string;
	agentDir: string;
	generation: string;
	ownership: Awaited<ReturnType<typeof acquireDaemonSupervisorOwnership>>;
}

const temporaryRoots: string[] = [];
const acquiredOwnerships: Array<Awaited<ReturnType<typeof acquireDaemonSupervisorOwnership>>> = [];
let previousRegistryDirEnv: string | undefined;

beforeEach(() => {
	previousRegistryDirEnv = process.env[REGISTRY_DIR_ENV];
});

afterEach(async () => {
	// Never leave a supervisor owner record behind, and never let a later test
	// (or the developer's live daemon) inherit our registry override.
	while (acquiredOwnerships.length > 0) {
		await acquiredOwnerships
			.pop()
			?.release()
			.catch(() => undefined);
	}
	if (previousRegistryDirEnv === undefined) delete process.env[REGISTRY_DIR_ENV];
	else process.env[REGISTRY_DIR_ENV] = previousRegistryDirEnv;
	while (temporaryRoots.length > 0) {
		const root = temporaryRoots.pop();
		if (root) rmSync(root, { recursive: true, force: true });
	}
});

/**
 * Every fixture gets a private mkdtemp registry and exports it through
 * PRIME_AGENT_INTERNAL_DAEMON_SUPERVISOR_REGISTRY_DIR, so nothing in this file
 * can read or mutate the developer's live registry under
 * $TMPDIR/prime-agent-<uid>/supervisor-owners.
 */
async function createOwnershipFixture(
	generation = `gen-${process.pid}-${temporaryRoots.length}`,
): Promise<OwnershipFixture> {
	const root = mkdtempSync(join(tmpdir(), "prime-agent-absence-proof-"));
	temporaryRoots.push(root);
	const registryDir = resolve(root, "supervisor-owners");
	const descriptorDir = resolve(root, "descriptors");
	const agentDir = resolve(root, "agent");
	mkdirSync(registryDir, { recursive: true, mode: 0o700 });
	mkdirSync(descriptorDir, { recursive: true, mode: 0o700 });
	mkdirSync(agentDir, { recursive: true, mode: 0o700 });
	process.env[REGISTRY_DIR_ENV] = registryDir;
	const socketPath = resolve(root, "daemon.sock");
	const ownership = await acquireDaemonSupervisorOwnership({
		socketPath,
		descriptorDir,
		agentDir,
		generation,
		appVersion: "test",
		registryDir,
	});
	acquiredOwnerships.push(ownership);
	return { registryDir, socketPath, descriptorDir, agentDir, generation, ownership };
}

function ownerDirectory(fixture: OwnershipFixture): string {
	return resolve(fixture.registryDir, `${fixture.generation}.owner`);
}

function ownerRecordPath(fixture: OwnershipFixture): string {
	return resolve(ownerDirectory(fixture), "owner.json");
}

/**
 * The macOS periodic $TMPDIR reaper deletes FILES that have not been accessed
 * recently and leaves the surrounding DIRECTORIES in place. It does not signal
 * the owning process. This helper reproduces exactly that shape.
 */
function simulateTmpdirFileReaper(root: string, shouldPrune: (path: string) => boolean = () => true): string[] {
	const pruned: string[] = [];
	for (const entry of readdirSync(root, { withFileTypes: true })) {
		const path = resolve(root, entry.name);
		if (entry.isDirectory()) {
			pruned.push(...simulateTmpdirFileReaper(path, shouldPrune));
			continue;
		}
		if (!shouldPrune(path)) continue;
		unlinkSync(path);
		pruned.push(path);
	}
	return pruned;
}

/** Genuine takeover: another live generation now owns the entry we read. */
function installReplacementOwnerRecord(fixture: OwnershipFixture): void {
	const now = new Date().toISOString();
	writeFileSync(
		ownerRecordPath(fixture),
		JSON.stringify({
			version: 1,
			role: "supervisor",
			token: "takeover-token",
			generation: `${fixture.generation}-successor`,
			// A live pid with the matching process start id: this process. The
			// successor is unambiguously alive, so standing down is correct.
			pid: process.pid,
			socketPath: fixture.socketPath,
			descriptorDir: fixture.descriptorDir,
			agentDir: fixture.agentDir,
			appVersion: "test",
			phase: "owner",
			createdAt: now,
			updatedAt: now,
		}),
		{ mode: 0o600 },
	);
}

type Outcome = { kind: "resolved" } | { kind: "threw"; name: string; code: unknown; message: string };

async function outcomeOf(action: () => Promise<unknown>): Promise<Outcome> {
	try {
		await action();
		return { kind: "resolved" };
	} catch (error) {
		return {
			kind: "threw",
			name: error instanceof Error ? error.name : typeof error,
			code: (error as { code?: unknown }).code,
			message: error instanceof Error ? error.message : String(error),
		};
	}
}

interface SupervisorHarness {
	handleLine(client: DaemonSocketClient, line: string): Promise<void>;
	write: ReturnType<typeof vi.fn>;
}

function socketClient(id: string): DaemonSocketClient {
	return { id, attachedActiveSessionIds: new Set(), capabilities: new Set() } as DaemonSocketClient;
}

/**
 * Constructor-bypass harness (same technique as daemon-supervisor-admission.test.ts):
 * the real constructor spawns watchers and binds a socket. Everything the
 * prepare_update_restart path touches is real, including the ownership object,
 * which is a genuine DaemonSupervisorOwnership backed by the fixture registry.
 */
function createSupervisorHarness(fixture: OwnershipFixture): SupervisorHarness {
	const write = vi.fn();
	return Object.assign(Object.create(DaemonSupervisor.prototype), {
		ready: Promise.resolve(),
		generation: fixture.generation,
		ownership: fixture.ownership,
		socketPath: fixture.socketPath,
		defaultSessionConfig: { agentDir: fixture.agentDir, cwd: fixture.agentDir },
		workers: new Map(),
		clients: new Set(),
		protocolClientIds: new WeakMap(),
		promptAdmissions: new Map(),
		mutationDrain: new MutationDrainLatch(),
		commandJournal: {
			lookup: vi.fn(() => undefined),
			begin: vi.fn(() => ({ status: "new" })),
			recordResult: vi.fn(),
			acknowledge: vi.fn(),
		},
		updateRestartPhase: undefined,
		write,
		log: vi.fn(),
	}) as SupervisorHarness;
}

async function prepareUpdateRestartThroughSupervisor(fixture: OwnershipFixture): Promise<DaemonResponse> {
	const supervisor = createSupervisorHarness(fixture);
	const client = socketClient("update-restart-client");
	const command = { id: "prepare-1", type: "prepare_update_restart" } satisfies DaemonCommand & { id: string };
	await supervisor.handleLine(client, JSON.stringify(createDaemonCommandEnvelope(command, command.id)));
	expect(supervisor.write).toHaveBeenCalledTimes(1);
	return supervisor.write.mock.calls[0]?.[1] as DaemonResponse;
}

describe("daemon supervisor registry absence vs takeover (#1291, #1148)", () => {
	describe("THESIS: an intact owner record keeps a healthy supervisor working", () => {
		it("THESIS: ownership.assertCurrent resolves while the owner record is intact", async () => {
			const fixture = await createOwnershipFixture();
			expect(existsSync(ownerRecordPath(fixture))).toBe(true);
			await expect(fixture.ownership.assertCurrent()).resolves.toBeUndefined();
		});

		it("THESIS: the exported assertDaemonSupervisorOwnerCurrent accepts the intact record", async () => {
			const fixture = await createOwnershipFixture();
			await expect(
				assertDaemonSupervisorOwnerCurrent({
					generation: fixture.generation,
					pid: fixture.ownership.record.pid,
					processStartId: fixture.ownership.record.processStartId,
					socketPath: fixture.socketPath,
				}),
			).resolves.toEqual(expect.any(String));
		});

		it("THESIS: prepare_update_restart completes through the real supervisor command path with an intact record", async () => {
			const fixture = await createOwnershipFixture();
			const response = await prepareUpdateRestartThroughSupervisor(fixture);
			expect(response).toMatchObject({ success: true, command: "prepare_update_restart" });
		});
	});

	describe("ANTITHESIS-A: the $TMPDIR reaper deletes the owner record under a live supervisor", () => {
		it("VACUITY GUARD: the reaper simulation removes owner.json and leaves every directory standing", async () => {
			const fixture = await createOwnershipFixture();
			const pruned = simulateTmpdirFileReaper(ownerDirectory(fixture), (path) => path.endsWith("owner.json"));

			expect(pruned).toEqual([ownerRecordPath(fixture)]);
			expect(existsSync(ownerRecordPath(fixture))).toBe(false);
			// Directory survives, sibling scope.json survives: this is a file prune,
			// not a registry teardown, and the supervisor process is untouched.
			expect(statSync(ownerDirectory(fixture)).isDirectory()).toBe(true);
			expect(existsSync(resolve(ownerDirectory(fixture), "scope.json"))).toBe(true);
			expect(existsSync(fixture.registryDir)).toBe(true);
		});

		// PINNING THE DEFECT (#1291, #1148). When the fix lands, exactly one
		// assertion in this test flips: assertCurrent must resolve because our own
		// process identity is still alive and the record is merely missing.
		it("ANTITHESIS-A: assertCurrent throws OwnershipLost today even though our process identity is alive [PINS DEFECT #1291]", async () => {
			const fixture = await createOwnershipFixture();
			// Our own identity - the one recorded in the file that just vanished -
			// is trivially alive: it is this very process.
			expect(fixture.ownership.record.pid).toBe(process.pid);
			simulateTmpdirFileReaper(ownerDirectory(fixture), (path) => path.endsWith("owner.json"));

			const outcome = await outcomeOf(() => fixture.ownership.assertCurrent());

			expect(outcome).toMatchObject({
				kind: "threw",
				name: "DaemonSupervisorOwnershipLostError",
				code: "supervisor_generation_stale",
			});
			expect((outcome as { message: string }).message).toContain(
				`Daemon supervisor generation ${fixture.generation} no longer owns its registry entry`,
			);
		});

		it("ANTITHESIS-A: prepare_update_restart loses every session with total=0 after the reaper [PINS DEFECT #1148]", async () => {
			const fixture = await createOwnershipFixture();
			simulateTmpdirFileReaper(ownerDirectory(fixture), (path) => path.endsWith("owner.json"));

			const response = await prepareUpdateRestartThroughSupervisor(fixture);

			// This is the incident verbatim: the handoff refuses, the caller reports
			// {total:0, restored:0, resumed:0, failed:0}, and the daemon is replaced
			// anyway a few minutes later.
			expect(response).toMatchObject({ success: false, command: "prepare_update_restart" });
			expect((response as { error: string }).error).toContain("no longer owns its registry entry");
		});
	});

	describe("ANTITHESIS-B: a genuine takeover by another live generation", () => {
		it("ANTITHESIS-B: assertCurrent throws when a different live generation owns the entry [MUST KEEP THROWING]", async () => {
			const fixture = await createOwnershipFixture();
			installReplacementOwnerRecord(fixture);

			const outcome = await outcomeOf(() => fixture.ownership.assertCurrent());

			expect(outcome).toMatchObject({
				kind: "threw",
				name: "DaemonSupervisorOwnershipLostError",
				code: "supervisor_generation_stale",
			});
		});

		it("ANTITHESIS-B: prepare_update_restart refuses after a genuine takeover [MUST KEEP REFUSING]", async () => {
			const fixture = await createOwnershipFixture();
			installReplacementOwnerRecord(fixture);

			const response = await prepareUpdateRestartThroughSupervisor(fixture);

			expect(response).toMatchObject({ success: false, command: "prepare_update_restart" });
			expect((response as { error: string }).error).toContain("no longer owns its registry entry");
		});
	});

	describe("SYNTHESIS: the two causes must be discriminated", () => {
		// EXECUTABLE SPECIFICATION OF THE FIX. Expected to fail on current main:
		// `!current || !sameOwnerRecord(...)` collapses both causes into one
		// throw, so the two outcomes are byte-identical. The fix flips this to
		// passing; a fix that merely suppresses the takeover error, or that
		// silently tolerates both, cannot satisfy it. Never delete this test.
		it.fails("SYNTHESIS: a reaped record under a live owner must NOT produce the same outcome as a live takeover", async () => {
			const reaped = await createOwnershipFixture("gen-reaped");
			simulateTmpdirFileReaper(ownerDirectory(reaped), (path) => path.endsWith("owner.json"));
			const reapedOutcome = await outcomeOf(() => reaped.ownership.assertCurrent());

			const takenOver = await createOwnershipFixture("gen-taken-over");
			installReplacementOwnerRecord(takenOver);
			const takeoverOutcome = await outcomeOf(() => takenOver.ownership.assertCurrent());

			// Discrimination, both branches pinned:
			// absent + our identity alive => recoverable, and ownership is rewritten.
			expect(reapedOutcome).toEqual({ kind: "resolved" });
			expect(existsSync(ownerRecordPath(reaped))).toBe(true);
			expect(JSON.parse(readFileSync(ownerRecordPath(reaped), "utf8"))).toMatchObject({
				token: reaped.ownership.record.token,
				generation: reaped.generation,
				pid: process.pid,
			});
			// replaced by a live generation => still fatal.
			expect(takeoverOutcome).toMatchObject({ kind: "threw", code: "supervisor_generation_stale" });
			expect(reapedOutcome).not.toEqual(takeoverOutcome);
		});

		// Anti-prune invariant of the proposed upstream fix (b): a live supervisor
		// must keep its owner record warm so the reaper never considers it cold.
		// No heartbeat writes the record today, so this fails on current main.
		it.fails("SYNTHESIS: a liveness check must advance the owner record mtime so the reaper never sees it as cold", async () => {
			const fixture = await createOwnershipFixture();
			const path = ownerRecordPath(fixture);
			const cold = new Date(Date.now() - 4 * 24 * 60 * 60 * 1000);
			utimesSync(path, cold, cold);
			const before = statSync(path).mtimeMs;

			await fixture.ownership.assertCurrent();

			expect(statSync(path).mtimeMs).toBeGreaterThan(before);
		});
	});

	describe("VACUITY GUARDS: the falsifiers, not the harness, are what break the thesis", () => {
		it("VACUITY GUARD: assertCurrent and prepare_update_restart both succeed when no falsifier is injected", async () => {
			const fixture = await createOwnershipFixture();

			await expect(fixture.ownership.assertCurrent()).resolves.toBeUndefined();
			const response = await prepareUpdateRestartThroughSupervisor(fixture);

			expect(response).toMatchObject({ success: true });
		});

		it("VACUITY GUARD: the takeover falsifier really replaces the record with a different live generation", async () => {
			const fixture = await createOwnershipFixture();
			installReplacementOwnerRecord(fixture);

			const record = JSON.parse(readFileSync(ownerRecordPath(fixture), "utf8")) as {
				generation: string;
				token: string;
				pid: number;
			};
			expect(record.generation).not.toBe(fixture.generation);
			expect(record.token).not.toBe(fixture.ownership.record.token);
			expect(() => process.kill(record.pid, 0)).not.toThrow();
		});
	});
});
