import { type ChildProcess, spawn } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { getProcessStartId } from "../../../src/core/session-lease.js";
import {
	acquireDaemonSupervisorOwnership,
	assertDaemonSupervisorOwnerCurrent,
} from "../../../src/modes/daemon/daemon-supervisor-ownership.js";

// EXHAUSTIVE DECISION-TABLE PROOF for #1291 / #1148.
//
// The two sibling files (1291-supervisor-registry-absence.test.ts and
// -e2e.test.ts) prove the INSTANCE: one reaped owner record destroys a live
// session tree. This file proves the CLASS. It enumerates the entire fact space
// that daemon-supervisor-ownership.ts assertCurrent() can observe, runs the REAL
// assertCurrent against REAL on-disk registry state for every point of that
// space, and compares the observed outcome against a total oracle.
//
// Implementation under proof (daemon-supervisor-ownership.ts:133-141):
//     async assertCurrent(): Promise<void> {
//         if (this.released) throw new DaemonSupervisorOwnershipLostError(...);
//         const current = readOwnerRecord(this.ownerDirectory);
//         if (!current || !sameOwnerRecord(current, this.record)) throw ...;
//     }
// readOwnerRecord (:639-643) returns undefined for THREE distinct causes -
// missing file, JSON.parse failure, failed shape guard - and sameOwnerRecord
// (:582-590) compares exactly five fields. Neither branch consults the liveness
// machinery that already exists in this same file (isProcessAlive /
// isProcessIdentityAlive), so a destroyed record under a healthy owner and a
// genuine takeover by a live rival are indistinguishable at the call site.
//
// REACHABILITY (added after review): the fact space is enumerated in full, but
// not every point of it is reachable in production, and the artifact must not
// overstate the defect. acquireDaemonSupervisorOwnership mints the record in
// the CURRENT process - `pid: process.pid` (:316) and
// `processStartId: getProcessStartId(process.pid)` (:309) - and assertCurrent
// compares that frozen record against the file. A process executing
// assertCurrent is therefore alive by construction and its own start id cannot
// change while it holds the pid, so every own-identity-dead or own-start-id-
// mismatched shape below exists only because this harness assigns those fields.
// Likewise assertCurrent reads ownerDirectoryPath(registryDir,
// this.record.generation) (:602-607), and each supervisor instance mints its own
// generation UUID (daemon-supervisor.ts:605), writes atomically
// (writeJsonAtomically, :710-712) and mutates only under a token check
// (:291-299) - so no in-repo writer can leave a VALID record with DIFFERENT
// compared fields at our own generation path. Every case carries a reachability
// label and the report splits on it. The reachable divergences are exactly the
// absent/unparseable/wrong-shape collapse under a live owner.
//
// SAFETY: every case builds its own mkdtemp registry, exports it through
// PRIME_AGENT_INTERNAL_DAEMON_SUPERVISOR_REGISTRY_DIR for the duration of the
// case, and removes it afterwards. Nothing here reads, writes, connects to or
// unlinks anything under the developer's live $TMPDIR/prime-agent-<uid> tree.
// The only processes signalled are children this file spawned itself.

const REGISTRY_DIR_ENV = "PRIME_AGENT_INTERNAL_DAEMON_SUPERVISOR_REGISTRY_DIR";

// ---------------------------------------------------------------------------
// 1. THE FACT SPACE
// ---------------------------------------------------------------------------

/**
 * What readOwnerRecord() finds on disk. "unparseable" and "wrong-shape" are
 * listed separately from "absent" precisely because they are distinct physical
 * causes that the implementation collapses into the same `undefined`.
 */
type RecordState = "present" | "absent" | "unparseable" | "wrong-shape";

/** Exactly the fields sameOwnerRecord() compares. Order is fixed for determinism. */
const COMPARED_FIELDS = ["token", "generation", "pid", "processStartId", "socketPath"] as const;
type ComparedField = (typeof COMPARED_FIELDS)[number];

/** Liveness of the identity WE claim in our own in-memory record. */
type PidLiveness = "alive" | "dead";

/** Agreement between our claimed processStartId and the real one for that pid. */
type StartIdAgreement = "matches" | "mismatches" | "absent-in-record";

interface Facts {
	readonly recordState: RecordState;
	/** Always empty unless recordState === "present" (see enumerateFacts). */
	readonly fieldMismatch: readonly ComparedField[];
	readonly pidLiveness: PidLiveness;
	readonly startIdAgreement: StartIdAgreement;
}

type Verdict = "recoverable" | "fatal";

/**
 * Whether a fact-shape can occur in production, or exists only because the
 * harness manufactured it. Enumeration is unaffected; the report splits on it.
 */
type Reachability = "reachable" | "unreachable-own-identity-minted" | "unreachable-generation-scoped-path";

function reachability(facts: Facts): Reachability {
	// acquireDaemonSupervisorOwnership sets pid: process.pid (:316) and
	// processStartId: getProcessStartId(process.pid) (:309), and nothing in the
	// repo rewrites them afterwards. The process running assertCurrent is
	// therefore alive with a matching (or unobservable) start id, always.
	if (facts.pidLiveness === "dead" || facts.startIdAgreement === "mismatches") {
		return "unreachable-own-identity-minted";
	}
	// assertCurrent looks only at OUR generation's directory. Generations are
	// per-supervisor-instance UUIDs, records are written atomically and mutated
	// only under a token check, so a valid record with different compared fields
	// cannot appear there. An external rebuild of the registry from durable
	// metadata (the #1296 proposal) is what would make this class reachable.
	if (facts.recordState === "present" && facts.fieldMismatch.length > 0) {
		return "unreachable-generation-scoped-path";
	}
	return "reachable";
}

function factKey(facts: Facts): string {
	const mismatch = facts.fieldMismatch.length === 0 ? "none" : facts.fieldMismatch.join("+");
	return `record=${facts.recordState} mismatch=${mismatch} pid=${facts.pidLiveness} startId=${facts.startIdAgreement}`;
}

/**
 * Full cross-product, deterministically ordered.
 *
 * DOCUMENTED COLLAPSE (the only one): fieldMismatch is a property of a record
 * that exists. When the record is absent, unparseable, or wrong-shape there is
 * no record to compare fields against - readOwnerRecord returns undefined
 * before sameOwnerRecord is ever reached - so all 32 subsets are the same
 * physical state. Those three record states therefore contribute exactly one
 * representative case each (the empty subset) instead of 32 identical ones.
 * This is a provable equivalence, not sampling: the mismatch axis is
 * unconstructible for a non-existent record.
 *
 * No other combination is skipped. In particular pidLiveness="dead" combined
 * with startIdAgreement="matches" IS constructible and IS enumerated: we
 * capture a child's real start id while it lives, then kill it.
 */
function enumerateFacts(): Facts[] {
	const recordStates: RecordState[] = ["present", "absent", "unparseable", "wrong-shape"];
	const pidLivenesses: PidLiveness[] = ["alive", "dead"];
	const startIdAgreements: StartIdAgreement[] = ["matches", "mismatches", "absent-in-record"];
	const subsets: ComparedField[][] = [];
	for (let mask = 0; mask < 1 << COMPARED_FIELDS.length; mask++) {
		subsets.push(COMPARED_FIELDS.filter((_, index) => (mask & (1 << index)) !== 0));
	}
	const facts: Facts[] = [];
	for (const recordState of recordStates) {
		const mismatches = recordState === "present" ? subsets : [[]];
		for (const fieldMismatch of mismatches) {
			for (const pidLiveness of pidLivenesses) {
				for (const startIdAgreement of startIdAgreements) {
					facts.push({ recordState, fieldMismatch, pidLiveness, startIdAgreement });
				}
			}
		}
	}
	return facts;
}

// ---------------------------------------------------------------------------
// 2. THE ORACLE (total: defined for every point of the fact space)
// ---------------------------------------------------------------------------

/**
 * Is the identity we claim in our own record actually us, and still running?
 * This mirrors isProcessIdentityAlive() in the implementation file, which
 * assertCurrent never calls.
 */
function ownIdentityIsAlive(facts: Facts): boolean {
	// PLATFORM NOTE: pidLiveness and startIdAgreement are INDEPENDENT axes and
	// are enumerated as such. getProcessStartId (src/core/session-lease.ts:140)
	// reads /proc/<pid>/stat on Linux and shells out to `ps` on macOS/BSD; for a
	// dead pid both return undefined, and isProcessIdentityAlive treats an
	// unobservable start id as agreement. So a dead pid fails ONLY the
	// isProcessAlive half, never the start-id half - which is exactly why the
	// two axes must not be assumed to co-occur. The verdict below is the same on
	// Linux CI and macOS because it takes pid liveness first.
	if (facts.pidLiveness === "dead") {
		return false;
	}
	// "absent-in-record" is alive-by-default in isProcessIdentityAlive: with no
	// recorded start id there is nothing to contradict, so a live pid stands.
	return facts.startIdAgreement !== "mismatches";
}

function decide(facts: Facts): Verdict {
	// RULE 4 first, because it dominates: if the identity we claim is not alive,
	// we are not who we say we are (dead pid, or a recycled pid now belonging to
	// somebody else). Re-asserting ownership from here would let a zombie claim
	// a socket. Fatal regardless of what is on disk.
	if (!ownIdentityIsAlive(facts)) {
		return "fatal";
	}
	// RULE 1: the record is gone (absent), corrupt (unparseable) or not a valid
	// owner record (wrong-shape) while our own identity is still alive. Nobody
	// took the entry; it was destroyed underneath a healthy owner - exactly the
	// macOS $TMPDIR file reaper shape from #1291, and equally a truncated or
	// partially written file. Recoverable: re-assert ownership and continue.
	if (facts.recordState !== "present") {
		return "recoverable";
	}
	// RULE 2: the record is present and every compared field is identical. This
	// is the ordinary no-op success path.
	if (facts.fieldMismatch.length === 0) {
		return "recoverable";
	}
	// RULE 3: the record is present and at least one compared field differs.
	// The entry on disk describes somebody else, and this file constructs that
	// somebody as a genuinely live rival (see perturbation policy below).
	// Genuine takeover: stand down. Today's behaviour is already correct here.
	return "fatal";
}

// ---------------------------------------------------------------------------
// 3. CONSTRUCTING EACH CASE AGAINST A REAL REGISTRY
// ---------------------------------------------------------------------------

interface OwnerRecordOnDisk {
	version: number;
	role: string;
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

interface ProcessIdentityFixture {
	pid: number;
	/** The start id the process really had, captured while it was running. */
	processStartId: string;
}

/** A start id no live process can have. Used for the CALLER-side record. */
const OWN_WRONG_START_ID = "ps:deliberately-not-the-real-start-id";
/** A different start id no live process can have. Used for the ON-DISK record. */
const RIVAL_WRONG_START_ID = "ps:rival-deliberately-not-the-real-start-id";

/** A live child process. The on-disk rival in table 1, the live record identity in table 2. */
let liveRival: ProcessIdentityFixture;
/** A dead child process, used as the identity OUR side claims. */
let deadOwn: ProcessIdentityFixture;
/** A second dead child process, used as the identity the ON-DISK record claims (table 2). */
let deadRival: ProcessIdentityFixture;
let ownStartId: string;
let previousRegistryDirEnv: string | undefined;

/** Every child this file ever spawned, so the teardown reaps all of them on any path. */
const spawnedChildren: ChildProcess[] = [];

function spawnIdleChild(): ChildProcess {
	// A child WE own. Nothing else in this file signals any pid.
	const child = spawn(process.execPath, ["-e", "setTimeout(() => {}, 600000)"], { stdio: "ignore" });
	spawnedChildren.push(child);
	return child;
}

function pidIsAlive(pid: number): boolean {
	try {
		process.kill(pid, 0);
		return true;
	} catch (error) {
		return (error as NodeJS.ErrnoException).code !== "ESRCH";
	}
}

function delay(ms: number): Promise<void> {
	return new Promise((resolveDelay) => setTimeout(resolveDelay, ms));
}

/**
 * Spawn a child whose real start id differs from every start id already in use.
 * getProcessStartId is `ps -o lstart=` on macOS (session-lease.ts:158-163),
 * which has one-second resolution, so two children spawned back to back can
 * legitimately share a start id. Several cases below need "the record's start
 * id differs from ours" to be a real difference, so we retry across a second
 * boundary rather than paper over a collision with a suffix.
 */
async function spawnLiveIdentity(
	taken: Set<string>,
): Promise<{ child: ChildProcess; identity: ProcessIdentityFixture }> {
	for (let attempt = 0; attempt < 4; attempt++) {
		const child = spawnIdleChild();
		const pid = child.pid;
		if (pid === undefined) {
			throw new Error("failed to spawn a child process for the identity fixtures");
		}
		const processStartId = getProcessStartId(pid);
		if (processStartId !== undefined && !taken.has(processStartId)) {
			return { child, identity: { pid, processStartId } };
		}
		// We only ever kill a pid we just created ourselves.
		child.kill("SIGKILL");
		await delay(1100);
	}
	throw new Error("could not obtain a process start id distinct from the other fixtures");
}

/**
 * A pid we can prove is dead: we spawn it, capture the start id it really had
 * while it lived (on macOS that value is unobservable once it exits), and kill
 * it. We only ever signal a pid this file created.
 */
async function createDeadIdentity(taken: Set<string>): Promise<ProcessIdentityFixture> {
	const { child, identity } = await spawnLiveIdentity(taken);
	await new Promise<void>((resolveExit) => {
		child.once("exit", () => resolveExit());
		// We only ever kill a pid we just created ourselves.
		child.kill("SIGKILL");
	});
	return identity;
}

/**
 * The real start id of a pid, without shelling out: the only pids this file
 * ever writes into a record are our own and the three children we spawned, and
 * their start ids are captured once and proved pairwise distinct in the vacuity
 * guards. A dead pid has no observable start id.
 */
function realStartIdOf(pid: number): string | undefined {
	if (pid === process.pid) {
		return ownStartId;
	}
	if (pid === liveRival.pid) {
		return liveRival.processStartId;
	}
	if (pid === deadOwn.pid || pid === deadRival.pid) {
		return undefined;
	}
	throw new Error(`a record names a pid this file never created: ${pid}`);
}

/**
 * The identity we claim in our own in-memory record, per the liveness axes.
 * pidLiveness/startIdAgreement describe OUR record, not the on-disk rival.
 */
function ownIdentityFor(facts: Facts): { pid: number; processStartId?: string } {
	const pid = facts.pidLiveness === "alive" ? process.pid : deadOwn.pid;
	switch (facts.startIdAgreement) {
		case "matches":
			// ownStartId is captured once: getProcessStartId shells out to `ps` on
			// macOS (~300ms), and our own start id cannot change mid-run.
			return {
				pid,
				processStartId: facts.pidLiveness === "alive" ? ownStartId : deadOwn.processStartId,
			};
		case "mismatches":
			return { pid, processStartId: OWN_WRONG_START_ID };
		case "absent-in-record":
			return { pid };
	}
}

/**
 * PERTURBATION POLICY for fieldMismatch. Rival liveness is deliberately NOT a
 * fifth axis: whenever a compared field differs we make the on-disk record
 * describe a genuinely live process we spawned (liveRival), so oracle RULE 3
 * ("live rival => fatal") applies uniformly and no case depends on an
 * unobservable dead-rival subtlety.
 */
function perturbedValue(field: ComparedField, own: OwnerRecordOnDisk): Partial<OwnerRecordOnDisk> {
	switch (field) {
		case "token":
			return { token: "rival-owner-token-0000" };
		case "generation":
			return { generation: `${own.generation}-successor` };
		case "pid":
			return { pid: liveRival.pid };
		case "processStartId": {
			const rival =
				liveRival.processStartId === own.processStartId
					? `${liveRival.processStartId}-rival`
					: liveRival.processStartId;
			return { processStartId: rival };
		}
		case "socketPath":
			return { socketPath: `${own.socketPath}.rival` };
	}
}

type Observed = "recoverable" | "fatal";

interface CaseResult {
	facts: Facts;
	key: string;
	oracle: Verdict;
	reachability: Reachability;
	observed: Observed;
	error?: { name: string; code: unknown };
}

interface OwnSideShape {
	pidLiveness: PidLiveness;
	startIdAgreement: StartIdAgreement;
}

/**
 * COST EQUIVALENCE ARGUMENT (why we do not acquire once per case).
 *
 * The complete observable input to assertCurrent() is the triple
 *   (this.released, this.record, the bytes at <ownerDirectory>/owner.json)
 * because the method re-reads the file on every call (:137) while `this.record`
 * is fixed at acquire time and `released` is only set by release(). Across the
 * 32 field-mismatch subsets and the 4 record states, ONLY the third component
 * varies. Rewriting owner.json between calls is therefore observationally
 * identical to re-acquiring, and it costs ~0.1ms instead of ~412ms
 * (acquireDaemonSupervisorOwnership calls getProcessStartId, which shells out
 * to `ps` on macOS).
 *
 * What genuinely varies our own side is (pidLiveness, startIdAgreement), so we
 * acquire once per distinct own-side shape - 6 per pass - and reuse that real
 * ownership object, restoring owner.json between cases. This is a provable
 * equivalence, not a coverage reduction: every one of the 210 fact-shapes is
 * still constructed on disk and still runs the real assertCurrent.
 */
const OWN_SIDE_SHAPES: OwnSideShape[] = (["alive", "dead"] as PidLiveness[]).flatMap((pidLiveness) =>
	(["matches", "mismatches", "absent-in-record"] as StartIdAgreement[]).map((startIdAgreement) => ({
		pidLiveness,
		startIdAgreement,
	})),
);

function ownSideKey(shape: OwnSideShape): string {
	return `${shape.pidLiveness}/${shape.startIdAgreement}`;
}

interface OwnSideFixture {
	root: string;
	previousEnv: string | undefined;
	ownership: Awaited<ReturnType<typeof acquireDaemonSupervisorOwnership>>;
	ownerRecordPath: string;
	/** owner.json exactly as it looks for an intact record of this own-side shape. */
	baseline: OwnerRecordOnDisk;
}

let acquiresPerformed = 0;

async function createOwnSideFixture(shape: OwnSideShape, index: number): Promise<OwnSideFixture> {
	const root = mkdtempSync(join(tmpdir(), "prime-agent-1291-table-"));
	const previousEnv = process.env[REGISTRY_DIR_ENV];
	const registryDir = resolve(root, "supervisor-owners");
	const descriptorDir = resolve(root, "descriptors");
	const agentDir = resolve(root, "agent");
	mkdirSync(registryDir, { recursive: true, mode: 0o700 });
	mkdirSync(descriptorDir, { recursive: true, mode: 0o700 });
	mkdirSync(agentDir, { recursive: true, mode: 0o700 });
	process.env[REGISTRY_DIR_ENV] = registryDir;
	const generation = `gen-table-${index}`;
	const ownership = await acquireDaemonSupervisorOwnership({
		socketPath: resolve(root, "daemon.sock"),
		descriptorDir,
		agentDir,
		generation,
		appVersion: "test",
		registryDir,
	});
	acquiresPerformed++;

	// Realise the claimed identity in the live in-memory record. This is the very
	// object assertCurrent compares against - no stub, no mock.
	const identity = ownIdentityFor({ ...shape, recordState: "present", fieldMismatch: [] });
	ownership.record.pid = identity.pid;
	ownership.record.processStartId = identity.processStartId;

	const ownerRecordPath = resolve(registryDir, `${generation}.owner`, "owner.json");
	const baseline = JSON.parse(readFileSync(ownerRecordPath, "utf8")) as OwnerRecordOnDisk;
	baseline.pid = identity.pid;
	baseline.processStartId = identity.processStartId;
	return { root, previousEnv, ownership, ownerRecordPath, baseline };
}

function disposeOwnSideFixture(fixture: OwnSideFixture): void {
	if (fixture.previousEnv === undefined) {
		delete process.env[REGISTRY_DIR_ENV];
	} else {
		process.env[REGISTRY_DIR_ENV] = fixture.previousEnv;
	}
	rmSync(fixture.root, { recursive: true, force: true });
}

function writeFileSideState(fixture: OwnSideFixture, facts: Facts): void {
	switch (facts.recordState) {
		case "present": {
			let mutated = fixture.baseline;
			for (const field of facts.fieldMismatch) {
				mutated = { ...mutated, ...perturbedValue(field, mutated) };
			}
			writeFileSync(fixture.ownerRecordPath, JSON.stringify(mutated), { mode: 0o600 });
			break;
		}
		case "absent":
			// Exactly what the macOS periodic $TMPDIR reaper does: prune the file,
			// leave the directory standing, never signal the owning process.
			rmSync(fixture.ownerRecordPath, { force: true });
			break;
		case "unparseable":
			// A truncated or torn write: JSON.parse throws inside readOwnerRecord.
			writeFileSync(fixture.ownerRecordPath, '{"version":1,"role":"super', { mode: 0o600 });
			break;
		case "wrong-shape":
			// Valid JSON that fails isDaemonSupervisorOwnerRecord (role is not
			// "supervisor"): the third distinct cause of the same `undefined`.
			writeFileSync(fixture.ownerRecordPath, JSON.stringify({ ...fixture.baseline, role: "worker" }), {
				mode: 0o600,
			});
			break;
	}
}

async function runFileSideCase(fixture: OwnSideFixture, facts: Facts): Promise<CaseResult> {
	writeFileSideState(fixture, facts);
	try {
		await fixture.ownership.assertCurrent();
		return {
			facts,
			key: factKey(facts),
			oracle: decide(facts),
			reachability: reachability(facts),
			observed: "recoverable",
		};
	} catch (error) {
		return {
			facts,
			key: factKey(facts),
			oracle: decide(facts),
			reachability: reachability(facts),
			observed: "fatal",
			error: {
				name: error instanceof Error ? error.name : typeof error,
				code: (error as { code?: unknown }).code,
			},
		};
	} finally {
		// Restore the intact record so the next case starts from a known state.
		writeFileSync(fixture.ownerRecordPath, JSON.stringify(fixture.baseline), { mode: 0o600 });
	}
}

async function runPass(pass: number): Promise<CaseResult[]> {
	const results = new Map<string, CaseResult>();
	for (const [shapeIndex, shape] of OWN_SIDE_SHAPES.entries()) {
		const fixture = await createOwnSideFixture(shape, pass * OWN_SIDE_SHAPES.length + shapeIndex);
		try {
			for (const facts of ENUMERATION) {
				if (ownSideKey(facts) !== ownSideKey(shape)) {
					continue;
				}
				results.set(factKey(facts), await runFileSideCase(fixture, facts));
			}
		} finally {
			disposeOwnSideFixture(fixture);
		}
	}
	return ENUMERATION.map((facts) => {
		const result = results.get(factKey(facts));
		if (!result) {
			throw new Error(`fact-shape was never executed: ${factKey(facts)}`);
		}
		return result;
	});
}

// ---------------------------------------------------------------------------
// 4. THE RUN
// ---------------------------------------------------------------------------

const ENUMERATION = enumerateFacts();
/** Two independent constructions per fact-shape, to prove the outcome is a function of the facts. */
const REPEATS = 2;

let firstPass: CaseResult[] = [];
let secondPass: CaseResult[] = [];
let elapsedMs = 0;

beforeAll(async () => {
	previousRegistryDirEnv = process.env[REGISTRY_DIR_ENV];
	const observedOwnStartId = getProcessStartId(process.pid);
	if (observedOwnStartId === undefined) {
		throw new Error("cannot observe this process's own start id; the start-id axes would be vacuous");
	}
	ownStartId = observedOwnStartId;
	// Pairwise-distinct start ids; see spawnLiveIdentity.
	const taken = new Set<string>([ownStartId, OWN_WRONG_START_ID, RIVAL_WRONG_START_ID]);
	liveRival = (await spawnLiveIdentity(taken)).identity;
	taken.add(liveRival.processStartId);
	deadOwn = await createDeadIdentity(taken);
	taken.add(deadOwn.processStartId);
	deadRival = await createDeadIdentity(taken);

	const started = Date.now();
	const passes: CaseResult[][] = [];
	for (let pass = 0; pass < REPEATS; pass++) {
		passes.push(await runPass(pass));
	}
	elapsedMs = Date.now() - started;
	firstPass = passes[0] ?? [];
	secondPass = passes[1] ?? [];
}, 600_000);

// Runs even when beforeAll throws, which is why every child is tracked at spawn
// time rather than reaped by whoever created it.
afterAll(() => {
	for (const child of spawnedChildren) {
		// Only pids this file spawned, held as ChildProcess handles: no pkill, no
		// kill by name, no pid this file did not create.
		child.kill("SIGKILL");
	}
	if (previousRegistryDirEnv === undefined) {
		delete process.env[REGISTRY_DIR_ENV];
	} else {
		process.env[REGISTRY_DIR_ENV] = previousRegistryDirEnv;
	}
});

describe("daemon supervisor ownership decision table (#1291, #1148)", () => {
	it("VACUITY GUARD: the fixtures really are what the axes claim", () => {
		expect(pidIsAlive(liveRival.pid)).toBe(true);
		expect(liveRival.pid).not.toBe(process.pid);
		expect(getProcessStartId(liveRival.pid)).toBe(liveRival.processStartId);
		// Both dead identities are proved dead by a pid + process-start probe.
		for (const dead of [deadOwn, deadRival]) {
			expect(pidIsAlive(dead.pid)).toBe(false);
			expect(getProcessStartId(dead.pid)).toBeUndefined();
			expect(dead.pid).not.toBe(process.pid);
			expect(dead.pid).not.toBe(liveRival.pid);
		}
		expect(deadOwn.pid).not.toBe(deadRival.pid);
		const startIds = [ownStartId, liveRival.processStartId, deadOwn.processStartId, deadRival.processStartId];
		expect(new Set(startIds).size).toBe(startIds.length);
		expect(startIds).not.toContain(OWN_WRONG_START_ID);
		expect(startIds).not.toContain(RIVAL_WRONG_START_ID);
		// 32 subsets for the present record, plus one representative each for the
		// three states in which no record exists to compare fields against.
		expect(ENUMERATION.length).toBe((32 + 3) * 2 * 3);
		expect(new Set(ENUMERATION.map(factKey)).size).toBe(ENUMERATION.length);
		expect(firstPass).toHaveLength(ENUMERATION.length);
		// One real acquire per distinct own-side shape per pass; see the cost
		// equivalence argument above.
		expect(acquiresPerformed).toBe(OWN_SIDE_SHAPES.length * REPEATS);
		// Reachability partitions the space: 2 own-side shapes a real supervisor
		// can have x (1 intact record + 3 record-destruction causes) = 8 reachable;
		// those same 2 shapes x 31 non-empty mismatch subsets = 62 unreachable at a
		// generation-scoped path; the remaining 4 own-side shapes x 35 = 140 are
		// unreachable because acquire mints the identity from process.pid.
		const byReach = new Map<Reachability, number>();
		for (const facts of ENUMERATION) {
			byReach.set(reachability(facts), (byReach.get(reachability(facts)) ?? 0) + 1);
		}
		expect(byReach.get("reachable")).toBe(8);
		expect(byReach.get("unreachable-generation-scoped-path")).toBe(62);
		expect(byReach.get("unreachable-own-identity-minted")).toBe(140);
	});

	it("CONFLATION REPORT: the implementation maps oracle-distinct facts onto the same outcome", () => {
		// (a) The implementation must be a FUNCTION of the facts: two independent
		// constructions of the same fact-shape must give the same outcome.
		const nondeterministic = firstPass
			.map((first, index) => ({ first, second: secondPass[index] }))
			.filter(({ first, second }) => second === undefined || first.observed !== second.observed)
			.map(({ first }) => first.key);
		expect(nondeterministic).toEqual([]);

		// (b) Pairs the oracle separates but the implementation cannot.
		const conflatedPairs: Array<[string, string]> = [];
		for (let i = 0; i < firstPass.length; i++) {
			for (let j = i + 1; j < firstPass.length; j++) {
				const left = firstPass[i];
				const right = firstPass[j];
				if (!left || !right) continue;
				if (left.oracle === right.oracle) continue;
				if (left.observed !== right.observed) continue;
				conflatedPairs.push([left.key, right.key]);
			}
		}
		expect(conflatedPairs.length).toBeGreaterThan(0);

		// (c) Compact, deterministically ordered artifact for issue #1291. Every
		// line is derived in ENUMERATION order, so the text is byte-stable.
		const divergent = firstPass.filter((result) => result.oracle !== result.observed);
		const reachOrder: Reachability[] = [
			"reachable",
			"unreachable-own-identity-minted",
			"unreachable-generation-scoped-path",
		];
		const divergentBy = (reach: Reachability): CaseResult[] =>
			divergent.filter((result) => result.reachability === reach);
		const line = (result: CaseResult): string =>
			`  oracle=${result.oracle} observed=${result.observed}  ${result.key}${result.error ? `  [${result.error.name}/${String(result.error.code)}]` : ""}`;
		const lines = [
			`cases=${firstPass.length} (${REPEATS} independent constructions each) conflated-pairs=${conflatedPairs.length}`,
			`reachability: ${reachOrder
				.map((reach) => `${reach}=${firstPass.filter((result) => result.reachability === reach).length}`)
				.join(" ")}`,
			`divergent-cases=${divergent.length} (${reachOrder.map((reach) => `${reach}=${divergentBy(reach).length}`).join(" ")})`,
			"REACHABLE divergences - the defect this file is evidence for:",
			...divergentBy("reachable").map(line),
			"UNREACHABLE divergences - harness-constructed, NOT evidence of a defect:",
			`  unreachable-own-identity-minted: ${divergentBy("unreachable-own-identity-minted").length} cases; assertCurrent's own record is minted from process.pid (:309, :316), so a dead or start-id-mismatched own identity cannot occur in production.`,
			`  unreachable-generation-scoped-path: ${divergentBy("unreachable-generation-scoped-path").length} cases; generations are per-instance UUIDs and records are written atomically under a token check, so a valid record with different compared fields cannot appear at our own path today. The #1296 registry rebuild would make this class reachable.`,
			"collapsed-causes (all three yield the identical observed outcome under a live owner):",
			...(["absent", "unparseable", "wrong-shape"] as const).map((state) => {
				const sample = firstPass.find(
					(result) =>
						result.facts.recordState === state &&
						result.facts.pidLiveness === "alive" &&
						result.facts.startIdAgreement === "matches",
				);
				return `  ${state} -> observed=${sample?.observed ?? "n/a"} error=${sample?.error?.name ?? "none"}/${String(sample?.error?.code ?? "none")} reachability=${sample ? reachability(sample.facts) : "n/a"}`;
			}),
		];
		console.log(lines.join("\n"));
		expect(divergent.length).toBeGreaterThan(0);
		// The reachable divergences are exactly the three record-destruction
		// causes under each of the two own-side shapes a real supervisor can have.
		expect(divergentBy("reachable")).toHaveLength(6);
		for (const result of divergentBy("reachable")) {
			expect(result.facts.recordState).not.toBe("present");
			expect(result.oracle).toBe("recoverable");
			expect(result.observed).toBe("fatal");
		}
	});

	// EXECUTABLE SPECIFICATION OF THE FIX, scoped to the REACHABLE fact-shapes.
	// Fails on current main because assertCurrent treats a destroyed, truncated
	// or invalid record identically to a lost claim, without consulting the
	// liveness machinery in the same file. Flips to green exactly when the class
	// is fixed. Never delete this test.
	//
	// Deliberately not asserted over the unreachable shapes: demanding a verdict
	// there would demand code for states acquireDaemonSupervisorOwnership cannot
	// produce (own identity is minted from process.pid at :309/:316) and states
	// no in-repo writer can create at our generation-scoped path.
	it.fails("SPEC: assertCurrent must agree with the oracle for every REACHABLE fact-shape", () => {
		const reachable = firstPass.filter((result) => result.reachability === "reachable");
		expect(reachable.length).toBeGreaterThan(0);
		const first = reachable.find((result) => result.oracle !== result.observed);
		expect(
			first === undefined
				? ""
				: `first reachable divergence: expected ${first.oracle}, observed ${first.observed} for ${first.key}`,
		).toBe("");
		for (const result of reachable) {
			expect(`${result.key} -> ${result.observed}`).toBe(`${result.key} -> ${result.oracle}`);
		}
	});

	it("the unreachable divergences stay enumerated and stay labelled", () => {
		// Kept executable so the reclassification cannot rot: if acquire ever
		// stops minting its own identity, or a generation stops being unique per
		// instance, these counts move and this test says so.
		const divergent = firstPass.filter((result) => result.oracle !== result.observed);
		expect(divergent.filter((result) => result.reachability === "unreachable-own-identity-minted")).toHaveLength(4);
		expect(divergent.filter((result) => result.reachability === "unreachable-generation-scoped-path")).toHaveLength(
			0,
		);
		// Every unreachable-own-identity case is one this harness manufactured by
		// assigning ownership.record.pid / processStartId after acquire.
		for (const result of firstPass.filter((result) => result.reachability === "unreachable-own-identity-minted")) {
			expect(result.facts.pidLiveness === "dead" || result.facts.startIdAgreement === "mismatches").toBe(true);
		}
	});

	it("REPORT: enumeration size and runtime", () => {
		console.log(
			`enumerated fact-shapes=${ENUMERATION.length}; constructions=${ENUMERATION.length * REPEATS}; real acquires=${acquiresPerformed}; construction+assert runtime=${elapsedMs}ms`,
		);
		expect(elapsedMs).toBeGreaterThan(0);
	});
});

// ---------------------------------------------------------------------------
// 5. SECOND TABLE: assertDaemonSupervisorOwnerCurrent (:365-390)
// ---------------------------------------------------------------------------
//
// The table above cannot say anything about RIVAL liveness, because
// assertCurrent's own record is minted from process.pid and its path is scoped
// to a generation UUID nobody else writes. The exported
// assertDaemonSupervisorOwnerCurrent is the function where rival liveness is
// NOT vacuous: it takes an owner DESCRIPTOR supplied by the caller -
// daemon-mode.ts:719-732 passes a SupervisorGenerationClaim held in memory and
// re-checked on a fence timer - so pid/processStartId legitimately belong to
// another process, and that process can die or have its pid recycled between
// checks.
//
//     const current = readOwnerRecord(ownerDirectoryPath(registryDir, owner.generation));
//     if (!current || current.pid !== owner.pid || current.processStartId !== owner.processStartId ||
//         current.socketPath !== normalizeSocketPath(owner.socketPath) || !isProcessAlive(current.pid)) throw LOST;
//     const fingerprint = ownerRecordFingerprint(current);
//     if (fingerprint !== validatedFingerprint && !isProcessIdentityAlive(current)) throw LOST;
//     return fingerprint;
//
// It already consults liveness, and it still collapses `!current` (record
// destroyed, truncated, or invalid) into the same throw as a genuine mismatch.
// It also lets a previously validated fingerprint skip the identity check
// entirely, so a recycled pid can be reported as the current owner.

const FENCE_FIELDS = ["pid", "processStartId", "socketPath"] as const;
type FenceField = (typeof FENCE_FIELDS)[number];

/** Liveness of the identity the ON-DISK record names - the fifth axis, made real. */
type RivalLiveness = "alive" | "dead-pid" | "startid-mismatch" | "no-rival";
/** Liveness of the identity the CALLER supplied in the owner descriptor. */
type DescriptorLiveness = "alive" | "dead-pid" | "startid-mismatch";
/** The two physical components of the record identity, enumerated independently. */
type RecordPid = "alive" | "dead";
type RecordStartId = "real" | "wrong" | "absent";
/** The validatedFingerprint argument, which gates the isProcessIdentityAlive check. */
type FingerprintArgument = "matches-current" | "stale" | "not-supplied";

interface FenceFacts {
	readonly recordState: RecordState;
	/** Always empty unless recordState === "present". */
	readonly fieldMismatch: readonly FenceField[];
	/** Representative values only when no record exists; see enumerateFenceFacts. */
	readonly recordPid: RecordPid;
	readonly recordStartId: RecordStartId;
	readonly descriptorLiveness: DescriptorLiveness;
	readonly fingerprint: FingerprintArgument;
}

/** "current" is a success outcome: the descriptor still names the live owner. */
type FenceVerdict = "current" | "recoverable" | "recoverable-by-takeover" | "fatal";
type FenceObserved = "current" | "fatal";

/**
 * The rival liveness the record instantiates, judged the way
 * isProcessIdentityAlive (:521-530) judges it: dead pid, or live pid whose
 * observed start id contradicts the recorded one, or alive.
 */
function rivalLivenessOf(facts: FenceFacts): RivalLiveness {
	if (facts.recordState !== "present") {
		return "no-rival";
	}
	if (facts.recordPid === "dead") {
		return "dead-pid";
	}
	return facts.recordStartId === "wrong" ? "startid-mismatch" : "alive";
}

function fenceKey(facts: FenceFacts): string {
	const mismatch = facts.fieldMismatch.length === 0 ? "none" : facts.fieldMismatch.join("+");
	const record = facts.recordState === "present" ? `${facts.recordPid}/${facts.recordStartId}` : "n/a";
	return `record=${facts.recordState} mismatch=${mismatch} rival=${rivalLivenessOf(facts)} recordIdentity=${record} descriptor=${facts.descriptorLiveness} fingerprint=${facts.fingerprint}`;
}

/**
 * Which descriptor livenesses are constructible for a given (mismatch, record
 * identity) point. The descriptor identity is (owner.pid, owner.processStartId)
 * and the function requires it to equal the record's on both fields unless we
 * are deliberately perturbing them, so the mismatch subset decides how much of
 * the descriptor identity we are free to choose. Each branch is an equivalence
 * argument, not sampling.
 */
function constructibleDescriptorLivenesses(
	recordState: RecordState,
	fieldMismatch: readonly FenceField[],
	recordPid: RecordPid,
	recordStartId: RecordStartId,
): DescriptorLiveness[] {
	if (recordState !== "present") {
		// No record to agree or disagree with: the descriptor identity is entirely
		// ours to choose, and all three states matter to the oracle.
		return ["alive", "dead-pid", "startid-mismatch"];
	}
	const perturbsPid = fieldMismatch.includes("pid");
	const perturbsStartId = fieldMismatch.includes("processStartId");
	if (perturbsPid && perturbsStartId) {
		return ["alive", "dead-pid", "startid-mismatch"];
	}
	if (perturbsPid) {
		// The descriptor must carry the RECORD's start id on a different pid. A
		// start id belonging to one process is never the real start id of another,
		// so a live descriptor pid is necessarily start-id mismatched - unless the
		// record carries no start id, in which case there is nothing to contradict
		// and "startid-mismatch" is the unconstructible one instead.
		return recordStartId === "absent" ? ["alive", "dead-pid"] : ["dead-pid", "startid-mismatch"];
	}
	if (perturbsStartId) {
		// Same pid as the record, different start id.
		if (recordPid === "dead") {
			return ["dead-pid"];
		}
		// A live pid: the descriptor can carry that pid's REAL start id (alive) or
		// another wrong one, except when the record already carries the real one -
		// then "different from the record" forces a wrong value.
		return recordStartId === "real" ? ["startid-mismatch"] : ["alive", "startid-mismatch"];
	}
	// Identity fields equal: the descriptor IS the record identity.
	const rival = rivalLivenessOf({
		recordState,
		fieldMismatch,
		recordPid,
		recordStartId,
		descriptorLiveness: "alive",
		fingerprint: "not-supplied",
	});
	return rival === "no-rival" ? ["alive"] : [rival];
}

/**
 * Full cross-product, deterministically ordered, with two documented collapses.
 *
 * 1. fieldMismatch and the record identity axes are properties of a record that
 *    exists. For absent/unparseable/wrong-shape, readOwnerRecord returns
 *    undefined before any comparison happens, so all subsets and all record
 *    identities are one physical state: one representative each.
 * 2. descriptorLiveness is collapsed wherever the mismatch subset forces it;
 *    see constructibleDescriptorLivenesses.
 *
 * The fingerprint argument is caller-supplied and therefore free everywhere,
 * including the record-less states, so it is enumerated in full.
 */
function enumerateFenceFacts(): FenceFacts[] {
	const recordStates: RecordState[] = ["present", "absent", "unparseable", "wrong-shape"];
	const fingerprints: FingerprintArgument[] = ["matches-current", "stale", "not-supplied"];
	const subsets: FenceField[][] = [];
	for (let mask = 0; mask < 1 << FENCE_FIELDS.length; mask++) {
		subsets.push(FENCE_FIELDS.filter((_, index) => (mask & (1 << index)) !== 0));
	}
	const facts: FenceFacts[] = [];
	for (const recordState of recordStates) {
		const mismatches = recordState === "present" ? subsets : [[]];
		const recordPids: RecordPid[] = recordState === "present" ? ["alive", "dead"] : ["alive"];
		const recordStartIds: RecordStartId[] = recordState === "present" ? ["real", "wrong", "absent"] : ["real"];
		for (const fieldMismatch of mismatches) {
			for (const recordPid of recordPids) {
				for (const recordStartId of recordStartIds) {
					for (const descriptorLiveness of constructibleDescriptorLivenesses(
						recordState,
						fieldMismatch,
						recordPid,
						recordStartId,
					)) {
						for (const fingerprint of fingerprints) {
							facts.push({
								recordState,
								fieldMismatch,
								recordPid,
								recordStartId,
								descriptorLiveness,
								fingerprint,
							});
						}
					}
				}
			}
		}
	}
	return facts;
}

/**
 * THE ORACLE for assertDaemonSupervisorOwnerCurrent. Total over the fact space.
 *
 * validatedFingerprint is deliberately NOT consulted. It is an input the caller
 * supplies, not a fact about who owns the socket now, and a fingerprint
 * validated at some earlier instant cannot prove the recorded process is still
 * the process at that pid. Where today's implementation lets it skip the
 * identity check, this oracle disagrees on purpose.
 */
function fenceDecide(facts: FenceFacts): FenceVerdict {
	// RULE 4, dominant: the identity supplied from outside is dead or recycled.
	// An untrusted descriptor may neither hold nor seize anything.
	if (facts.descriptorLiveness !== "alive") {
		return "fatal";
	}
	// RULE 1: the record is gone, corrupt, or not an owner record, while the
	// descriptor identity is alive. The entry was destroyed under a live owner -
	// the #1291 shape, one level up. Recoverable: rewrite the entry.
	if (facts.recordState !== "present") {
		return "recoverable";
	}
	// RULE 2: the record is present and agrees with the descriptor on all three
	// compared fields. The descriptor is alive, so the record identity is alive:
	// the ordinary success path, and the only outcome that should return.
	if (facts.fieldMismatch.length === 0) {
		return "current";
	}
	// RULE 3: the record names a genuinely live other identity. Stand down.
	if (rivalLivenessOf(facts) === "alive") {
		return "fatal";
	}
	// RULE 5: the record names an identity that is provably not alive. Nothing
	// owns that entry; the socket is stranded and a live legitimate holder
	// should be able to seize it under the guard rule 4 just enforced.
	return "recoverable-by-takeover";
}

/**
 * REACHABILITY for this table. The descriptor is caller-supplied data about
 * ANOTHER process - a claim held in memory and re-checked on a timer - so a
 * dead or recycled descriptor identity, a dead or recycled record identity, a
 * destroyed record and every fingerprint state are all ordinary production
 * facts. The one class that no in-repo writer produces is the same one as in
 * table 1: a VALID record with DIFFERENT compared fields at a generation-scoped
 * path, which the #1296 registry rebuild would create.
 */
type FenceReachability = "reachable" | "unreachable-generation-scoped-path";

function fenceReachability(facts: FenceFacts): FenceReachability {
	return facts.recordState === "present" && facts.fieldMismatch.length > 0
		? "unreachable-generation-scoped-path"
		: "reachable";
}

interface FenceCaseResult {
	facts: FenceFacts;
	key: string;
	oracle: FenceVerdict;
	reachability: FenceReachability;
	observed: FenceObserved;
	error?: { name: string; code: unknown };
}

interface FenceFixture {
	root: string;
	registryDir: string;
	generation: string;
	ownerRecordPath: string;
	baseline: OwnerRecordOnDisk;
}

/** A fingerprint that is not any record's: used for the "stale" argument. */
const STALE_FINGERPRINT = createHash("sha256").update("not-the-fingerprint-of-any-record").digest("hex");

function recordIdentityFor(facts: FenceFacts): { pid: number; processStartId?: string } {
	const pid = facts.recordPid === "alive" ? liveRival.pid : deadRival.pid;
	switch (facts.recordStartId) {
		case "real":
			// The start id that pid really had. For the dead fixture we captured it
			// while it lived; it is still "the record's own" start id.
			return {
				pid,
				processStartId: facts.recordPid === "alive" ? liveRival.processStartId : deadRival.processStartId,
			};
		case "wrong":
			return { pid, processStartId: RIVAL_WRONG_START_ID };
		case "absent":
			return { pid };
	}
}

function descriptorIdentityFor(
	facts: FenceFacts,
	record: { pid: number; processStartId?: string },
): { pid: number; processStartId?: string } {
	const perturbsPid = facts.fieldMismatch.includes("pid");
	const perturbsStartId = facts.fieldMismatch.includes("processStartId");
	const pid =
		perturbsPid || facts.recordState !== "present"
			? facts.descriptorLiveness === "dead-pid"
				? deadOwn.pid
				: process.pid
			: record.pid;
	if (!perturbsStartId && facts.recordState === "present") {
		return { pid, processStartId: record.processStartId };
	}
	switch (facts.descriptorLiveness) {
		case "alive":
			return { pid, processStartId: realStartIdOf(pid) };
		case "dead-pid":
		case "startid-mismatch":
			return { pid, processStartId: OWN_WRONG_START_ID };
	}
}

/**
 * VACUITY GUARD, per case: the descriptor and the bytes on disk must really
 * instantiate the facts they claim, on both the mismatch subset and the two
 * liveness axes.
 */
function assertFenceCaseIsWhatItClaims(
	facts: FenceFacts,
	record: OwnerRecordOnDisk,
	descriptor: { pid: number; processStartId?: string; socketPath: string },
): void {
	if (facts.recordState === "present") {
		for (const field of FENCE_FIELDS) {
			const differs = record[field] !== descriptor[field];
			if (differs !== facts.fieldMismatch.includes(field)) {
				throw new Error(`constructed case does not match its mismatch subset on ${field}: ${fenceKey(facts)}`);
			}
		}
		const recordAlive = pidIsAlive(record.pid);
		const recordReal = realStartIdOf(record.pid);
		const rival = rivalLivenessOf(facts);
		const rivalHolds =
			rival === "dead-pid"
				? !recordAlive
				: rival === "alive"
					? recordAlive && (record.processStartId === undefined || record.processStartId === recordReal)
					: recordAlive && record.processStartId !== undefined && record.processStartId !== recordReal;
		if (!rivalHolds) {
			throw new Error(`on-disk rival is not ${rival}: ${fenceKey(facts)}`);
		}
	}
	const descriptorAlive = pidIsAlive(descriptor.pid);
	const descriptorReal = realStartIdOf(descriptor.pid);
	const holds =
		facts.descriptorLiveness === "dead-pid"
			? !descriptorAlive
			: facts.descriptorLiveness === "alive"
				? descriptorAlive &&
					(descriptor.processStartId === undefined || descriptor.processStartId === descriptorReal)
				: descriptorAlive &&
					descriptor.processStartId !== undefined &&
					descriptor.processStartId !== descriptorReal;
	if (!holds) {
		throw new Error(`descriptor identity is not ${facts.descriptorLiveness}: ${fenceKey(facts)}`);
	}
}

async function runFenceCase(fixture: FenceFixture, facts: FenceFacts): Promise<FenceCaseResult> {
	// HARD SAFETY: the function under test resolves its registry from the
	// environment, so refuse to run unless the environment points inside this
	// case's own temporary tree.
	const activeRegistry = process.env[REGISTRY_DIR_ENV];
	if (activeRegistry !== fixture.registryDir) {
		throw new Error("refusing to run: the supervisor registry environment does not point at this fixture");
	}
	const identity = recordIdentityFor(facts);
	const record: OwnerRecordOnDisk = {
		...fixture.baseline,
		pid: identity.pid,
		processStartId: identity.processStartId,
	};
	switch (facts.recordState) {
		case "present":
			writeFileSync(fixture.ownerRecordPath, JSON.stringify(record), { mode: 0o600 });
			break;
		case "absent":
			rmSync(fixture.ownerRecordPath, { force: true });
			break;
		case "unparseable":
			writeFileSync(fixture.ownerRecordPath, '{"version":1,"role":"super', { mode: 0o600 });
			break;
		case "wrong-shape":
			writeFileSync(fixture.ownerRecordPath, JSON.stringify({ ...record, role: "worker" }), { mode: 0o600 });
			break;
	}
	const descriptorIdentity = descriptorIdentityFor(facts, identity);
	const descriptor = {
		generation: fixture.generation,
		pid: descriptorIdentity.pid,
		...(descriptorIdentity.processStartId ? { processStartId: descriptorIdentity.processStartId } : {}),
		socketPath: facts.fieldMismatch.includes("socketPath")
			? `${fixture.baseline.socketPath}.descriptor`
			: fixture.baseline.socketPath,
	};
	assertFenceCaseIsWhatItClaims(facts, record, { ...descriptorIdentity, socketPath: descriptor.socketPath });
	// The fingerprint the implementation would compute for exactly these bytes.
	const currentFingerprint =
		facts.recordState === "present"
			? createHash("sha256")
					.update(JSON.stringify(JSON.parse(readFileSync(fixture.ownerRecordPath, "utf8"))))
					.digest("hex")
			: undefined;
	const validatedFingerprint =
		facts.fingerprint === "not-supplied"
			? undefined
			: facts.fingerprint === "stale"
				? STALE_FINGERPRINT
				: (currentFingerprint ?? STALE_FINGERPRINT);
	if (facts.fingerprint === "stale" && currentFingerprint === STALE_FINGERPRINT) {
		throw new Error("the stale fingerprint collided with a real one");
	}
	const common = {
		facts,
		key: fenceKey(facts),
		oracle: fenceDecide(facts),
		reachability: fenceReachability(facts),
	};
	try {
		const returned = await assertDaemonSupervisorOwnerCurrent(descriptor, validatedFingerprint);
		if (currentFingerprint !== undefined && returned !== currentFingerprint) {
			// Proves our fingerprint computation is the implementation's, not a guess.
			throw new Error(`fingerprint mismatch between harness and implementation: ${fenceKey(facts)}`);
		}
		return { ...common, observed: "current" };
	} catch (error) {
		if (!(error instanceof Error) || error.name !== "DaemonSupervisorOwnershipLostError") {
			throw error;
		}
		return {
			...common,
			observed: "fatal",
			error: { name: error.name, code: (error as { code?: unknown }).code },
		};
	}
}

const FENCE_ENUMERATION = enumerateFenceFacts();

let fenceFirstPass: FenceCaseResult[] = [];
let fenceSecondPass: FenceCaseResult[] = [];
let fenceElapsedMs = 0;
let fencePreviousEnv: string | undefined;
let fenceFixture: FenceFixture | undefined;

describe("assertDaemonSupervisorOwnerCurrent rival-liveness decision table (#1291, #1296)", () => {
	beforeAll(async () => {
		fencePreviousEnv = process.env[REGISTRY_DIR_ENV];
		const root = mkdtempSync(join(tmpdir(), "prime-agent-1291-fence-"));
		const registryDir = resolve(root, "supervisor-owners");
		const descriptorDir = resolve(root, "descriptors");
		const agentDir = resolve(root, "agent");
		mkdirSync(registryDir, { recursive: true, mode: 0o700 });
		mkdirSync(descriptorDir, { recursive: true, mode: 0o700 });
		mkdirSync(agentDir, { recursive: true, mode: 0o700 });
		process.env[REGISTRY_DIR_ENV] = registryDir;
		const generation = "gen-fence-0";
		// One real acquire, purely to obtain a genuine owner record to rewrite.
		// The function under test takes its owner from the CALLER, so no ownership
		// object is needed here.
		const ownership = await acquireDaemonSupervisorOwnership({
			socketPath: resolve(root, "daemon.sock"),
			descriptorDir,
			agentDir,
			generation,
			appVersion: "test",
			registryDir,
		});
		acquiresPerformed++;
		const ownerRecordPath = resolve(registryDir, `${generation}.owner`, "owner.json");
		const baseline = JSON.parse(readFileSync(ownerRecordPath, "utf8")) as OwnerRecordOnDisk;
		expect(ownership.record.generation).toBe(generation);
		fenceFixture = { root, registryDir, generation, ownerRecordPath, baseline };

		const started = Date.now();
		const passes: FenceCaseResult[][] = [];
		for (let pass = 0; pass < REPEATS; pass++) {
			const results: FenceCaseResult[] = [];
			for (const facts of FENCE_ENUMERATION) {
				results.push(await runFenceCase(fenceFixture, facts));
			}
			passes.push(results);
		}
		fenceElapsedMs = Date.now() - started;
		fenceFirstPass = passes[0] ?? [];
		fenceSecondPass = passes[1] ?? [];
	}, 600_000);

	afterAll(() => {
		if (fenceFixture) {
			rmSync(fenceFixture.root, { recursive: true, force: true });
		}
		if (fencePreviousEnv === undefined) {
			delete process.env[REGISTRY_DIR_ENV];
		} else {
			process.env[REGISTRY_DIR_ENV] = fencePreviousEnv;
		}
	});

	it("VACUITY GUARD: the enumeration is total and every axis is exercised", () => {
		expect(new Set(FENCE_ENUMERATION.map(fenceKey)).size).toBe(FENCE_ENUMERATION.length);
		expect(fenceFirstPass).toHaveLength(FENCE_ENUMERATION.length);
		expect(fenceSecondPass).toHaveLength(FENCE_ENUMERATION.length);
		const rivalCounts = new Map<RivalLiveness, number>();
		for (const facts of FENCE_ENUMERATION) {
			const rival = rivalLivenessOf(facts);
			rivalCounts.set(rival, (rivalCounts.get(rival) ?? 0) + 1);
		}
		// All three rival states, and the record-less representative, are present.
		for (const rival of ["alive", "dead-pid", "startid-mismatch", "no-rival"] as const) {
			expect(rivalCounts.get(rival) ?? 0).toBeGreaterThan(0);
		}
		// The dead rival really is dead and the start-id-mismatched rival really
		// is a live pid carrying a start id that is not its own.
		expect(pidIsAlive(deadRival.pid)).toBe(false);
		expect(getProcessStartId(deadRival.pid)).toBeUndefined();
		expect(pidIsAlive(liveRival.pid)).toBe(true);
		expect(getProcessStartId(liveRival.pid)).toBe(liveRival.processStartId);
		expect(RIVAL_WRONG_START_ID).not.toBe(liveRival.processStartId);
	});

	it("CONFLATION REPORT: rival liveness is observable here, and still not observed", () => {
		const nondeterministic = fenceFirstPass
			.map((first, index) => ({ first, second: fenceSecondPass[index] }))
			.filter(({ first, second }) => second === undefined || first.observed !== second.observed)
			.map(({ first }) => first.key);
		expect(nondeterministic).toEqual([]);

		const oracleOrder: FenceVerdict[] = ["current", "recoverable", "recoverable-by-takeover", "fatal"];
		const observedOrder: FenceObserved[] = ["current", "fatal"];
		const divergent = fenceFirstPass.filter((result) => (result.oracle as string) !== (result.observed as string));
		const reachableDivergent = divergent.filter((result) => result.reachability === "reachable");
		const unreachableDivergent = divergent.filter((result) => result.reachability !== "reachable");
		const groupCount = (results: FenceCaseResult[], oracle: FenceVerdict, observed: FenceObserved): number =>
			results.filter((result) => result.oracle === oracle && result.observed === observed).length;
		const lines = [
			`cases=${fenceFirstPass.length} (${REPEATS} independent constructions each)`,
			`oracle-outcomes: ${oracleOrder
				.map((verdict) => `${verdict}=${fenceFirstPass.filter((result) => result.oracle === verdict).length}`)
				.join(" ")}`,
			`observed-outcomes: ${observedOrder
				.map((observed) => `${observed}=${fenceFirstPass.filter((result) => result.observed === observed).length}`)
				.join(
					" ",
				)} (the function has two outcomes, so recoverable and recoverable-by-takeover are unobservable by construction)`,
			`divergent-cases=${divergent.length} (reachable=${reachableDivergent.length} unreachable-generation-scoped-path=${unreachableDivergent.length})`,
			"REACHABLE divergences by outcome pair:",
			...oracleOrder.flatMap((oracle) =>
				observedOrder
					.map((observed) => ({ oracle, observed, count: groupCount(reachableDivergent, oracle, observed) }))
					.filter((group) => group.count > 0)
					.map((group) => `  oracle=${group.oracle} observed=${group.observed}: ${group.count}`),
			),
			"UNREACHABLE divergences by outcome pair (a valid record with different compared fields at a generation-scoped path; the #1296 rebuild creates exactly this):",
			...oracleOrder.flatMap((oracle) =>
				observedOrder
					.map((observed) => ({ oracle, observed, count: groupCount(unreachableDivergent, oracle, observed) }))
					.filter((group) => group.count > 0)
					.map((group) => `  oracle=${group.oracle} observed=${group.observed}: ${group.count}`),
			),
			"rival-liveness slice (record present, at least one compared field differs, descriptor alive):",
			...(["alive", "dead-pid", "startid-mismatch"] as const).map((rival) => {
				const slice = fenceFirstPass.filter(
					(result) =>
						result.facts.recordState === "present" &&
						result.facts.fieldMismatch.length > 0 &&
						result.facts.descriptorLiveness === "alive" &&
						rivalLivenessOf(result.facts) === rival,
				);
				return `  rival=${rival} cases=${slice.length} oracle={${[...new Set(slice.map((result) => result.oracle))].sort().join(",")}} observed={${[...new Set(slice.map((result) => result.observed))].sort().join(",")}}`;
			}),
			"record-destruction collapse (descriptor alive, record present-and-equal vs destroyed):",
			...(["present", "absent", "unparseable", "wrong-shape"] as const).map((state) => {
				const sample = fenceFirstPass.find(
					(result) =>
						result.facts.recordState === state &&
						result.facts.fieldMismatch.length === 0 &&
						result.facts.descriptorLiveness === "alive" &&
						result.facts.fingerprint === "not-supplied" &&
						result.facts.recordPid === "alive" &&
						result.facts.recordStartId === "real",
				);
				return `  ${state} -> oracle=${sample?.oracle ?? "n/a"} observed=${sample?.observed ?? "n/a"} error=${sample?.error?.name ?? "none"}/${String(sample?.error?.code ?? "none")}`;
			}),
			"fingerprint bypass (record present and equal, rival pid recycled so its start id no longer matches):",
			...(["matches-current", "stale", "not-supplied"] as const).map((fingerprint) => {
				const sample = fenceFirstPass.find(
					(result) =>
						result.facts.recordState === "present" &&
						result.facts.fieldMismatch.length === 0 &&
						result.facts.recordPid === "alive" &&
						result.facts.recordStartId === "wrong" &&
						result.facts.fingerprint === fingerprint,
				);
				return `  fingerprint=${fingerprint} -> oracle=${sample?.oracle ?? "n/a"} observed=${sample?.observed ?? "n/a"}`;
			}),
		];
		console.log(lines.join("\n"));
		expect(divergent.length).toBeGreaterThan(0);
	});

	// EXECUTABLE SPECIFICATION for the reachable half of this table.
	it.fails("SPEC: assertDaemonSupervisorOwnerCurrent must agree with the oracle for every REACHABLE fact-shape", () => {
		const reachable = fenceFirstPass.filter((result) => result.reachability === "reachable");
		expect(reachable.length).toBeGreaterThan(0);
		const first = reachable.find((result) => (result.oracle as string) !== (result.observed as string));
		expect(
			first === undefined
				? ""
				: `first reachable divergence: expected ${first.oracle}, observed ${first.observed} for ${first.key}`,
		).toBe("");
		for (const result of reachable) {
			expect(`${result.key} -> ${result.observed}`).toBe(`${result.key} -> ${result.oracle}`);
		}
	});

	it("REPORT: enumeration size and runtime", () => {
		console.log(
			`fence fact-shapes=${FENCE_ENUMERATION.length}; constructions=${FENCE_ENUMERATION.length * REPEATS}; construction+assert runtime=${fenceElapsedMs}ms`,
		);
		expect(fenceElapsedMs).toBeGreaterThan(0);
	});
});
