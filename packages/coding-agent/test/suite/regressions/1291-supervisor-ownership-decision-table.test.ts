import { type ChildProcess, spawn } from "node:child_process";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { getProcessStartId } from "../../../src/core/session-lease.js";
import { acquireDaemonSupervisorOwnership } from "../../../src/modes/daemon/daemon-supervisor-ownership.js";

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

interface RivalIdentity {
	pid: number;
	processStartId: string;
}

interface DeadIdentity {
	pid: number;
	/** The start id the process really had, captured before we killed it. */
	processStartId: string;
}

let liveRival: RivalIdentity;
let deadOwn: DeadIdentity;
let ownStartId: string;
let liveChild: ChildProcess | undefined;
let previousRegistryDirEnv: string | undefined;

function spawnIdleChild(): ChildProcess {
	// A child WE own. Nothing else in this file signals any pid.
	return spawn(process.execPath, ["-e", "setTimeout(() => {}, 600000)"], { stdio: "ignore" });
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
 * A pid we can prove is dead: we spawn it, capture the start id it really had
 * while it lived (on macOS that value is unobservable once it exits), and kill
 * it. We only ever signal a pid this file created.
 */
async function createDeadIdentity(): Promise<DeadIdentity> {
	const child = spawnIdleChild();
	const pid = child.pid;
	if (pid === undefined) {
		throw new Error("failed to spawn the child process used for the dead-pid cases");
	}
	const processStartId = getProcessStartId(pid) ?? `ps:dead-${pid}`;
	await new Promise<void>((resolveExit) => {
		child.once("exit", () => resolveExit());
		// We only ever kill a pid we just created ourselves.
		child.kill("SIGKILL");
	});
	return { pid, processStartId };
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
			return { pid, processStartId: "ps:deliberately-not-the-real-start-id" };
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
		return { facts, key: factKey(facts), oracle: decide(facts), observed: "recoverable" };
	} catch (error) {
		return {
			facts,
			key: factKey(facts),
			oracle: decide(facts),
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
	ownStartId = getProcessStartId(process.pid) ?? "ps:self";
	liveChild = spawnIdleChild();
	if (liveChild.pid === undefined) {
		throw new Error("failed to spawn the live rival child process");
	}
	liveRival = { pid: liveChild.pid, processStartId: getProcessStartId(liveChild.pid) ?? `ps:rival-${liveChild.pid}` };
	deadOwn = await createDeadIdentity();

	const started = Date.now();
	const passes: CaseResult[][] = [];
	for (let pass = 0; pass < REPEATS; pass++) {
		passes.push(await runPass(pass));
	}
	elapsedMs = Date.now() - started;
	firstPass = passes[0] ?? [];
	secondPass = passes[1] ?? [];
}, 600_000);

afterAll(() => {
	liveChild?.kill("SIGKILL");
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
		expect(pidIsAlive(deadOwn.pid)).toBe(false);
		expect(deadOwn.pid).not.toBe(process.pid);
		// 32 subsets for the present record, plus one representative each for the
		// three states in which no record exists to compare fields against.
		expect(ENUMERATION.length).toBe((32 + 3) * 2 * 3);
		expect(new Set(ENUMERATION.map(factKey)).size).toBe(ENUMERATION.length);
		expect(firstPass).toHaveLength(ENUMERATION.length);
		// One real acquire per distinct own-side shape per pass; see the cost
		// equivalence argument above.
		expect(acquiresPerformed).toBe(OWN_SIDE_SHAPES.length * REPEATS);
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

		// (c) Compact, deterministically ordered artifact for issue #1291.
		const divergent = firstPass.filter((result) => result.oracle !== result.observed);
		const lines = [
			`cases=${firstPass.length} (${REPEATS} independent constructions each) conflated-pairs=${conflatedPairs.length}`,
			`divergent-cases=${divergent.length}`,
			...divergent.map(
				(result) =>
					`  oracle=${result.oracle} observed=${result.observed}  ${result.key}${result.error ? `  [${result.error.name}/${String(result.error.code)}]` : ""}`,
			),
			"collapsed-causes (all three yield the identical observed outcome under a live owner):",
			...(["absent", "unparseable", "wrong-shape"] as const).map((state) => {
				const sample = firstPass.find(
					(result) =>
						result.facts.recordState === state &&
						result.facts.pidLiveness === "alive" &&
						result.facts.startIdAgreement === "matches",
				);
				return `  ${state} -> observed=${sample?.observed ?? "n/a"} error=${sample?.error?.name ?? "none"}/${String(sample?.error?.code ?? "none")}`;
			}),
		];
		console.log(lines.join("\n"));
		expect(divergent.length).toBeGreaterThan(0);
	});

	// EXECUTABLE SPECIFICATION OF THE FIX. Fails on current main because
	// assertCurrent consults neither readOwnerRecord's cause nor the liveness of
	// the identity it claims. Flips to green exactly when the class is fixed.
	// Never delete this test.
	it.fails("SPEC: assertCurrent must agree with the oracle for every enumerated fact-shape", () => {
		const first = firstPass.find((result) => result.oracle !== result.observed);
		expect(
			first === undefined
				? ""
				: `first divergence: expected ${first.oracle}, observed ${first.observed} for ${first.key}`,
		).toBe("");
		for (const result of firstPass) {
			expect(`${result.key} -> ${result.observed}`).toBe(`${result.key} -> ${result.oracle}`);
		}
	});

	it("REPORT: enumeration size and runtime", () => {
		console.log(
			`enumerated fact-shapes=${ENUMERATION.length}; constructions=${ENUMERATION.length * REPEATS}; real acquires=${acquiresPerformed}; construction+assert runtime=${elapsedMs}ms`,
		);
		expect(elapsedMs).toBeGreaterThan(0);
	});
});
