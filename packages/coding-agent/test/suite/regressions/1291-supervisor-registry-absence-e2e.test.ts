import { type ChildProcess, spawn } from "node:child_process";
import { existsSync, readdirSync, readFileSync, statSync, unlinkSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { ENV_AGENT_DIR } from "../../../src/config.js";
import { getProcessStartId } from "../../../src/core/session-lease.js";
import { DaemonAgentConnection } from "../../../src/modes/agent-connection/daemon-agent-connection.js";
import { DaemonClient } from "../../../src/modes/daemon/daemon-client.js";
import type { DaemonUpdateRestartManifest } from "../../../src/modes/daemon/daemon-protocol.js";
import type { SessionSummary } from "../../../src/modes/daemon/daemon-session-list.js";
import { createHarness, type Harness } from "../harness.js";

// End-to-end companion to 1291-supervisor-registry-absence.test.ts.
//
// That file proves the ownership conflation in
// daemon-supervisor-ownership.ts assertCurrent():
//     if (!current || !sameOwnerRecord(current, this.record)) throw ...
// against a real on-disk registry, but through a constructor-bypass supervisor
// with an EMPTY worker set. It therefore proves "the handoff is rejected", not
// "a live session tree is lost".
//
// This file closes that gap. Every test here boots a REAL DaemonSupervisor in a
// forked child (test/fixtures/eng-4600-supervisor-fixture.ts, supervisor mode),
// creates a REAL resident session worker over the daemon socket using the faux
// provider extension (no network, no API key, no paid tokens), and then drives
// the real prepare_update_restart command as a socket client.
//
// counts.total is the caller-visible number from the incident report. It is
// computed here exactly as package-manager-cli.ts computes it during a self
// update: `manifest?.sessions.length ?? 0` - a refused prepare yields no
// manifest and therefore total 0, which is the {total:0, restored:0, resumed:0,
// failed:0} line in the 2026-08-12 incident.

type FixtureMessage = { type: "booted" } | { type: "ready" } | { type: "failed"; error: string };

interface OwnerRecord {
	version: 1;
	role: "supervisor";
	token: string;
	generation: string;
	pid: number;
	processStartId?: string;
	socketPath: string;
	descriptorDir: string;
	agentDir: string;
	appVersion: string;
	phase: "starting" | "owner" | "stopping";
	createdAt: string;
	updatedAt: string;
}

interface FixtureHandle {
	child: ChildProcess;
	diagnostics: { stdout: string; stderr: string };
	messages: FixtureMessage[];
	waiters: Array<{
		predicate: (message: FixtureMessage) => boolean;
		resolve: (message: FixtureMessage) => void;
		timeout: ReturnType<typeof setTimeout>;
	}>;
}

interface ProcessIdentity {
	pid: number;
	processStartId: string;
	label: string;
}

interface Paths {
	agentDir: string;
	descriptorDir: string;
	registryDir: string;
	socketPath: string;
}

interface LiveSupervisor {
	paths: Paths;
	handle: FixtureHandle;
	client: DaemonClient;
	owner: OwnerRecord;
	summary: SessionSummary;
	workerIdentity: ProcessIdentity;
	connection: DaemonAgentConnection;
}

const fixturePath = resolve(__dirname, "../../fixtures/eng-4600-supervisor-fixture.ts");
const fauxExtensionPath = resolve(__dirname, "../../fixtures/eng-4600-faux-extension.ts");
const tsxPath = resolve(__dirname, "../../../../../node_modules/tsx/dist/cli.mjs");
const tsconfigPath = resolve(__dirname, "../../../../../tsconfig.json");
const supervisorRegistryDirEnv = "PRIME_AGENT_INTERNAL_DAEMON_SUPERVISOR_REGISTRY_DIR";

// Every process in this file is either forked directly by spawnFixture or is a
// session worker forked by one of those fixtures inside its own isolated
// agentDir. Nothing else is ever signalled: no pkill, no kill by name, and the
// exact pid+process-start identity is re-verified immediately before SIGKILL.
const handles = new Set<FixtureHandle>();
const clients = new Set<DaemonClient>();
const connections = new Set<DaemonAgentConnection>();
const ownedProcesses = new Map<string, ProcessIdentity>();
const harnesses: Harness[] = [];

afterEach(async () => {
	for (const connection of connections) {
		await connection.dispose().catch(() => undefined);
	}
	connections.clear();
	for (const client of clients) {
		client.close();
	}
	clients.clear();
	for (const handle of handles) {
		if (handle.child.exitCode === null && handle.child.signalCode === null) {
			handle.child.kill("SIGKILL");
			await waitForExit(handle).catch(() => undefined);
		}
	}
	handles.clear();
	for (const identity of ownedProcesses.values()) {
		await killOwnedProcess(identity).catch(() => undefined);
	}
	ownedProcesses.clear();
	while (harnesses.length > 0) {
		harnesses.pop()?.cleanup();
	}
});

function identityState(identity: ProcessIdentity): "exited" | "matching" | "unknown" {
	try {
		process.kill(identity.pid, 0);
	} catch (error) {
		if ((error as NodeJS.ErrnoException).code !== "EPERM") {
			return "exited";
		}
	}
	const observed = getProcessStartId(identity.pid);
	if (observed === undefined) {
		return "unknown";
	}
	return observed === identity.processStartId ? "matching" : "exited";
}

async function killOwnedProcess(identity: ProcessIdentity): Promise<void> {
	if (identityState(identity) === "matching") {
		process.kill(identity.pid, "SIGKILL");
	}
	const deadline = Date.now() + 20_000;
	while (identityState(identity) !== "exited" && Date.now() < deadline) {
		await new Promise((resolveDelay) => setTimeout(resolveDelay, 25));
	}
	if (identityState(identity) !== "exited") {
		throw new Error(`Timed out waiting for ${identity.label} ${identity.pid} to exit`);
	}
}

async function ownProcess(pid: number, label: string, timeoutMs = 5000): Promise<ProcessIdentity> {
	const deadline = Date.now() + timeoutMs;
	while (Date.now() < deadline) {
		const processStartId = getProcessStartId(pid);
		if (processStartId) {
			const identity = { pid, processStartId, label };
			ownedProcesses.set(`${pid}:${processStartId}`, identity);
			return identity;
		}
		await new Promise((resolveDelay) => setTimeout(resolveDelay, 25));
	}
	throw new Error(`Could not capture the process-start identity for ${label} ${pid}`);
}

function dispatchMessage(handle: FixtureHandle, message: FixtureMessage): void {
	const index = handle.waiters.findIndex((waiter) => waiter.predicate(message));
	if (index === -1) {
		handle.messages.push(message);
		return;
	}
	const [waiter] = handle.waiters.splice(index, 1);
	if (!waiter) {
		return;
	}
	clearTimeout(waiter.timeout);
	waiter.resolve(message);
}

function spawnFixture(paths: Paths): FixtureHandle {
	const child = spawn(process.execPath, [tsxPath, fixturePath], {
		cwd: paths.agentDir,
		env: {
			...process.env,
			[supervisorRegistryDirEnv]: paths.registryDir,
			[ENV_AGENT_DIR]: paths.agentDir,
			ENG_4600_AGENT_DIR: paths.agentDir,
			ENG_4600_DESCRIPTOR_DIR: paths.descriptorDir,
			ENG_4600_FIXTURE_MODE: "supervisor",
			ENG_4600_REGISTRY_DIR: paths.registryDir,
			ENG_4600_SOCKET_PATH: paths.socketPath,
			PI_OFFLINE: "1",
			TSX_TSCONFIG_PATH: tsconfigPath,
		},
		stdio: ["ignore", "pipe", "pipe", "ipc"],
	});
	const handle: FixtureHandle = { child, diagnostics: { stdout: "", stderr: "" }, messages: [], waiters: [] };
	handles.add(handle);
	child.stdout?.on("data", (chunk: Buffer) => {
		handle.diagnostics.stdout += chunk.toString("utf8");
	});
	child.stderr?.on("data", (chunk: Buffer) => {
		handle.diagnostics.stderr += chunk.toString("utf8");
	});
	child.on("message", (message: FixtureMessage) => dispatchMessage(handle, message));
	return handle;
}

function waitForMessage(
	handle: FixtureHandle,
	predicate: (message: FixtureMessage) => boolean,
	timeoutMs = 60_000,
): Promise<FixtureMessage> {
	const queued = handle.messages.findIndex(predicate);
	if (queued !== -1) {
		const [message] = handle.messages.splice(queued, 1);
		if (message) {
			return Promise.resolve(message);
		}
	}
	return new Promise((resolveMessage, rejectMessage) => {
		const timeout = setTimeout(() => {
			handle.waiters = handle.waiters.filter((waiter) => waiter.timeout !== timeout);
			rejectMessage(
				new Error(
					`Timed out waiting for fixture message (exit=${handle.child.exitCode}/${handle.child.signalCode})\n${handle.diagnostics.stderr}`,
				),
			);
		}, timeoutMs);
		handle.waiters.push({ predicate, resolve: resolveMessage, timeout });
	});
}

function waitForExit(handle: FixtureHandle, timeoutMs = 20_000): Promise<void> {
	if (handle.child.exitCode !== null || handle.child.signalCode !== null) {
		return Promise.resolve();
	}
	return new Promise((resolveExit, rejectExit) => {
		const timeout = setTimeout(() => rejectExit(new Error("Timed out waiting for fixture exit")), timeoutMs);
		handle.child.once("exit", () => {
			clearTimeout(timeout);
			resolveExit();
		});
	});
}

async function createPaths(): Promise<Paths> {
	const harness = await createHarness();
	harnesses.push(harness);
	return {
		agentDir: harness.tempDir,
		descriptorDir: join(harness.tempDir, "workers"),
		registryDir: join(harness.tempDir, "registry"),
		socketPath: join(harness.tempDir, "daemon.sock"),
	};
}

async function connectEventually(socketPath: string): Promise<DaemonClient> {
	const deadline = Date.now() + 30_000;
	let lastError: unknown;
	while (Date.now() < deadline) {
		const client = new DaemonClient(socketPath);
		try {
			await client.connect(500);
			await client.waitForHello(2000);
			clients.add(client);
			return client;
		} catch (error) {
			lastError = error;
			client.close();
			await new Promise((resolveDelay) => setTimeout(resolveDelay, 25));
		}
	}
	throw new Error(`Timed out connecting to the fixture supervisor: ${String(lastError)}`);
}

function ownerDirectory(paths: Paths, generation: string): string {
	return join(paths.registryDir, `${generation}.owner`);
}

function ownerRecordPath(paths: Paths, generation: string): string {
	return join(ownerDirectory(paths, generation), "owner.json");
}

function listOwnerRecords(registryDir: string): OwnerRecord[] {
	if (!existsSync(registryDir)) {
		return [];
	}
	return readdirSync(registryDir)
		.filter((name) => name.endsWith(".owner"))
		.map((name) => JSON.parse(readFileSync(join(registryDir, name, "owner.json"), "utf8")) as OwnerRecord);
}

async function waitForSingleOwner(registryDir: string, timeoutMs = 30_000): Promise<OwnerRecord> {
	const deadline = Date.now() + timeoutMs;
	while (Date.now() < deadline) {
		const [owner] = listOwnerRecords(registryDir);
		if (owner) {
			return owner;
		}
		await new Promise((resolveDelay) => setTimeout(resolveDelay, 25));
	}
	throw new Error("Timed out waiting for the fixture supervisor owner record");
}

function requireSessionSummary(value: unknown): SessionSummary {
	if (!value || typeof value !== "object" || typeof (value as Partial<SessionSummary>).id !== "string") {
		throw new Error("The daemon did not return a session summary");
	}
	return value as SessionSummary;
}

/**
 * Boots a real DaemonSupervisor child and creates one real resident session
 * worker through the real socket protocol. The session runs on the faux
 * provider extension: no network, no real provider, no API key, no tokens.
 */
async function bootSupervisorWithRealSession(): Promise<LiveSupervisor> {
	const paths = await createPaths();
	const handle = spawnFixture(paths);
	await waitForMessage(handle, (message) => message.type === "booted");
	handle.child.send({ type: "go" });
	const ready = await waitForMessage(handle, (message) => message.type === "ready" || message.type === "failed");
	if (ready.type !== "ready") {
		throw new Error(`Supervisor fixture failed to start: ${(ready as { error: string }).error}`);
	}
	if (handle.child.pid !== undefined) {
		await ownProcess(handle.child.pid, "supervisor fixture").catch(() => undefined);
	}
	const owner = await waitForSingleOwner(paths.registryDir);
	const client = await connectEventually(paths.socketPath);
	const created = await client.request(
		{
			type: "create",
			config: {
				agentDir: paths.agentDir,
				apiKey: "faux-key",
				cwd: paths.agentDir,
				extensions: [fauxExtensionPath],
				model: "faux",
				noContextFiles: true,
				noExtensions: false,
				noSkills: true,
				noTools: true,
				provider: "faux",
			},
		},
		60_000,
	);
	if (!created.success) {
		throw new Error(`${created.error}\nfixture stderr:\n${handle.diagnostics.stderr}`);
	}
	const summary = requireSessionSummary(created.data);
	if (!summary.workerPid) {
		throw new Error("The resident session worker did not expose its pid");
	}
	const workerIdentity = await ownProcess(summary.workerPid, "resident session worker");
	// A session with no content and no queued work is legitimately discarded by
	// createUpdateRestartSession(). One faux round trip gives the session real
	// history and a materialized session file, so the manifest must carry it.
	const activeSessionId = summary.activeSessionId ?? summary.id;
	const connection = await DaemonAgentConnection.attach(client, activeSessionId, { recoverDaemon: async () => {} });
	connections.add(connection);
	await connection.getInitialSnapshot();
	await connection.prompt("checkpoint me");
	await connection.waitForIdle();
	expect(await connection.getMessages()).toContainEqual(
		expect.objectContaining({
			role: "assistant",
			content: [expect.objectContaining({ text: "upgrade response 1" })],
		}),
	);
	return { paths, handle, client, owner, summary, workerIdentity, connection };
}

async function listSessions(client: DaemonClient): Promise<SessionSummary[]> {
	const listed = await client.request({ type: "list" }, 20_000);
	if (!listed.success) {
		throw new Error(listed.error);
	}
	return (listed.data as { sessions: unknown[] }).sessions.map(requireSessionSummary);
}

/**
 * The macOS periodic $TMPDIR reaper deletes cold FILES and leaves the
 * surrounding DIRECTORIES in place, and it never signals the owning process.
 * The owner record is the coldest file in the registry tree because it is only
 * written on ownership change. This is exactly that prune, on one file.
 */
function reapOwnerRecordFileOnly(paths: Paths, generation: string): string {
	const path = ownerRecordPath(paths, generation);
	unlinkSync(path);
	return path;
}

/** Genuine takeover: a different, unambiguously live generation owns the entry. */
function installReplacementOwnerRecord(paths: Paths, owner: OwnerRecord): void {
	const now = new Date().toISOString();
	writeFileSync(
		ownerRecordPath(paths, owner.generation),
		`${JSON.stringify({
			...owner,
			token: "takeover-token",
			generation: `${owner.generation}-successor`,
			pid: process.pid,
			processStartId: getProcessStartId(process.pid),
			updatedAt: now,
		})}\n`,
		{ mode: 0o600 },
	);
}

interface PrepareOutcome {
	success: boolean;
	error?: string;
	manifest?: DaemonUpdateRestartManifest;
	/** Computed exactly as package-manager-cli.ts does: `manifest?.sessions.length ?? 0`. */
	total: number;
}

async function prepareUpdateRestart(client: DaemonClient): Promise<PrepareOutcome> {
	const response = await client.request({ type: "prepare_update_restart" }, 120_000);
	if (!response.success) {
		return { success: false, error: response.error, total: 0 };
	}
	const manifest = response.data as DaemonUpdateRestartManifest;
	return { success: true, manifest, total: manifest.sessions.length };
}

describe("#1291/#1148 end-to-end: a reaped owner record discards a live session tree", () => {
	it("THESIS: prepare_update_restart checkpoints a real resident session while the owner record is intact", async () => {
		const live = await bootSupervisorWithRealSession();

		expect(existsSync(ownerRecordPath(live.paths, live.owner.generation))).toBe(true);
		// The session is real: a separate live worker process with a descriptor on disk.
		expect(identityState(live.workerIdentity)).toBe("matching");
		expect(await listSessions(live.client)).toHaveLength(1);

		const outcome = await prepareUpdateRestart(live.client);

		expect(outcome).toMatchObject({ success: true });
		// The teeth of the whole exercise: this fails if no session ever existed.
		expect(outcome.total).toBeGreaterThanOrEqual(1);
		expect(outcome.manifest?.sessions.map((session) => session.activeSessionId)).toContain(
			live.summary.activeSessionId ?? live.summary.id,
		);
		for (const session of outcome.manifest?.sessions ?? []) {
			expect(session.sessionFile).toEqual(expect.any(String));
		}
		expect(outcome.manifest?.discardedActiveSessionIds ?? []).not.toContain(
			live.summary.activeSessionId ?? live.summary.id,
		);
	}, 180_000);

	it("ANTITHESIS: unlinking only the owner record collapses the same live session tree to counts.total 0 [PINS #1291/#1148]", async () => {
		const live = await bootSupervisorWithRealSession();
		// Vacuity guard inside the falsifier: the session really exists first.
		expect(await listSessions(live.client)).toHaveLength(1);
		expect(identityState(live.workerIdentity)).toBe("matching");

		reapOwnerRecordFileOnly(live.paths, live.owner.generation);

		const outcome = await prepareUpdateRestart(live.client);

		expect(outcome.success).toBe(false);
		// Name the mechanism, not the symptom. The wire response carries only the
		// message, and this message is DaemonSupervisorOwnershipLostError
		// (code supervisor_generation_stale) for this exact generation.
		expect(outcome.error).toBe(
			`Daemon supervisor generation ${live.owner.generation} no longer owns its registry entry`,
		);
		// The incident line verbatim: {total:0, restored:0, resumed:0, failed:0}.
		expect(outcome.total).toBe(0);
		// And the tree that was just discarded is demonstrably still alive: the
		// supervisor process, its session worker, and the descriptor all survive.
		expect(live.handle.child.exitCode).toBeNull();
		expect(identityState(live.workerIdentity)).toBe("matching");
		expect(readdirSync(live.paths.descriptorDir).filter((name) => name.endsWith(".json"))).toHaveLength(1);
	}, 180_000);

	it("VACUITY GUARD: the reaper removes the owner record file only and leaves every directory standing", async () => {
		const live = await bootSupervisorWithRealSession();

		const pruned = reapOwnerRecordFileOnly(live.paths, live.owner.generation);

		expect(existsSync(pruned)).toBe(false);
		expect(statSync(ownerDirectory(live.paths, live.owner.generation)).isDirectory()).toBe(true);
		expect(existsSync(join(ownerDirectory(live.paths, live.owner.generation), "scope.json"))).toBe(true);
		expect(statSync(live.paths.registryDir).isDirectory()).toBe(true);
		// The supervisor was never signalled; this is a file prune, not a teardown.
		expect(live.handle.child.exitCode).toBeNull();
		expect(identityState(live.workerIdentity)).toBe("matching");
	}, 180_000);

	// EXECUTABLE SPECIFICATION OF THE FIX. Both branches are pinned in one test
	// so a fix that simply tolerates every missing or foreign owner record cannot
	// pass. Expected to fail on current main because assertCurrent() collapses
	// "record absent" and "record replaced by another live generation" into one
	// throw. Never delete this test; when the fix lands it turns green.
	it.fails("SYNTHESIS: a reaped record under a live owner must preserve the session tree while a live takeover still refuses", async () => {
		const reaped = await bootSupervisorWithRealSession();
		expect(await listSessions(reaped.client)).toHaveLength(1);
		reapOwnerRecordFileOnly(reaped.paths, reaped.owner.generation);
		const reapedOutcome = await prepareUpdateRestart(reaped.client);

		const takenOver = await bootSupervisorWithRealSession();
		expect(await listSessions(takenOver.client)).toHaveLength(1);
		installReplacementOwnerRecord(takenOver.paths, takenOver.owner);
		const takeoverOutcome = await prepareUpdateRestart(takenOver.client);

		// Absent record under a live owner: recoverable, and the sessions proven
		// to exist in the THESIS survive the handoff.
		expect(reapedOutcome.success).toBe(true);
		expect(reapedOutcome.total).toBeGreaterThanOrEqual(1);
		expect(reapedOutcome.manifest?.sessions.map((session) => session.activeSessionId)).toContain(
			reaped.summary.activeSessionId ?? reaped.summary.id,
		);
		// Replaced by a different live generation: still fatal, still zero.
		expect(takeoverOutcome.success).toBe(false);
		expect(takeoverOutcome.error).toBe(
			`Daemon supervisor generation ${takenOver.owner.generation} no longer owns its registry entry`,
		);
		expect(takeoverOutcome.total).toBe(0);
	}, 180_000);
});
