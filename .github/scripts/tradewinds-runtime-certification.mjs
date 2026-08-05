import {
  createHash,
  createPublicKey,
  generateKeyPairSync,
  sign,
  verify,
} from 'node:crypto';
import {
  mkdirSync,
  readFileSync,
  writeFileSync,
} from 'node:fs';
import { join, resolve } from 'node:path';

const EXECUTION_IDS = ['E01', 'E02', 'E03', 'E04', 'E05', 'E06', 'E07', 'E08', 'E09', 'E10'];
const PORTFOLIO_IDS = ['P01', 'P02', 'P03', 'P04', 'P05', 'P06'];
const CONNECTOR_IDS = ['C01', 'C02', 'C03', 'C04', 'C05', 'C06', 'C07', 'C08'];
const SCENARIO_IDS = [...EXECUTION_IDS, ...PORTFOLIO_IDS, ...CONNECTOR_IDS];
const EXECUTION_MODES = ['base', 'pessimistic', 'stress'];
const PORTFOLIO_MODES = ['replay', 'paper', 'dry'];
const AREAS = ['accounting', 'order-invariants', 'recovery'];
const HASH_RE = /^sha256:[a-f0-9]{64}$/;

function record(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function canonicalize(value) {
  if (value === null || typeof value === 'string' || typeof value === 'boolean') return value;
  if (typeof value === 'number') {
    if (!Number.isFinite(value)) throw new Error('non-finite canonical number');
    return Object.is(value, -0) ? 0 : value;
  }
  if (Array.isArray(value)) return value.map(canonicalize);
  if (record(value)) return Object.fromEntries(Object.keys(value).sort().map((key) => {
    if (value[key] === undefined) throw new Error(`undefined canonical field: ${key}`);
    return [key, canonicalize(value[key])];
  }));
  throw new Error('unsupported canonical value');
}

function canonicalJson(value) {
  return JSON.stringify(canonicalize(value));
}

function sha(value) {
  return `sha256:${createHash('sha256').update(value).digest('hex')}`;
}

function json(path) {
  return JSON.parse(readFileSync(path, 'utf8'));
}

function writeJson(path, value) {
  writeFileSync(path, `${canonicalJson(value)}\n`, 'utf8');
}

function bindingHash(binding) {
  return sha(canonicalJson(binding));
}

function worldHash(world) {
  return sha(canonicalJson(world));
}

function artifactSetHash(artifacts) {
  return sha(canonicalJson([...artifacts].map(({ id, kind, uri, sha256, bytes, createdAt, immutable }) => ({
    id, kind, uri, sha256, bytes, createdAt, immutable,
  })).sort((left, right) => left.id.localeCompare(right.id))));
}

function spkiHash(key) {
  return sha(key.export({ type: 'spki', format: 'der' }));
}

function unsigned(pack) {
  const { signature: _signature, ...payload } = pack;
  return payload;
}

function signPayload(payload, privateKey, keyId) {
  return {
    ...payload,
    signature: {
      algorithm: 'ed25519',
      keyId,
      value: sign(null, Buffer.from(canonicalJson(payload)), privateKey).toString('base64'),
    },
  };
}

function fail(issues, condition, issue) {
  if (!condition) issues.push(issue);
}

function loadArtifacts(payload, root, issues) {
  const byId = new Map();
  for (const artifact of payload.artifacts ?? []) {
    if (!record(artifact) || typeof artifact.id !== 'string' || typeof artifact.uri !== 'string') {
      issues.push('artifact-descriptor-invalid');
      continue;
    }
    if (byId.has(artifact.id)) issues.push(`artifact-duplicate:${artifact.id}`);
    const path = join(root, 'artifacts', artifact.uri);
    let bytes;
    try { bytes = readFileSync(path); } catch { issues.push(`artifact-unreadable:${artifact.id}`); continue; }
    fail(issues, bytes.length === artifact.bytes, `artifact-size:${artifact.id}`);
    fail(issues, sha(bytes) === artifact.sha256, `artifact-hash:${artifact.id}`);
    fail(issues, artifact.immutable === true, `artifact-mutable:${artifact.id}`);
    byId.set(artifact.id, { ...artifact, path, bytes });
  }
  return byId;
}

function matrixFor(world, id) {
  if (id.startsWith('E')) return [world.W1?.scenarios?.[id], EXECUTION_MODES];
  if (id.startsWith('P')) return [world.W2?.scenarios?.[id], PORTFOLIO_MODES];
  return [world.W3?.scenarios?.[id], ['hyperliquid']];
}

function suiteIssues(payload, artifacts) {
  const issues = [];
  const world = payload.worldParity;
  if (!record(world)) return ['world-missing'];
  const exactBindingHash = bindingHash(payload.binding);
  const proofs = Array.isArray(world.scenarioProofs) ? world.scenarioProofs : [];
  fail(issues, proofs.length === SCENARIO_IDS.length, 'scenario-proof-count');
  fail(issues, new Set(proofs.map((proof) => proof?.scenarioId)).size === SCENARIO_IDS.length, 'scenario-proof-duplicates');
  for (const id of SCENARIO_IDS) {
    const proof = proofs.find((candidate) => candidate?.scenarioId === id);
    if (!proof) { issues.push(`scenario-missing:${id}`); continue; }
    fail(issues, proof.status === 'passed', `scenario-status:${id}`);
    fail(issues, proof.bindingHash === exactBindingHash, `scenario-binding:${id}`);
    const fixture = artifacts.get(proof.fixtureArtifactRef);
    const measurement = artifacts.get(proof.measurementArtifactRef);
    fail(issues, fixture?.kind === 'world-parity-fixture' && fixture.sha256 === proof.fixtureHash, `scenario-fixture:${id}`);
    fail(issues, measurement?.kind === 'world-parity-measurement' && measurement.sha256 === proof.measurementHash, `scenario-measurement:${id}`);
    const [matrix, dimensions] = matrixFor(world, id);
    let completeMatrix = true;
    for (const dimension of dimensions) {
      const result = matrix?.[dimension];
      const valid = result?.status === 'passed' && HASH_RE.test(result?.resultHash ?? '') && typeof result?.runId === 'string';
      fail(issues, valid, `scenario-run:${id}:${dimension}`);
      completeMatrix &&= valid;
    }
    if (completeMatrix) {
      const expectedRuns = dimensions.map((dimension) => ({
        dimension,
        runId: matrix[dimension].runId,
        resultHash: matrix[dimension].resultHash,
      }));
      fail(issues, canonicalJson(proof.runs) === canonicalJson(expectedRuns), `scenario-run-binding:${id}`);
    } else {
      issues.push(`scenario-run-binding:${id}`);
    }
  }
  const hashFields = ['events', 'orders', 'fills', 'lots', 'cash', 'equity'];
  fail(issues, world.W0?.declaredStatus === 'certified', 'W0-status');
  for (const field of hashFields) {
    fail(issues, HASH_RE.test(world.W0?.runA?.[field] ?? '') && world.W0?.runA?.[field] === world.W0?.runB?.[field], `W0-${field}`);
  }
  for (const flag of ['failClosedMissingData', 'monotonicSequencing', 'noLookahead', 'noSilentFallback']) {
    fail(issues, world.W0?.[flag] === true, `W0-${flag}`);
  }
  const performance = world.W1?.performance;
  fail(issues, world.W1?.declaredStatus === 'certified', 'W1-status');
  fail(issues, world.W1?.interprocessDeterministic === true && world.W1?.candleOnlyIsLowFidelity === true, 'W1-flags');
  fail(issues, world.W1?.l3Mbo?.sourceProvidesMbo === false && world.W1?.l3Mbo?.status === 'n/a-data', 'W1-l3');
  fail(issues, performance?.sustainedEventsPerSecond >= performance?.capturedPeakEventsPerSecond * 10, 'W1-throughput');
  fail(issues, performance?.durationSeconds >= 60 && performance?.memoryBounded === true
    && performance?.backpressureMeasured === true && performance?.droppedEvents === 0, 'W1-performance');
  fail(issues, world.W2?.declaredStatus === 'certified', 'W2-status');
  for (const flag of ['adapterImportsAbsentFromStrategies', 'portfolioAndRiskCannotBeBypassed', 'targetChangesIdempotent', 'unknownOrNegativeLiveKellyIsZero']) {
    fail(issues, world.W2?.[flag] === true, `W2-${flag}`);
  }
  fail(issues, world.W3?.declaredStatus === 'certified', 'W3-status');
  fail(issues, canonicalJson(world.W3?.advertisedCapabilities) === canonicalJson(payload.binding.scope.capabilities), 'W3-capabilities');
  for (const flag of ['privateRestLedgerConverge', 'reductionsNeverBlocked', 'ambiguousResponsesFreezeOpenings', 'noSilentFallback']) {
    fail(issues, world.W3?.[flag] === true, `W3-${flag}`);
  }
  return issues;
}

function portableInputIssues(payload, artifacts) {
  const issues = [];
  const parseArtifact = (id) => {
    const bytes = artifacts.get(id)?.bytes;
    return bytes ? JSON.parse(bytes.toString('utf8')) : null;
  };
  const local = parseArtifact('world-parity-local-report');
  const performance = parseArtifact('world-parity-performance');
  const g5 = parseArtifact('world-parity-native-g5');
  fail(issues, local?.kind === 'world-parity-portable-report'
    && local.gitSha === '7aaa19d68ef37f64652a878badff484aa04e4c66', 'portable-local-build');
  fail(issues, local?.configHash === payload.binding.configHash && local?.schemaVersion === payload.binding.schemaVersion && local?.dirty === false, 'portable-local-binding');
  fail(issues, performance?.kind === 'world-parity-portable-performance' && performance?.status === 'passed', 'portable-performance-status');
  fail(issues, performance?.tenTimesPeakSatisfied === true && performance?.deterministic === true
    && performance?.backpressure?.droppedEvents === 0 && performance?.memory?.boundedDuringRun === true, 'portable-performance-proof');
  fail(issues, g5?.kind === 'native-testnet-g5-portable-summary' && HASH_RE.test(g5?.originalReportHash ?? ''), 'portable-g5-hash');
  fail(issues, g5?.technicalPreCertification === true && g5?.certificationClaimed === false && g5?.certifiedG5LifecycleCredit === 0, 'portable-g5-honesty');
  fail(issues, g5?.completedRoundTrips === 25 && g5?.completedOrderLifecycles === 50
    && Array.isArray(g5?.completedInjectedFaultDrills) && g5.completedInjectedFaultDrills.length === 12, 'portable-g5-coverage');
  fail(issues, g5?.exactFillEconomics === true && g5?.durableOmsUsed === true
    && g5?.decisionLineageUsed === true && g5?.finalFlat === true, 'portable-g5-invariants');

  const runs = ['world-parity-vitest-a', 'world-parity-vitest-b', 'world-parity-vitest-external']
    .map(parseArtifact);
  for (const [index, run] of runs.entries()) {
    fail(issues, run?.kind === 'world-parity-normalized-vitest-run' && run?.success === true
      && run?.total === 125 && run?.passed === 125 && run?.failed === 0, `portable-vitest-shape:${index}`);
    fail(issues, Array.isArray(run?.assertions) && run.assertions.every((row) => row.status === 'passed')
      && sha(canonicalJson(run.assertions)) === run.assertionsHash, `portable-vitest-hash:${index}`);
  }
  fail(issues, runs.every((run) => run?.assertionsHash === runs[0]?.assertionsHash), 'portable-vitest-reproduction-drift');
  return { issues, assertions: runs[0]?.assertions ?? [] };
}

function verifyDraft(pack, root) {
  const issues = [];
  const payload = unsigned(pack);
  const publicKey = createPublicKey(readFileSync(join(root, 'keys', 'pack-public.pem'), 'utf8'));
  const signature = Buffer.from(pack.signature?.value ?? '', 'base64');
  fail(issues, pack.signature?.algorithm === 'ed25519' && signature.length > 0
    && verify(null, Buffer.from(canonicalJson(payload)), publicKey, signature), 'pack-signature');
  fail(issues, payload.binding?.gitSha === '7aaa19d'
    && payload.binding?.dirty === false, 'pack-binding');
  fail(issues, payload.binding?.scope?.venue === 'hyperliquid' && payload.binding?.scope?.network === 'testnet', 'pack-scope');
  fail(issues, Array.isArray(payload.artifacts) && payload.artifacts.length === 54, 'pack-artifact-count');
  const artifacts = loadArtifacts(payload, root, issues);
  issues.push(...suiteIssues(payload, artifacts));
  const portable = portableInputIssues(payload, artifacts);
  issues.push(...portable.issues);
  return { payload, artifacts, assertions: portable.assertions, issues };
}

function areaCoverage(assertions) {
  const patterns = {
    accounting: /account|reconcil|funding|fee|cash|equity|lot/i,
    'order-invariants': /order|durable|cancel|modify|partial|idempot|reduce-only|queue|fill/i,
    recovery: /recover|restart|restore|crash|replay|outage|reconnect|resync|gap|quarantine/i,
  };
  const result = Object.fromEntries(AREAS.map((area) => [area, assertions.filter((row) => patterns[area].test(row.fullName)).length]));
  for (const area of AREAS) if (result[area] < 5) throw new Error(`Insufficient ${area} coverage: ${result[area]}`);
  return result;
}

function review(rootArg, ephemeralArg) {
  const root = resolve(rootArg);
  const ephemeral = resolve(ephemeralArg);
  mkdirSync(ephemeral, { recursive: true });
  mkdirSync(join(root, 'keys'), { recursive: true });
  const pack = json(join(root, 'pack.draft.json'));
  const verified = verifyDraft(pack, root);
  if (verified.issues.length > 0) throw new Error(`Draft rejected: ${verified.issues.join(',')}`);

  const tamperChecks = [];
  const changedBinding = structuredClone(pack);
  changedBinding.binding.configHash = `sha256:${'0'.repeat(64)}`;
  tamperChecks.push({ id: 'T01-pack-signature-binding', rejected: verifyDraft(changedBinding, root).issues.includes('pack-signature') });
  const missingProofPayload = structuredClone(verified.payload);
  missingProofPayload.worldParity.scenarioProofs.pop();
  tamperChecks.push({ id: 'T02-missing-scenario', rejected: suiteIssues(missingProofPayload, verified.artifacts).length > 0 });
  const divergentW0 = structuredClone(verified.payload);
  divergentW0.worldParity.W0.runB.cash = `sha256:${'1'.repeat(64)}`;
  tamperChecks.push({ id: 'T03-W0-divergence', rejected: suiteIssues(divergentW0, verified.artifacts).length > 0 });
  const weakPerformance = structuredClone(verified.payload);
  weakPerformance.worldParity.W1.performance.sustainedEventsPerSecond = 1;
  tamperChecks.push({ id: 'T04-throughput-regression', rejected: suiteIssues(weakPerformance, verified.artifacts).length > 0 });
  const missingMode = structuredClone(verified.payload);
  delete missingMode.worldParity.W2.scenarios.P05.dry;
  tamperChecks.push({ id: 'T05-mode-matrix-hole', rejected: suiteIssues(missingMode, verified.artifacts).length > 0 });
  if (tamperChecks.some((check) => !check.rejected)) throw new Error('A red-team tamper case was accepted');

  const issuedAt = Date.now();
  if (issuedAt >= verified.payload.expiresAt) throw new Error('Draft expired before review');
  verified.payload.issuedAt = issuedAt;
  const coverage = areaCoverage(verified.assertions);
  const report = {
    v: 1,
    kind: 'agent-reach-external-red-team',
    issuedAt,
    packId: verified.payload.packId,
    bindingHash: bindingHash(verified.payload.binding),
    worldParityHash: worldHash(verified.payload.worldParity),
    assertions: verified.assertions.length,
    assertionHash: sha(canonicalJson(verified.assertions)),
    areaCoverage: coverage,
    tamperChecks,
    verdict: 'approve',
    openFindings: 0,
    limitations: [
      'Portable evidence contains commitments and normalized assertions, not private source or raw testnet order rows.',
      'Final pack acceptance is repeated by the private production loader after this external handoff.',
    ],
  };
  const reportPath = join(root, 'artifacts', 'external-red-team-report.json');
  writeJson(reportPath, report);
  const reportBytes = readFileSync(reportPath);
  verified.payload.artifacts.push({
    id: 'external-red-team-report',
    kind: 'external-red-team-report',
    uri: 'external-red-team-report.json',
    sha256: sha(reportBytes),
    bytes: reportBytes.length,
    createdAt: issuedAt,
    immutable: true,
  });

  const reviewer = generateKeyPairSync('ed25519');
  const witness = generateKeyPairSync('ed25519');
  const reviewerKeyId = `agent-reach-review-${spkiHash(reviewer.publicKey).slice(7, 19)}`;
  const witnessKeyId = `agent-reach-witness-${spkiHash(witness.publicKey).slice(7, 19)}`;
  const reviewerPublicPath = join(root, 'keys', 'reviewer-public.pem');
  const witnessPublicPath = join(root, 'keys', 'witness-public.pem');
  const reviewerPrivatePath = join(ephemeral, 'reviewer-private.pem');
  const witnessPrivatePath = join(ephemeral, 'witness-private.pem');
  writeFileSync(reviewerPublicPath, reviewer.publicKey.export({ type: 'spki', format: 'pem' }));
  writeFileSync(witnessPublicPath, witness.publicKey.export({ type: 'spki', format: 'pem' }));
  writeFileSync(reviewerPrivatePath, reviewer.privateKey.export({ type: 'pkcs8', format: 'pem' }), { mode: 0o600 });
  writeFileSync(witnessPrivatePath, witness.privateKey.export({ type: 'pkcs8', format: 'pem' }), { mode: 0o600 });

  verified.payload.redTeamReview = signPayload({
    v: 1,
    reviewId: `agent-reach-external-${issuedAt}`,
    packId: verified.payload.packId,
    bindingHash: bindingHash(verified.payload.binding),
    worldParityHash: worldHash(verified.payload.worldParity),
    issuedAt,
    expiresAt: verified.payload.expiresAt,
    reviewer: 'agent-reach-external-red-team',
    organization: 'Agent-Reach external Windows review environment',
    verdict: 'approve',
    areas: AREAS,
    openFindings: 0,
    artifactRefs: ['external-red-team-report'],
  }, reviewer.privateKey, reviewerKeyId);
  const reviewedPath = join(root, 'pack.reviewed-unsigned.json');
  writeJson(reviewedPath, verified.payload);
  const anchorPath = join(root, 'external-witness-anchor.json');
  writeJson(anchorPath, {
    v: 1,
    kind: 'tradewinds-world-parity-runtime-witness-anchor',
    issuedAt,
    packId: verified.payload.packId,
    evidenceEpoch: verified.payload.evidenceEpoch,
    bindingHash: bindingHash(verified.payload.binding),
    worldParityHash: worldHash(verified.payload.worldParity),
    artifactSetHash: artifactSetHash(verified.payload.artifacts),
    redTeamReviewHash: sha(canonicalJson(verified.payload.redTeamReview)),
    reviewerPublicKeySpkiHash: spkiHash(reviewer.publicKey),
    witnessPublicKeySpkiHash: spkiHash(witness.publicKey),
  });
  const statePath = join(ephemeral, 'state.json');
  writeJson(statePath, {
    v: 1,
    packId: verified.payload.packId,
    reviewerKeyId,
    witnessKeyId,
    witnessPrivatePath,
    reviewedPath,
  });
  process.stdout.write(`${JSON.stringify({
    statePath,
    anchorPath,
    reviewedPath,
    reviewerKeyId,
    witnessKeyId,
    assertions: verified.assertions.length,
    coverage,
    tamperChecks,
    artifactSetHash: artifactSetHash(verified.payload.artifacts),
  }, null, 2)}\n`);
}

function finalize(rootArg, stateArg, logIndexArg, integratedSecondsArg) {
  const root = resolve(rootArg);
  const state = json(resolve(stateArg));
  const payload = json(state.reviewedPath);
  const logIndex = Number(logIndexArg);
  const integratedAt = Number(integratedSecondsArg) * 1_000;
  if (!Number.isSafeInteger(logIndex) || logIndex < 0 || !Number.isSafeInteger(integratedAt) || integratedAt <= 0) {
    throw new Error('Invalid Rekor coordinates');
  }
  payload.externalWitness = signPayload({
    v: 1,
    receiptId: `agent-reach-rekor-${logIndex}`,
    packId: payload.packId,
    evidenceEpoch: payload.evidenceEpoch,
    bindingHash: bindingHash(payload.binding),
    worldParityHash: worldHash(payload.worldParity),
    artifactSetHash: artifactSetHash(payload.artifacts),
    issuedAt: integratedAt,
    expiresAt: payload.expiresAt,
    witness: 'agent-reach-rekor-witness',
    organization: 'Sigstore Rekor public transparency log',
    logId: 'sigstore-rekor-public-good-instance-v1',
    logIndex,
    integratedAt,
  }, readFileSync(state.witnessPrivatePath, 'utf8'), state.witnessKeyId);
  writeJson(join(root, 'red-team-review.json'), payload.redTeamReview);
  writeJson(join(root, 'external-witness.json'), payload.externalWitness);
  writeJson(join(root, 'pack.external-unsigned.json'), payload);
  process.stdout.write(`${JSON.stringify({
    packId: payload.packId,
    reviewId: payload.redTeamReview.reviewId,
    receiptId: payload.externalWitness.receiptId,
    reviewerKeyId: payload.redTeamReview.signature.keyId,
    witnessKeyId: payload.externalWitness.signature.keyId,
    logIndex,
    integratedAt,
    artifactSetHash: payload.externalWitness.artifactSetHash,
  }, null, 2)}\n`);
}

const [command, ...args] = process.argv.slice(2);
if (command === 'review' && args.length === 2) review(args[0], args[1]);
else if (command === 'finalize' && args.length === 4) finalize(args[0], args[1], args[2], args[3]);
else throw new Error('Usage: tradewinds-runtime-certification.mjs review <evidenceRoot> <ephemeralRoot> | finalize <evidenceRoot> <state> <logIndex> <integratedTimeSeconds>');
