# Worker Coordination Board

Date: `2026-05-03`
Status: `coordination surface`

This board exists because the main diagrams now expose many blockers, but a
worker needs a smaller routing surface: which lane owns the next move, what
files are in scope, what proves progress, and what must not be promoted by
prose.

## Active Assignment Round

Round date: `2026-05-04`
Round owner: `W0 orchestrator / integrator`
Round status: `active`

| Lane | Agent | Assignment | Dependency note | Promotion gate |
|---|---|---|---|---|
| `W1` | `Erdos` (`019dee7a-6313-78a3-b586-d4bae6315fc2`) | Inspect and advance the MDL/CR carrier seam with the smallest safe typed Agda receipt or sharper typed obstruction. | Critical dependency for full `W3` empirical equality and `W4` carrier promotion. | Targeted MDL seam Agda; no prose-only CR-flat claim. |
| `W2` | `Boole` (`019dee7a-652c-7b02-9b36-fc1f0905cd12`) | Inspect and advance the natural / `p2` bridge-or-obstruction and convergence-bound target. | Partially independent of `W1`; must not claim empirical or chemistry closure. | Targeted natural/dynamics Agda; L2/offline only if required. |
| `W3` | `Tesla` (`019dee7a-65ee-7f30-9eae-7f583e86e759`) | Inspect empirical bridge modules and produce typed equality if carrier exists, otherwise a precise carrier-mismatch diagnostic. | Full equality waits on `W1`; mismatch/status surfaces may advance independently. | Targeted empirical Agda or docs diff check. |
| `W4` | `Poincare` (`019dee7a-66db-7343-8ef5-4fe6e7a402a2`) | Inspect Candidate256 chemistry surfaces and advance a symmetric nontrivial quotient-sensitive law or sharper typed requirement. | Static law work can advance independently; full carrier promotion waits on `W1`. | Targeted chemistry Agda; no spectra, bonding, or wet-lab claim. |

## Formal Model

O:
- Repo owner/reviewer accepts or rejects promoted theorem and documentation
  changes.
- Orchestrator assigns one nonblocking lane per worker.
- Workers own bounded file surfaces and must not modify unrelated dirty files.

R:
- Convert diagram blockers into executable worker lanes.
- Keep lanes disjoint enough for parallel work.
- Preserve the proof-obligation boundary until a named theorem owner and
  validation result exist.

C:
- Coordination docs:
  `Docs/WorkerCoordinationBoard.md`,
  `Docs/AutonomousExecutionBrief.md`,
  `Docs/AutonomousOrchestratorClosureFrame.md`,
  `TODO.md`, `CHANGELOG.md`.
- Diagrams:
  `Docs/WorkerCoordinationMap.puml`,
  `Docs/RepoMetasystem.puml`,
  `Docs/PhysicsUnificationMap.puml`,
  `Docs/PhysicsRealityRoadmap.puml`.
- Proof-obligation owner:
  `DASHI/Physics/Closure/P0BlockadeProofObligations.agda`.

S:
- The strongest current closure path is theorem-owned, but several red/yellow
  diagram blocks remain blockers.
- The recurring P0 blockers are not lack of prose; they are missing carriers,
  laws, receipts, validation, or theorem consumers.
- The current task is coordination and routing. It does not discharge any P0
  blocker.

L:
- `unassigned blocker`
  -> `worker-lane assigned`
  -> `candidate module/doc patch`
  -> `targeted verification`
  -> `diagram/docs/TODO/changelog synchronized`
  -> `promoted only if theorem/receipt gate is met`

P:
- Maintain one board of lanes and one diagram of dependencies.
- Use lane IDs in worker prompts, status updates, and follow-up commits.
- Keep high-risk theorem lanes separate from docs-only guardrail lanes.

G:
- A lane can move out of `blocked` only by a named Agda theorem owner, a typed
  proof-obligation inhabitant, or an explicit empirical/carrier-mismatch
  diagnostic.
- A worker may update only its assigned files.
- Diagram colors remain governance colors: red/pink is open or empirical
  non-claim; yellow is bridge/advanced-but-blocked; green is theorem-owned.
- If a `.puml` file changes, run `./scripts/render_docs_diagrams.sh`.

F:
- Concrete theorem work still remains for MDL/CR, p2/natural convergence,
  empirical adequacy, chemistry, GR/QFT consumers, ITIR consumers, origin
  receipts, and the cancellation-pressure seam.
- This board reduces coordination gap only.

## Parallel Worker Lanes

| Lane | Owner label | Current blocker | Primary files | Success condition | Validation |
|---|---|---|---|---|---|
| `W0` | Orchestrator / integrator | Keep workers disjoint and docs synchronized. | `Docs/WorkerCoordinationBoard.md`, `Docs/WorkerCoordinationMap.puml`, `README.md`, `TODO.md`, `CHANGELOG.md` | Board and diagrams route every active blocker to a lane without claiming closure. | `./scripts/render_docs_diagrams.sh`, `git diff --check` |
| `W1` | MDL/CR carrier worker | Continuum/MDL seam still needs a noncanonical CR-flat target or aligned carrier/channel. | `DASHI/Physics/Closure/CanonicalToNoncanonicalMdl*.agda`, `DASHI/Physics/Closure/P0BlockadeProofObligations.agda`, `Docs/ContinuumLimit.md` | A concrete aligned-carrier or CR-flat-target candidate is named, or a sharper obstruction is proved. | Targeted Agda on touched modules; widen only if imports require it. |
| `W2` | Natural/p2/convergence worker | Natural law and conserved-quantity lanes lack a positive p2 bridge or stronger obstruction plus convergence-rate theorem. | `DASHI/Physics/Closure/CanonicalScheduleIndependentNatural*.agda`, `DASHI/Physics/Closure/CanonicalDynamicsLawTheorem.agda`, `Docs/NaturalDynamicsLaw.md` | Either `P2Bridge` or admissible obstruction is advanced, and the convergence-bound target is made strictly more concrete. | Targeted Agda on touched natural/dynamics modules. |
| `W3` | Empirical adequacy worker | Fixed point / certificate surfaces are not connected to empirical observables. | `DASHI/Physics/Closure/*Empirical*.agda`, `Docs/PhotonuclearEmpiricalRegistry.md`, `Docs/OriginTraceabilityLedger.md` | `obs(fixedPoint) = empirical` is either inhabited for a typed carrier or reported as a precise carrier-mismatch diagnostic. | Targeted Agda on empirical bridge modules; docs diff check. |
| `W4` | Chemistry law worker | Candidate256 witness is landed, but not promoted into a stronger chemistry-facing law. | `DASHI/Physics/Closure/ChemistryRightLimitsQuotientCrossBand*.agda`, `DASHI/Physics/Closure/AtomicChemistryRecoveryTheorem.agda`, `Docs/AtomAndWaveRecoveryStatus.md` | A symmetric, nontrivial, quotient-sensitive law consumes the witness without claiming spectra or bonding. | Targeted Agda on chemistry modules. |
| `W5` | GR/QFT consumer worker | GR/QFT has coarse/interpretable transport, but no richer downstream consumer. | `DASHI/Physics/Closure/KnownLimits*.agda`, `DASHI/Physics/Closure/*Consumer*.agda`, `Docs/AbstractGaugeMatterBundle.md` | A richer consumer surface is added or the missing upstream ingredient is isolated. | Targeted Agda on touched consumer modules. |
| `W6` | ITIR/PNF consumer worker | NGram/ITIR/PNF residual sidecars are imported, but receipt-bearing theorem consumers remain open. | `DASHI/Interop/*.agda`, `Ontology/Hecke/PNFResidualBridge.agda`, `Docs/ITIRPNFResidualLogicBridge.md`, `Docs/ClaimComparisonEngine.md` | A receipt-bearing consumer target is named, or a minimal receipt fixture/interface is added without assigning labels by inspection. | Targeted Agda on interop modules; docs diff check. |
| `W7` | Claim-governance worker | Higher-structure, cross-scale, neurochemical, temporal, spacetime, and market readings are guarded but not theorem lanes. | `Docs/AttractorOrbitClassifier.md`, `Docs/ClaimComparisonEngine.md`, `DASHI/Physics/Closure/TemporalSheafProofObligations.agda` | Guardrails stay synchronized with any new chart language; no hypothesis is promoted without typed carriers and validation. | Targeted Agda if proof-obligation files change; `git diff --check`. |
| `W8` | Origin receipt worker | Minimal-credible closure path lacks a co-located origin receipt. | `DASHI/Physics/Closure/P0BlockadeProofObligations.agda`, `Docs/OriginTraceabilityLedger.md`, `Docs/PhysicsRecoveryLedger.md` | A receipt names carrier, map, signature owner, dynamics witness, empirical status, and CRT/J scalar bridge without strengthening closure. | Targeted Agda if receipt module changes; docs diff check. |
| `W9` | Cancellation-pressure seam worker | The cancellation-side `DeltaToQuadraticBridgeTheorem` seam remains witness-gated. | `DASHI/Physics/Closure/DeltaToQuadraticBridgeTheorem.agda`, `DASHI/Arithmetic/WeightedValuationEnergy.agda`, adjacent cancellation/transport modules | Either discharge `CancellationPressureCompatibility theorem dim≡15` against the tracked-profile transport, or weaken/replace that transport theorem explicitly. | Targeted Agda on `DeltaToQuadraticBridgeTheorem.agda` and touched arithmetic/transport modules. |

## Assignment Contract

Each worker prompt should include:

- Lane ID and owner label.
- Exact read/write file surface.
- One success condition from the table.
- One validation command or a reason validation is docs-only.
- Required return summary:
  `FORMAL MODEL: O, R, C, S, L, P, G, F`.

Workers must not:

- Recolor a blocker green by commentary.
- Add semantic labels from human inspection where a receipt is required.
- Run heavy aggregate validation as an inner-loop check.
- Modify files outside the assigned lane without re-coordination.

## Completion Gate

The coordination layer is complete when:

- every red/yellow blocker in the main diagrams has a lane owner;
- every active TODO blocker that is not visible in a main diagram has a lane
  owner or an explicit parked status;
- every lane has a file surface, success condition, and validation rule;
- diagrams render cleanly;
- README/TODO/changelog mention the coordination surface.
