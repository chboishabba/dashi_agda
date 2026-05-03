## Start Here

This repo is a formal-and-bridge workspace around the DASHI program.
For a new serious reader, the important split is:

- `proved`: the canonical Agda theorem spine and the specific closure claims it currently discharges
- `bridge`: documents and modules that connect the formal spine to physics-facing interpretations without claiming full derivation
- `packaging`: summary surfaces that assemble current lanes without strengthening theorems
- `empirical`: data-facing and measurement-facing surfaces that stay explicitly non-claiming
- `speculative`: roadmap or intuition surfaces that are not current repo claims

Use one of these reader tracks first:

- Repo track: `Docs/RepoGuide.md`
- Physics/unification track: `Docs/PhysicsGuide.md`
- Short unification claim surface: `Docs/UnificationClaim.md`
- Origin traceability ledger: `Docs/OriginTraceabilityLedger.md`
- Core-spine bridge surface: `Docs/CoreSpineBridge.md`
- Claim comparison engine: `Docs/ClaimComparisonEngine.md`
- ITIR/PNF residual bridge: `Docs/ITIRPNFResidualLogicBridge.md`
- PNF case-study boundary: `Docs/PNFCaseStudiesWatergateIran.md`
- Strong theorem owners:
  `DASHI/Physics/Closure/UnifiedPhysicsTheorem.agda`,
  `DASHI/Physics/Closure/AtomicChemistryRecoveryTheorem.agda`,
  `DASHI/Physics/Closure/PhysicsUnificationToCanonicalClosureAdapter.agda`
- Worker coordination board:
  `Docs/WorkerCoordinationBoard.md` and `Docs/WorkerCoordinationMap.puml`
- P0 blocker obligation surface:
  `DASHI/Physics/Closure/P0BlockadeProofObligations.agda`
- P0 worker-lane obligation index:
  `DASHI/Physics/Closure/P0BlockerObligationIndex.agda`
- Atom/wave secondary note: `Docs/AtomAndWaveRecoveryStatus.md`
- Recovery truth surfaces: `Docs/PhysicsRecoveryLedger.md` and `Docs/ArchiveRecoveryCrosswalk.md`
- Module and diagram entrypoint: [architecture.md](architecture.md)

What not to read first:

- do not start with `DASHI/Everything.agda`
- do not start with long status bullets below
- do not treat empirical or packaging lanes as theorem closure

## Repository Status

Archive-backed status update:

## Active Blocker Coordination

The historical closure checklist is complete and now serves as provenance. The
active blocker queue is coordinated through `Docs/WorkerCoordinationBoard.md`
and `TODO.md`, with validation policy in `Docs/AgdaValidationTargets.md` and
promotion governance in `Docs/OriginTraceabilityLedger.md`.

Current worker lanes:

- Active assignment round `2026-05-04`: `W1`=`Erdos`,
  `W2`=`Boole`, `W3`=`Tesla`, `W4`=`Poincare`. Result: `W1` produced a typed
  current-carrier MDL obstruction, `W2` produced a finite-carrier convergence
  bound, `W3` produced a narrow empirical equality plus mismatch diagnostic,
  and `W4` produced a symmetric nontrivial quotient-law advance. These are
  theorem/diagnostic advances, not full blocker closure; stronger carrier,
  metric, and empirical-promotion gaps remain as recorded in the board.
- W4 TSFV refinement: the Candidate256 quotient law now records simultaneous
  sheet-sign reversal as an involution and proves cross-band coupling
  invariance under it. This keeps the law structural and trit/lattice-native,
  not based on asymmetric provenance or temporal ordering.
- Follow-up round `2026-05-04`: `W1b` named a retargeted schedule-MDL
  replacement channel, and `W2b` added a local pointed metric/horizon rate law.
  Remaining blockers are now narrower: accept/prove the retargeted channel as
  the intended noncanonical continuum target, and provide realization-family
  metric coherence for the convergence theorem.
- Dependency-reduction round `2026-05-04`: `W1c` added a typed retarget-policy
  ingredient and acceptance surface, `W2c` added a realization-indexed
  shift-flow metric family witness, and `W8` added an origin-observation receipt
  surface. These reduce the implicit blocker surface but do not promote full
  empirical adequacy, chemistry handoff, or arbitrary-realization convergence.
- W3 mismatch diagnostic clarification: in this repo the term means a typed
  negative bridge receipt with three parts: first mismatch depth, trit-level
  mismatch kind, and the responsible `F_extract` / `F_promote` / `F_graph` /
  `F_explain` / `F_action` component. It is not mere inequality.
- Targeted dependency round `2026-05-04`: `W8b` is assigned to `Bernoulli` for
  a concrete origin-observation receipt instance or typed blocker, and `W3b`
  is assigned to `Hubble` for the B4 empirical dependency clarification. The
  retarget-policy ingredient remains governance-parked and must not be
  inhabited by worker assumption.
- Targeted dependency results: `W8b` landed
  `MinimalCredibleShiftOriginObservation`, a concrete non-promoting origin
  receipt for `minimumCredibleClosureShift` with `empiricalBlocked` and
  `missingEmpiricalAdequacyBridge`; `W3b` landed a B4 separation receipt showing
  closure/observable B4 promotion does not discharge empirical B4 validation.
- Policy-consumption round `2026-05-04`: `W1d` now accepts exactly the canonical
  retargeted schedule-MDL channel by equality in
  `CanonicalToNoncanonicalMdlRetargetPolicyDecision`; `W3c` and `W4c` are
  assigned to consume that policy in their lanes without promoting empirical or
  physical chemistry closure.
- Policy-consumption results: `W3c` consumed the W1d policy and W8b origin
  receipt, leaving typed blockers for chi2 transport, empirical B4 validation,
  full-profile universe boundary, and `empiricalBlocked`; `W4c` added
  `ChemistryPhysicalHandoffDiagnostic`, whose status is
  `missingPhysicalConsumer`.
- Remainder-narrowing round `2026-05-04`: `W3d` is assigned to chi2
  fixed-point carrier transport or typed obstruction, and `W4d` is assigned to
  a chemistry physical-consumer surface or sharper missing-ingredient
  diagnostic.
- Remainder-narrowing results: `W3d` added
  `Chi2FixedPointCarrierTransportObstruction`, naming the needed positive
  transport receipt and proving the current pool-mismatch/no-same-surface
  obstruction; `W4d` sharpened the physical-handoff blocker to
  `missingRetargetedQuotientInterpretationCarrierOrPreservationLaw`.
- Dual-discharge attempt round `2026-05-04`: `W3e` is assigned to the chi2
  same-surface / fixed-point defect-observation receipt, and `W4e` is assigned
  to the retargeted-quotient physical interpretation carrier/preservation law.
- Dual-discharge results: `W3e` inhabited the chi2 transport receipt only via a
  `carrierForgettingConstantReceiptOnly` boundary, so W3 still needs a
  non-forgetting same-surface theorem over `Chi2BoundaryCase`; `W4e` inhabited
  a boundary-only pre-physical consumer, so W4 now has
  `retargetedQuotientPrePhysicalConsumerAvailable` without spectra, bonding,
  wet-lab, or scale-setting claims.
- Blocker-tightening results: `W3f` added
  `Chi2NonForgettingSameSurfaceObstruction`, proving the current same `Nat`
  defect target cannot also distinguish primary/secondary chi2 cases; `W4f`
  added `ChemistryStrictPhysicalSemanticsBlocker`, naming the strict physical
  missing ingredients as scale-setting law, spectral observable map, bonding
  interpretation, and empirical physical validation.
- Obligation-surfacing results: `W3g` added
  `Chi2CanonicalPoolObservationCandidate`, a local nonconstant chi2-pool
  discriminator that remains non-empirical and non-promoting; `W4g` added
  `W4StrictPhysicalNextObligation`, the concrete obligation surface for the
  strict Candidate256 physical handoff.
- Local-transport/ledger results: `W3h` added
  `Chi2ToShiftPressureTransportCandidate`, mapping the three local chi2 pool
  cases to start/next/held shift-pressure points without claiming fixed-point
  empirical adequacy; `W4h` added `W4StrictPhysicalObligationLedger`, ordering
  strict Candidate256 physical work with scale-setting first.
- Local-dynamics result: `W3i` added
  `Chi2TransportDynamicsToFixedPointBridge`, composing the local chi2 transport
  with the existing two-step shift absorption to the held point while still
  refusing any empirical observation-target claim.
- Obligation-narrowing results: `W3j` added
  `W3EmpiricalTargetPromotionBridgeObligation`, the typed surface for the
  remaining empirical target/promotion work; `W4i` added
  `W4StrictPhysicalScaleSettingLaneObligation`, the first ordered strict
  physical lane.
- Surrogate-boundary results: `W3k` added
  `W3SurrogateEmpiricalTargetBoundary`, proving the W3 target/promotion record
  shape is syntactically inhabitible only with a surrogate `Nat` target; `W4j`
  added `W4SurrogateScaleSettingBoundary`, proving the scale lane is
  dimensionlessly inhabitible while physical units/calibration remain missing.
- Authority/calibration gate results: `W3l` added
  `W3AcceptedEmpiricalAuthorityGate`, separating surrogate availability from
  accepted empirical authority; `W4k` added `W4PhysicalCalibrationGate`,
  separating dimensionless surrogate scale from calibrated physical units and
  dimensional preservation.
- Gate-hardening result: `W3AcceptedEvidenceAuthorityToken` and
  `Candidate256PhysicalCalibrationAuthorityToken` now have no constructors in
  the current repo, preventing surrogate evidence or `Nat` scale reuse from
  accidentally promoting W3/W4.
- External-intake result: `W3AcceptedAuthorityExternalReceiptObligation` and
  `W4PhysicalCalibrationExternalReceiptObligation` now name the upstream
  authority/calibration receipt shapes that would be required to unlock those
  hardened gates, while recording current status as obligations-needed only.
- Remaining-lane obligation result: `GRQFTConsumerNextObligation`,
  `PNFResidualConsumerNextObligation`, and
  `CancellationPressureCompatibilityNextObligation` now name the W5, W6, and W9
  next receipts/diagnostics without promoting GR/QFT closure, ITIR/PNF runtime
  labels, or cancellation-pressure compatibility.
- Final-boundary obligation result:
  `CanonicalToNoncanonicalMdlRetargetFinalSeamObligation`,
  `NaturalP2ConvergencePromotionObligation`,
  `ClaimGovernancePromotionObligation`, and
  `OriginReceiptPromotionExternalObligation` now name the remaining W1, W2, W7,
  and W8 promotion receipts without promoting the retargeted seam, natural/p2
  dynamics, claim-governance readings, or origin empirical status.
- P0 obligation index result:
  `P0BlockerObligationIndex` now imports the current W1-W9 obligation/status
  surfaces as a single board-wide smoke target. This is a discoverability and
  validation surface only; it does not inhabit any external authority token or
  promote empirical, chemistry, GR/QFT, PNF, origin, natural, or
  cancellation-pressure closure.
- `W1`: MDL/CR aligned carrier or CR-flat target.
- `W2`: natural / `p2` bridge or obstruction plus
  `CanonicalDynamicsLawTheorem` convergence-rate dynamics.
- `W3`: `EmpiricalAdequacyBridge` or explicit carrier-mismatch diagnostic.
- `W4`: stronger chemistry-facing law from the landed witness.
- `W5`: richer GR/QFT consumer gate.
- `W6`: ITIR/PNF receipt-bearing consumer wiring.
- `W7`: claim-governance synchronization for higher-structure and cross-scale
  charts.
- `W8`: origin receipt for the minimal-credible closure path.
- `W9`: cancellation-pressure seam in `DeltaToQuadraticBridgeTheorem`.

Workers must choose one lane from the board, keep file ownership bounded, and
must not reopen completed checklist items unless an active blocker explicitly
depends on that surface.

## Diagram Surfaces

- Canonical architecture overview: [architecture.md](architecture.md)
- Origin traceability and core-spine navigation:
  `Docs/OriginTraceabilityLedger.md`, `Docs/CoreSpineBridge.md`, and
  `Docs/ClaimComparisonEngine.md`, `Docs/ITIRPNFResidualLogicBridge.md`
- Strong claim owners:
  `UnifiedPhysicsTheorem.agda`,
  `AtomicChemistryRecoveryTheorem.agda`,
  `PhysicsUnificationToCanonicalClosureAdapter.agda`
- Repo reader metasystem: `Docs/RepoMetasystem.puml` and `Docs/RepoMetasystem.svg`
- Worker coordination map: `Docs/WorkerCoordinationMap.puml` and
  `Docs/WorkerCoordinationMap.svg`
- Canonical theorem spine: `Docs/CanonicalProofSpine.puml` and `Docs/CanonicalProofSpine.svg`
- Physics/unification boundary map: `Docs/PhysicsUnificationMap.puml` and `Docs/PhysicsUnificationMap.svg`
- Physical reality roadmap: `Docs/PhysicsRealityRoadmap.puml` and `Docs/PhysicsRealityRoadmap.svg`
- Status-board convention:
  green = theorem-owned/proved,
  yellow = bridge or advanced-but-blocked,
  blue = packaging/interface,
  red/pink = empirical non-claim or open gate.
- Observable/signature round: `Docs/ObservableSignatureGaugeEntryRound.puml` and `Docs/ObservableSignatureGaugeEntryRound.svg`
- Training dynamics bridge: `Docs/TRAINING_DYNAMICS.puml` and `Docs/TRAINING_DYNAMICS.svg`
- Versioned PlantUML sources: `Docs/*.puml`
- Versioned rendered previews: `Docs/*.svg` and `Docs/*.png`
- Re-render command: `./scripts/render_docs_diagrams.sh`
- Worker routing rule:
  use `Docs/WorkerCoordinationBoard.md` before assigning parallel workers to
  red/yellow blocker boxes. Each worker should own one lane, one bounded file
  surface, one success condition, and one validation rule.
- The orbit/signature/shell-family story remains the strongest part of the
  repo and is now better supported by sibling-repo and archive material.
- The wave / psi / graded-series bridge is no longer only aspirational:
  archive material and sibling-repo scaffolding now make it a strong formal
  direction, though still not a closure theorem.
- The five-pillar closure interface exists, but currently acts as a packaging
  surface over earlier modules, not yet as the final bottleneck proof.
- Current mathematical bottleneck remains:
  prove the invariant quadratic + uniqueness-up-to-scale seams from the
  contraction/projection machinery and then derive the downstream
  signature/Clifford/gauge chain from that theorem.
- Canonical bottleneck progress this round:
  `ContractionForcesQuadraticStrong` now records explicit scale-aware
  uniqueness data (`scaleFactor`, `normalizeToScaledQ̂core`) while keeping the
  old normalized witness surface stable; it also now carries named
  `NondegeneracySeam` and `IsotropyCompatibilitySeam` records instead of
  leaving those bottleneck slots as raw `⊤` placeholders, while preserving the
  old compatibility fields for downstream consumers.  Those seam records are
  now theorem-bearing: nondegeneracy records full normalization to `Q̂core`
  and now reduces the remaining anisotropy requirement through the definitional
  bridge `Q̂core≡sumSq`, so `CoreAnisotropyAssumption` is no longer a raw
  `Q̂core` assumption but two narrower local premises on `HFZ.sumSq`
  recursion (`SquareZeroResidualPremise` and
  `SumSqZeroDecompositionPremise`), and those local premises are now discharged
  from the integer / `HFZ.sumSq` machinery already in repo, so strong
  nondegeneracy no longer depends on a residual anisotropy assumption;
  isotropy compatibility now carries explicit shell-respecting structure plus
  an inhabited action-transport package whenever a shell transport boundary
  witness is present, and the downstream signature/Clifford boundary now states
  that only normalized quadratic is actually consumed, so unconditional
  shell-orbit existence is not part of the current theorem contract; and the
  non-unit scale path now has an explicit `CoreScaleSeam` obstruction theorem
  in positive dimension, so the honest positive-dimensional non-unit story
  lives on an explicit restricted carrier (`CoreScaleCarrierSeam`) rather than
  the full core, while `AdmissibleFor` remains a whole-carrier surface whose
  positive-dimensional scale factor is forced to unit. The strong closure
  surface now also exposes `strongNondegeneracy` as the default discharged
  theorem path, so downstream code can depend on null-cone reflection without
  threading `CoreAnisotropyAssumption` manually. And
  `QuadraticToCliffordBridgeTheorem` now replaces the old uniqueness
  placeholder with an explicit generator-image uniqueness theorem on the
  factorization surface. The spin/Dirac bridge now also exposes an explicit
  `spinDiracBridgeBoundary`, confirming that the current downstream path still
  consumes only the normalized-quadratic contract and does not require a wider
  nondegeneracy surface. The core/full-closure side now says the same thing
  explicitly through `closureQuadraticBoundary`, so the canonical closure stack
  records that it is carrying bridge witnesses, not consuming null-cone
  reflection.
- Local merge-prep tooling status:
  the repo now treats a Nix/zkperf surface as acceptable only if it preserves
  the existing authoritative CI route through `DASHI/Everything.agda` and also
  adds an explicit recursive smoke surface for merge-relevant nested modules.
  Demo DA51/zkperf JSONL witness files are acceptable as illustrative tracked
  artifacts for now, but they must be documented as non-authoritative sample
  outputs rather than as canonical reproducibility inputs.
- Layer-2 separator search now has an explicit target surface:
  `Ontology.Hecke.ProfileSummaryFamilySeparation`
  packages the honest split between
  `CurrentProfileSummarySeparates`
  and
  `CurrentProfileSummaryCollapses`,
  and
  `Ontology.Hecke.CurrentSaturatedProfileSummaryFamilySeparation`
  gives the current saturated-branch specialization of the same question,
  while
  `scripts/profile_summary_separation.py`
  is the Python mirror that searches the current generator taxonomy for a
  separating pair under the full `profileSummaryFamily` invariant, and
  `scripts/profile_summary_adapter.py`
  is now a precomputed-artifact-first seam over
  `artifacts/hecke/profile_summary_family.json`; the remaining gap is the
  missing materialized data, not missing Python shape. A schema example lives
  at `artifacts/hecke/profile_summary_family.example.json`.
  That gap is now closed locally by
  `scripts/materialize_profile_summary_family.hs`, which materializes the JSON
  artifact directly from the compiled MAlonzo bridge
  `GeneratorCollapseClass -> primeImage -> profileSummaryFamily`.
  On the current nine-generator taxonomy, the full family already separates,
  and on the saturated-only slice it also separates. The current materialized
  families cluster into five classes overall and four classes on the saturated
  branch. `scripts/minimize_profile_summary_projection.py` now shows that
  `forcedStableCount`, `totalDrift`, and `contractiveCount` each preserve the
  same current partition as the full six-field family on both scopes.
  `Ontology.Hecke.ContractiveCountLayer2Invariant`
  now promotes `contractiveCount` as the theorem-facing current Layer-2
  singleton surface, and
  `Ontology.Hecke.CurrentSaturatedContractiveCountLayer2Invariant`
  gives the same specialization on the current saturated branch.
- Closure contract status now lives in `Docs/ClosureContractStatus.md`:
  the strong layer carries discharged nondegeneracy, but the current
  signature -> Clifford -> spin/Dirac -> full-closure chain still factors only
  through the normalized-quadratic boundary.
- Routine Agda target policy now lives in `Docs/AgdaValidationTargets.md`:
  use focused canonical bridge modules in normal edit loops, treat
  `PhysicsClosureValidationSummary.agda` as heavy/avoid-by-default, and treat
  `Everything.agda` as an occasional bounded checkpoint rather than a routine
  inner-loop command.
- Representation-language clarification:
  `Docs/ColourInDashi.md` now fixes the repo-facing split between optical
  colour, perceptual colour, and QCD colour, and states the safe Dashi claim
  boundary: colour is a projection-stable observable on a structured latent
  signal, not a primitive property.
- Internal-symmetry clarification:
  `Docs/TriadicCarrierToSU3.md` now fixes the safe bridge from a triadic
  3-sector carrier to an `SU(3)`-like internal symmetry claim. Ternary
  counting alone is not enough; the lift requires conserved Hermitian norm,
  determinant-one admissible mixing, and an observable quotient.
- MDL toy clarification:
  `Docs/MusicalSymmetryMDL.md` now states the stronger basin target explicitly:
  replace direct symmetry reward with a compression/MDL proxy and ask whether
  symmetric attractor classes still dominate.
- Antifascistic / three-body / music boundary:
  `Docs/AntifascisticBoundaryAndMusic.md` records the safe split between
  invertible entropy-preserving dynamics, three-body carrier-vs-observable
  predictability, and the maintained music MDL toy. It also fixes the safe
  pitch-class bridge as `Z/12Z ~= Z/3Z x Z/4Z`, not a perfect-fifth `Z3` orbit.
- Musical attractor target:
  `Docs/MusicalAttractorTheorem.md` now names the precise exploratory bridge:
  carrier `(Z/12Z)^n`, summed chromatic metric, nearest-scale `K_music`,
  Lyapunov level `L_music`, one-step descent to `S^n`, and explicit quotient
  boundaries separating CRT `p mod 3`, tonal clustering, and the order-12
  perfect-fifth map.
- Canonical closure routing now includes an explicit
  `ContractionForcesQuadraticStrong -> QuadraticToCliffordBridgeTheorem`
  step that builds a canonical bilinear-form interface from normalized
  quadratic data before spin/Dirac layers.
- Interop/text-pressure sidecars:
  `DASHI/Combinatorics/NGram.agda` and
  `DASHI/Interop/ITIRJoinBridge.agda` exist locally and are aggregate-imported
  by `DASHI/Everything.agda`.
  `NGram` is a fixed-width ternary-window surface, not text semantics;
  `ITIRJoinBridge` is a conservative UFTC severity/code to DASHI pressure
  adapter, not a live ITIR runtime or production join-edge classifier.
  `DASHI/Interop/SensibLawResidualLattice.agda` adds the four-level
  `ResidualLevel` join-semilattice, signature-fibred PNF comparison gates,
  wrapper filtering, `PredicateIndexSurface`, a six-level residual refinement,
  and a minimal `PredicatePNF` carrier shape;
  `DASHI/Algebra/TetralemmaBridge.agda` and
  `DASHI/Algebra/SixfoldLogic.agda` connect the residual/tetralemma/sixfold
  carriers to `LogicTlurey` and `Base369.HexTruth` without treating parser
  output as semantic authority. The tetralemma bridge also records the
  `TriTruth -> ResidualLevel` embedding and proves that `contradiction` is not
  in the tone image.
  `Ontology/Hecke/PNFResidualBridge.agda` adds the Hecke-side PNF fibre
  adapter: quotient projection equality is a candidate-pool fibre, stable /
  illegal / other defects map to `partial` / `contradiction` / `noTypedMeet`,
  and illegal defects preserve critical pressure under residual joins.
  `WrapperState` now includes `performativeEvidence`, which maps to
  `scopeExceeded6` when emitted by the pipeline; `PNFEmissionReceipt` records
  parser profile, reducer profile, source span, and emitted atom so residual
  comparison is receipt-driven rather than hand-labelled.
  `Docs/PNFCaseStudiesWatergateIran.md` records Watergate/Iran as conditional
  fixtures for this wrapper gate, not as manually labelled examples; it also
  treats formula posts and attribution-by-response interview exchanges as
  conditional trace fixtures that require emitted receipts. Formula posts can
  be tested as operator-level sufficient-statistic fixtures only after a
  formula-reader receipt emits that structure; they are not proof certificates
  for market periods, actor classifications, or `AntiFascistSystem` instances
  without separate model witnesses. The docs also now record
  domain-incommensurability as an open design fixture: a failed economic-cost
  to decision-domain measure bridge must be emitted or certified before the
  repo can classify a comparison as incommensurable.
  `Docs/ClaimComparisonEngine.md` is the normalized reader surface for the
  whole path from runtime receipt emission to residual joins, pressure,
  tetralemma/sixfold carriers, and the Hecke adapter.
  `Docs/AttractorOrbitClassifier.md` is the downstream design surface for
  using receipted residual/domain/formula/Hecke features as an
  attractor-orbit hypothesis generator; it is explicitly not a trading bot,
  market predictor, or hidden-cause attribution engine without separate
  empirical and causal validation. State-level political labels are likewise
  kept outside the operator-class trace unless a separate taxonomy, receipt
  corpus, scope rule, and validation standard are supplied.
  Aggressor/responsibility labels likewise require a shared-fibre or
  cross-fibre responsibility taxonomy, cost/threat/response receipts,
  third-party burden provenance where relevant, and external validation.
  Existential-domain and operator-completeness labels likewise require
  physical-survival witness receipts, provenance, temporal/wrapper/modality
  fields, an optional warrant-ordering rule, and a typed multi-domain
  interaction operator before economic/theological/existential fibres can be
  compared or composed.
  Enemy-classification operator labels likewise require textual/source-span
  receipts, interpretive-profile metadata, a classifier-input taxonomy, and
  inverse/deactivation semantics before the repo can compare lineage-fixed or
  behaviour-conditional classifiers against operator-duality surfaces.
  Collapsed-quotient labels likewise remain inside the residual formalism:
  one-element or coarser quotient lattices can be well-formed, but
  `noTypedMeet`, product-lattice, and lift/redifferentiation claims require
  explicit quotient maps, lost-distinction records, receipts, and validation.
  Protected-identity/conduct-axis and three-body lattice labels likewise
  require role-binding taxonomies, product-lattice maps, decision-projection
  rules, decoupling semantics where claimed, source receipts, and validation.
  Hostile-provenance and four-body theology labels likewise require
  source-critical receipts, adversarial/indirect witness qualifiers,
  orientation maps, product-lattice definitions, operator witnesses, and
  validation; `Ultrametric.agda` exists, but no theological-lattice metric is
  currently supplied.
  Non-Abrahamic and N-body comparative-lattice labels likewise require
  school-level source receipts, interpretive profiles, carrier definitions for
  identity-map, permanent-distance, telos-free action, process, or
  perspective-indexed fixtures, typed translations into or away from PNF, and
  validation before the repo can classify named traditions or doctrines.
  East Asian and Indigenous living-lattice labels likewise require culturally
  governed public receipts, place/community provenance where applicable,
  restricted-knowledge flags, topology-changing carrier definitions for
  substrate, natural-flow, relation-matrix, immanent-node, fully connected,
  derivation-graph, or timeless-bundle fixtures, typed morphisms, and
  validation before the repo can compare them with DASHI carriers, graphs,
  bundles, scan orders, metrics, or fixed points.
  Affective-state and feelings-wheel labels likewise require a named emotion
  taxonomy, source or subject/session receipts, psychometric or clinical
  validation status, contemplative-source profiles where relevant, typed
  feeling-tone, naming, perspective, and wrapper carriers, and explicit
  clinical non-authority flags before the repo can compare them with Base369,
  Whakapapa, DharmaSystem, Amalek-collapse, trauma-healing, Dreaming, or
  JFixedPoint fixtures.
  Mathematical-atlas and higher-structure labels likewise require typed chart
  interfaces before the repo can promote category-theory, Jain-topos, HoTT,
  ergodic, information-geometric, coinductive/non-well-founded, tropical,
  renormalization, or infinity-categorical analogies into theorem claims.
  Required gates include chart carriers, morphisms from existing
  PNF/residual/operator surfaces, preservation laws, and validation; the repo
  does not currently prove a DASHI infinity-topos, a Jain subobject
  classifier, a checked Amalek adjunction, a HoTT path-space reading of
  Whakapapa/Dreaming, an ergodic Songline/scan-order theorem, a Fisher/MDL PNF
  projection, a tropical degeneration, an RG relevance law, or `JFixedPoint` as
  a terminal object.
  Cross-scale physics, biology, neuroscience, affective, theological, and
  consciousness labels likewise require typed scale carriers, explicit scale
  maps, observable-preservation laws, measurement protocols, empirical
  validation, and clinical non-authority flags where health-related claims are
  involved. The repo does not currently prove that quantum superposition is
  pre-vedana, measurement is vedana, projectors are Amalek, unitaries are
  AntiFascistSystem, RG relevance governs enemy classifiers, Landauer erasure
  proves cultural-memory destruction, phase transitions instantiate live
  conflict triggers, `CRTPeriod` is correlation length, DNA eigenclasses are
  literal DASHI biology, epigenetics is a Dreaming layer, predictive brain
  networks are DASHI operator modules, polyvagal states are Base369, IIT Phi is
  JFixedPoint, or the full chain is reality's self-description.
  Neurochemical and body-brain-chemistry labels require the same discipline:
  typed synaptic/electrical, volume-transmission, endocrine/hormonal, and
  epigenetic or cultural propagation carriers; receptor/context models;
  biomarker measurement protocols; causal hypotheses; biomedical validation;
  and clinical non-authority flags before GABA, glutamate, dopamine,
  serotonin, norepinephrine, oxytocin, cortisol, insulin, or acetylcholine can
  be compared to DASHI operator classes, Base369, Dreaming, Whakapapa,
  Amalek-collapse, market behavior, or therapeutic claims.
  Market self-observation and trader-operator labels likewise require typed
  trader-state receipts, market-data receipts, cross-scale maps, execution
  rules, risk controls, cost models, compliance review, and out-of-sample
  validation before the repo can promote trading psychology, RG-stack,
  three-conjunct signal, MDL-compression, or `JFixedPoint trade` language into
  any market signal or investment recommendation.
  Temporal-sheaf labels likewise require typed Time, Interval, Property,
  Value, Section, and Global carriers; overlap/restriction/gluing laws;
  exclusive-property single-valued fibre semantics; pre/post transition
  sheaves; a proof that a claimed `JFixedPoint` / `+1` transition is not just
  ordinary `CRTPeriod` recurrence; and a temporal section metric before
  temporal qualifiers can be promoted from flat metadata into a dimension of
  the state space. The minimal Agda obligation surface for this is
  `DASHI.Physics.Closure.TemporalSheafProofObligations`; it is not a discharged
  temporal semantics theorem.
  Spacetime-sheaf labels likewise require a typed Space / mereological carrier,
  containment and spatial-overlap laws, sections over `(Time, Space)`,
  spacetime gluing, exclusive-property single-valuedness at each coordinate,
  Cauchy-style slice/delta/admissibility carriers, evolution validity
  preservation, and pre/post extension-obstruction witnesses before the repo
  can promote spacetime, 3+1, Cauchy-surface, spacetime-density-matrix, or
  `JFixedPoint`-as-singularity readings. The current Agda surface only records
  those proof obligations.
  Base369-chain interpretations likewise require typed carrier maps,
  quotient/seam or commutation proofs, operator witnesses, and validation
  before the repo can promote cyclic carriers into actor-count semantics,
  Theta operators, strategy windows, resolution conditions, or global
  attractor claims.
  Pairwise interaction claims likewise require a product carrier, directed
  receipts, a coupling/composition law, and a joint attractor theorem before
  the repo can claim convergence, non-convergence, or terminal dominance.
  Conditional-trigger claims require emitted trigger receipts, modality and
  qualifier rules, deactivation semantics, a latent fixed-point witness, and a
  convergence theorem before a terminal-looking trace can be reclassified as
  conditional convergence.
  Bot/source join-domain claims require a typed observation map from operators
  to receipt streams, an orbit-input bijectivity or canonical-representative
  theorem, and empirical/causal validation; current Hecke, CRT, and
  J-fixed-point bridge surfaces do not by themselves provide that.
  Global phase/bifurcation claims require a global carrier, basin metric,
  perturbation threshold, typed epistemic interaction operator, and validation
  standard before the repo can claim a dominant attractor shift or basin exit.
  The remaining promotion work is consumer wiring, not inventing those
  surfaces from zero.
- Active closure seam tightening:
  keep the canonical bridge interface fixed while replacing the internal
  signature source with a causal-classification theorem on the normalized
  quadratic (`Q̂core`) under cone/arrow/isotropy/finite-speed/nondegeneracy
  assumptions.
- Archive coverage update:
  `Docs/PhysicsArchiveCoverageMap.md` now records the current high-signal
  local-DB support threads for the physics-closure spine. The current repo
  reading is:
  `Physics Closure in DASHI`,
  `Branch · Cone monotonicity analysis`,
  and `Branch · Snap Filtering Analysis`
  are direct formal support lanes, while
  `Branch · Topology and MDA/MDL`
  and the light-transport / phase-sync thread remain support lanes for
  continuum and physical-realization work.
- Photonuclear empirical lane visibility:
  `DASHI/Physics/Closure/PhotonuclearEmpiricalConstantsRegistry.agda`,
  `DASHI/Physics/Closure/PhotonuclearEmpiricalMeasurementSurface.agda`,
  `DASHI/Physics/Closure/PhotonuclearEmpiricalEvidenceSummary.agda`, and
  `DASHI/Physics/Closure/PhotonuclearEmpiricalValidationSummary.agda` now
  provide the empirical-first owner stack, with
  `Docs/PhotonuclearEmpiricalRegistry.md` as the canonical map. This lane is
  explicitly empirical-only and non-claiming.
- Unifying interface lane:
  `DASHI/Physics/DashiDynamics.agda`
  is now the theorem-thin entry surface that binds the current packaged
  carriers together without claiming derivation between them. Its intended
  reading is:
  state/path/observable/scalar interfaces +
  action/density/amplitude/reduction law slots +
  photonuclear empirical validation carrier +
  held/control pressure consumer +
  explicit non-claim boundary.
  It is a packaging interface, not a new physics theorem.
  `DASHI/Physics/DashiDynamicsShiftInstance.agda`
  is the first minimal inhabitant of that interface over an existing
  repo-native carrier: the shift pressure-point surface plus the packaged
  photonuclear validation summary.
  That instance now owns the first non-placeholder core law surface:
  density is empirical `densityProxy + pressure rank`,
  action/amplitude are pressure-rank proxies on equality paths,
  the exported density law is monotonic under the bounded three-point
  pressure-advance endomap,
  and the action law now also carries a bounded least-action witness:
  among admissible monotone pressure targets on the three-point carrier,
  `shiftPressureAdvance` chooses the smallest available pressure step.
- Variational bridge lane:
  `DASHI/Physics/PressureHamiltonJacobiGap.agda`
  is now the theorem-thin least-action / Hamilton-Jacobi-facing consumer
  over `DashiDynamics`.
  Its intended reading is:
  variational state +
  admissible targets +
  transition cost +
  value function +
  local optimality +
  Bellman / Hamilton-Jacobi presentation,
  all with explicit non-claim boundaries.
  `DASHI/Physics/PressureHamiltonJacobiShiftInstance.agda`
  is the first bounded inhabitant of that lane over the three-point shift
  pressure carrier.
  It reuses the existing least-action witness from
  `DashiDynamicsShiftInstance`
  and adds one discrete Bellman-style inequality witness, without claiming a
  continuous-limit PDE or a Schrödinger derivation.
- Gradient-flow seam:
  `DASHI/Physics/PressureGradientFlowGap.agda`
  is now the theorem-thin held-point / potential-descent consumer over
  `DashiDynamics`.
  `DASHI/Physics/PressureGradientFlowShiftInstance.agda`
  is the first bounded inhabitant of that lane over the three-point shift
  carrier.
  The core
  `DashiDynamicsShiftInstance`
  reduction side now records an explicit held-point fixed point together with
  a bounded potential-descent witness, so the repo has a local
  gradient-flow-style seam before any wider continuum or wave-lift claim.
  That seam is now sharpened one step further:
  strict descent holds on the explicit non-held slice of the three-point
  carrier, so the current core package now exposes the minimal Lyapunov-style
  strengthening that was previously missing, still without claiming a global
  convergence theorem.
  The next bounded tightening is now landed too:
  `DashiDynamicsShiftInstance`
  carries a constructive convergence theorem to the held point on the
  three-point carrier, together with an explicit `≤ 2` step bound.
  That finite terminality story is now packaged explicitly at
  `DASHI/Physics/PressureGradientFlowTerminalityGap.agda`
  and
  `DASHI/Physics/PressureGradientFlowTerminalityShiftInstance.agda`,
  so the shift lane now records eventual held-entry, bounded convergence,
  unique fixed point, and unique zero-potential point on the current carrier
  without pretending this is already a general attractor theorem.
  Separately,
  `DASHI/Physics/ShiftPotentialQuadraticEnergy.agda`
  packages the finite scalar quadratic energy induced by
  `shiftHeldPotential`
  and proves monotone descent of
  `Q(s) = shiftHeldPotential(s)^2`
  under the same pressure advance map, while staying explicitly short of the
  full canonical quadratic-form lane.
  The next handoff is now explicit too:
  `DASHI/Physics/ShiftPotentialQuadraticBridge.agda`
  packages that same finite energy surface as a local
  `ContractionQuadraticBridge.QuadraticOutput`-compatible object, so the
  pressure lane now has a real bridge into the repo's quadratic interface
  layer without claiming it has reconstructed the canonical contraction =>
  quadratic theorem path.
  The bilinear-facing seam is now bounded too:
  `DASHI/Physics/ShiftPotentialBilinearBridge.agda`
  exposes one explicit symmetric pair form on the finite shift carrier whose
  diagonal matches the pressure-induced quadratic energy exactly.
  This is recorded as a local bilinear-style handoff, not as a full
  polarization theorem or vector-space upgrade.
  That local bilinear seam is now related to the existing Clifford-gate metric
  interface too:
  `DASHI/Physics/ShiftPotentialCliffordMetric.agda`
  packages the same finite bilinear form as a
  `DASHI.Geometry.CliffordGate.BilinearForm`
  together with an explicit `RingLike ℤ` carrier and an exact diagonal
  recovery theorem, still without constructing a Clifford algebra.
- Schrödinger-facing packaging constraint:
  the recovered tail of
  `Classical Quantum Bridge`
  (`69eb5a54-5f74-839f-96d4-0009db829915`,
  canonical `d69ca38ba7051141efc5c7245437fe574b6a5057`)
  should be implemented, if at all, as theorem-thin or assumption-guarded
  consumers over `DashiDynamics`, not as a fake proof surface.
  The intended order is:
  `SchrodingerGap`
  then
  `SchrodingerAssumedTheorem`,
  with any demo-only mock module treated as plumbing-only and non-citable.
  That bounded packaging round is now landed:
  `DASHI/Physics/SchrodingerGap.agda`
  is the theorem-thin Schrödinger-facing consumer over `DashiDynamics`, and
  `DASHI/Physics/SchrodingerAssumedTheorem.agda`
  is the assumption-guarded theorem seam that only repackages a supplied
  `schrodingerForm` witness from the gap surface.
  The first concrete inhabitant is now also landed:
  `DASHI/Physics/SchrodingerGapShiftInstance.agda`
  defines a bounded pressure-ordered endomap on the existing three-point
  shift carrier, ties density to the empirical `densityProxy` plus pressure
  rank by reusing the core `DashiDynamicsShiftInstance` helpers, proves
  monotonicity for density and amplitude proxies, and constructs one
  assumption-guarded theorem instance from that real witness.
  A second, more structured inhabitant is now landed too:
  `DASHI/Physics/SchrodingerGapPhaseWaveShiftInstance.agda`
  lifts `WaveState` from the raw pressure point to a record carrying
  carrier point,
  amplitude,
  and phase proxy.
  Its Schrödinger-form witness now packages density monotonicity,
  amplitude monotonicity,
  phase descent,
  and one bounded interference / phase-transport law:
  exact conservation of `amplitude + phase` on the current carrier.
  The finite continuum-style follow-on now also exists at
  `DASHI/Physics/ShiftPhaseWaveContinuumStory.agda`,
  where the structured wave carrier is packaged with a bounded transport
  coordinate, a conserved interference charge, and an exact
  coordinate/phase balance law, all still explicitly below any PDE or
  scaling-limit claim.
  The next finite wave-facing layer is now landed too:
  `DASHI/Physics/ShiftPhaseTableInterference.agda`
  adds a four-class finite phase table with a symmetric interaction kernel
  and bounded pair-state interference intensity observable,
  while
  `DASHI/Physics/ShiftDiscreteWaveStep.agda`
  packages the same structured carrier as an integer-pair discrete wave with
  finite phase encoding, superposition by vector addition, and one
  Schrödinger-like Euler step under a scalar Hamiltonian proxy.
  That finite wave package now has its next theorem-thin follow-on layers too:
  `DASHI/Physics/ShiftWaveScalingInterface.agda`
  introduces an explicit coarse/fine refinement surface with step
  compatibility and a discrete second-difference operator, but still no limit
  or PDE claim;
  `DASHI/Physics/ShiftWaveRefinementSeam.agda`
  now enriches that refinement story with coarse/fine observation records,
  explicit `project` / `embed` maps, and transport/agreement witnesses over
  the same carrier without claiming any actual limit theorem;
  `DASHI/Physics/ShiftWaveRefinementHierarchy.agda`
  now replaces the old same-carrier-only weak point with a genuine finite
  `3 -> 5` hierarchy whose coarse points embed at interior refined points and
  whose refined Laplacian agrees with the coarse Laplacian on embedded points
  under the current projection-based field lift;
  `DASHI/Physics/ShiftWaveRefinementLevel.agda`
  now packages that concrete hierarchy as a reusable theorem-thin family
  surface with named coarse/fine levels, a lift, and explicit refinement
  boundary text so later `5 -> 9` or `9 -> 17` steps can reuse the same
  interface without pretending a recursive family theorem;
  `DASHI/Physics/ShiftWaveGlobalUpdate.agda`
  now packages the current Euler-style Schrödinger step as a synchronous
  whole-field one-pass update on both the coarse and refined carriers, with
  compatibility on lifted coarse fields at embedded coarse points, but still
  no unitarity, stability, or PDE claim;
  `DASHI/Physics/ShiftSpatialLaplacian.agda`
  adds the finite three-point spatial Laplacian with reflected endpoint
  behavior;
  `DASHI/Physics/ShiftDiscreteHelmholtzSurface.agda`
  now packages the corresponding coarse/refined discrete Helmholtz residuals
  and the modewise Schrödinger-step law
  `ψ ↦ ψ + i λ ψ`
  for finite eigenfields, still with no spectral or PDE claim;
  `DASHI/Physics/ShiftDiscreteWaveEnergy.agda`
  now makes the Euler-style step boundary explicit as a finite energy package:
  held-state basis waves are preserved, while non-held basis waves expose
  concrete growth witnesses instead of a fake stability theorem;
  `DASHI/Physics/ShiftWaveEnergyHierarchy.agda`
  now lifts that story across the concrete `3 -> 5` hierarchy with exact
  coarse/fine field-energy surfaces, an exact lifted-field energy shape
  theorem, and embedded-window Laplacian-energy control under the current
  projection lift, while explicitly refusing stronger whole-five-point or
  scaling-limit claims;
  `DASHI/Physics/ShiftDiscreteContinuityCurrent.agda`
  now packages the current finite continuity/current story as an explicit
  bookkeeping surface: field-local energy, updated energy, Laplacian-stencil
  current magnitude, pairwise phase/interference currents, and exact
  conservation of `amplitude + phase` under one finite advance step, with no
  PDE continuity or Noether overclaim;
  `DASHI/Physics/ShiftDiscreteActionPrinciple.agda`
  now packages a theorem-thin finite action surface over the same field:
  local action density is defined exactly as local energy plus local current
  magnitude, and the update law is pinned directly to the existing
  Euler-style Schrödinger step without claiming a variational derivation;
  `DASHI/Physics/ShiftFiniteEvolutionWitness.agda`
  now adds a Dashi-style finite witness/search layer with bounded
  PNF-style evolution obligations, explicit Skolem-style one-pass update
  witnesses, and finite Herbrand-style candidate histories on both the coarse
  and refined carriers;
  `DASHI/Physics/ShiftFinitePathSum.agda`
  now adds a bounded exact two-history path-sum surface over the existing
  phase-table and discrete-wave weights, still explicitly below any continuum
  path integral or analytic propagator claim;
  `DASHI/Physics/ShiftFieldTheoryConsistency.agda`
  now ties the current coarse witness, updated-energy view, action/current
  bookkeeping, and bounded path-sum together as one exact theorem-thin
  coherence package over the same deterministic one-pass advance, without any
  path-selection, dominance, Noether, or continuum overclaim;
  `DASHI/Physics/ShiftFiniteGaugeSymmetry.agda`
  now packages the first finite local `C4`/`U(1)`-like phase-symmetry
  surface over the integer-pair wave lane, keeping generic compose/inverse/
  additive/scale equalities as explicit target-law surfaces rather than fake
  closed proofs;
  `DASHI/Physics/ShiftFiniteGaugeCoupling.agda`
  now adds the first finite matter-plus-static-gauge lift over the current
  coarse carrier with a bounded covariant Laplacian, Hamiltonian, and
  one-pass update surface, together with explicit vacuum compatibility and
  bounded gauge-covariance targets, still below any full local-covariance,
  dynamic-gauge, or continuum claim;
  `DASHI/Physics/ShiftGaugeFieldTheoryAgreement.agda`
  now closes the next honest vacuum-gauge slice by tying the existing
  field-theory coherence package, the hierarchy-energy package, and the new
  finite gauge-coupling package to the same coarse one-pass update and its
  lifted energy surfaces, still without any gauge-energy conservation or full
  local-covariance overclaim;
  `DASHI/Physics/ShiftConstantPhaseCovariance.agda`
  now adds the next bounded symmetry tightening on top of that slice:
  exact global `C4` constant-phase covariance is witnessed for the vacuum
  static-gauge covariant operator itself, while the corresponding full
  one-pass update covariance is kept as an explicit target surface rather
  than overclaimed as a closed theorem;
  `DASHI/Physics/ShiftGaugeCurrentConsistency.agda`
  now packages the next bounded current-sourced gauge-update coherence
  surface, reusing the existing coarse local-current magnitude pointwise on
  the coarse carrier and closing exact covariance only for the current
  intentionally neutral `currentPhase` reducer, while richer edge-current
  invariance and nontrivial current-to-phase transport remain target-law
  surfaces;
  `DASHI/Physics/ShiftFiniteMatrixSymmetry.agda`
  now repackages the current `Phase4`/`C4` quarter-turn action as a finite
  matrix-action surface over the integer-pair wave lane and adds one bounded
  first non-abelian doublet-action analogue with a concrete non-commuting
  witness, still below any `SU(2)`, Hilbert-space, or analytic claim;
  `DASHI/Physics/ShiftMinimalGaugeTheory.agda`
  now packages the first minimal matter-plus-static-gauge world over the same
  carrier, with one-pass matter evolution, exact vacuum reduction back to the
  current coarse global update, and explicit vacuum-gauge retention, still
  below any local-covariance, dynamic-gauge, or full-`U(1)` claim;
  `DASHI/Physics/ShiftTwoFieldGaugeInteraction.agda`
  now adds the first theorem-thin two-field gauge-mediated interaction
  surface over that same static-gauge lane: two matter fields evolve through
  bounded gauge-mediated nearest-neighbor coupling and a joint current-sourced
  gauge update, but the active gauge-update reducer remains the neutral
  inherited one, so the result is symmetry-safe rather than a promoted
  physically reactive gauge theory;
  and
  `DASHI/Physics/ShiftUnitaryLikeConstraint.agda`
  records the basis-level norm preservation and four-quarter-turn cycle for
  `mulI`, while explicitly refusing to overclaim unitarity for the Euler-style
  Schrödinger step.
- Sibling-repo support surfaces:
  `../dashitest` contains useful diagnostic and measurement artifacts for
  wave/interference, MDL, and regime-style language, but it is currently a
  support repo rather than a code dependency for this tree. The strongest
  cross-reference points are
  `../dashitest/dashiCORE/README.md`,
  `../dashitest/dashiCORE/docs/dashibrain_core_integration.md`,
  `../dashitest/dashifine/newtest/grayscott_krr.py`,
  `../dashitest/dashifine/newtest/triality_stack.py`,
  `../dashitest/docs/tree_diffusion_benchmark.md`,
  `../dashitest/docs/phase3_quotient_learning.md`,
  `../dashitest/docs/bad_day.md`,
  `../dashitest/trading/scripts/plot_action_entropy.py`, and
  `../dashitest/trading/scripts/plot_hysteresis_phase.py`.
  These are useful documentation-side analogues for measurement and
  interference language, not theorem evidence for the Agda closure stack.

Current theorem status:

- Stage A is complete: the orbit-profile discriminant selects Lorentz signature
  `(3,1)` in the current 4D framework.
- Arithmetic lane now records canonicalization progress: `normalizeAdd` is
  nonexpansive and lands in a canonical state, `CanonicalResidueZero`
  collapses the residue budget there, and `CancellationPressureFromCanonical`
  bounds the carry-budget pressure by the support proxy so normalized
  states satisfy the current arithmetic pressure guarantee.
- Stage B is complete for the current finite 4D realization: the
  cone/arrow/isotropy stack now drives shell enumeration through abstract
  interfaces rather than a shift-specific proof source.
- Stage C is still open: the current target is **minimal credible physics
  closure**, meaning a theorem-backed dynamics package plus an
  observable-consequence package for the same 4D framework. That package must
  distinguish what is already proved from what is only a forward prediction
  claim. The next concrete benchmark is profile rigidity across new 4D
  realizations.
- Current archive-backed Stage C priority order:
  1. derived dynamics law;
  2. realization-independent projection/delta theorem;
  3. signature forcing / execution-delta interface;
  4. continuum scaling law;
  5. physical reality bridge from wavefield / phase synchronization.
- Current `Δ -> quadratic` status is intentionally split into two lanes:
  the concrete cancellation-energy transport in
  `DASHI/Physics/Closure/DeltaToQuadraticBridgeTheorem.agda`
  now packages its witness surface repo-natively as
  `CancellationPressureCompatibility theorem dim≡15`,
  with
  `canonicalCancellationPressureCompatibility`
  as the thin concrete constructor from the current pair-pressure witness;
  that lane is still treated repo-side as an external compatibility input
  rather than an in-repo derivation from the current tracked-profile
  transport,
  and the sole remaining cancellation-side seam in that module is the
  `pressurePreserved` witness inside
  `CancellationPressureCompatibility`; the sharper forward proposal is
  a weighted valuation measurement
  layer
  `Φ(x) = (v_p(x) * sqrt(log p))_p`
  with
  `Q₊(x) = Σ_p v_p(x)^2 log p`
  as a positive diagonal surface that should feed, rather than replace,
  the existing canonical quadratic/signature stack.
  The first constructive helper surface for that lane now lives in
  `DASHI/Arithmetic/WeightedValuationEnergy.agda`.
  The bridge module now also exposes
  `WeightedValuationTransportCompatibility`
  plus
  `WeightedValuationForwardCandidate`
  so the weighted lane has a record-level admissibility/coherence package
  without identifying that lane with `Q̂core`.
  It now also exposes
  `weightedValuationForwardCandidateToDeltaBridge`
  and
  `weightedValuationForwardCandidateNormalizesQuadratic`,
  so a weighted forward candidate can be promoted into the theorem-side delta
  bridge once a signature bridge is supplied, without adding any new
  arithmetic-side identification claim.
  The weaker profile-side seam now also has its own arithmetic owner:
  `DASHI/Arithmetic/ArithmeticPrimeProfileBridge.agda`
  exposes
  `EmbeddedPrimeProfileMeasurement`,
  while
  `DASHI/Physics/Closure/DeltaToQuadraticBridgeTheorem.agda`
  carries
  `EmbeddedProfileScoreCompatibility`
  only as the explicit
  `deltaSum -> embeddedProfileScore`
  compatibility lane.
  The same module now also exposes
  `DeltaQuadraticSignatureCliffordPackage`
  so an already-packaged delta bridge can carry its normalized quadratic,
  inherited signature-31 data,
  and a specialized Clifford presentation handle
  without widening the cancellation-side claim.
  `DASHI/Physics/Closure/CancellationPressureCompatibilityNextObligation.agda`
  now names the exact next W9 routes: either supply the existing-route
  `pressureWitness`, or supply the weighted replacement route with
  cancellation-to-weighted-quadratic identification. It does not inhabit
  `CancellationPressureCompatibility`.
- Generic pressure algebra owner:
  `DASHI/Pressure.agda`
  now exposes a finite five-level pressure carrier with
  `_⊑p_`,
  `_⊔p_`,
  and the basic join-semilattice laws as a reusable algebra surface.
  This is intentionally generic and separate from the existing
  `Ontology/Hecke/*Pressure*`
  modules, which remain domain-specific consumers rather than the owner of the
  reusable pressure chain.
  The first thin consumer bridge now lives in
  `Ontology/Hecke/PressureAdapter.agda`,
  embedding the current three-tier Hecke `PressureClass`
  into the generic pressure carrier and proving that the existing Hecke order
  maps monotonically into `_⊑p_`.
  The first concrete reuse site is now the Hecke representative-computation
  layer:
  `Ontology/Hecke/StaysOneMoreStepRepresentativeComputations.agda`,
  `Ontology/Hecke/ExitToAnchoredRepresentativeComputations.agda`, and
  `Ontology/Hecke/ImmediateExitRepresentativeComputations.agda`
  each now expose both the domain-local `PressureClass` tier and the embedded
  generic `DASHI.Pressure.Pressure` tier on the same computation record.
  `Ontology/Hecke/RepresentativePressureOrder.agda`
  is the current theorem-thin comparison surface over that generic tier.
  It now also carries one pairwise join collapse
  (`stay ⊔ anchored = anchored`)
  plus the three-way envelope
  (`(stay ⊔ anchored) ⊔ immediate-exit = immediate-exit`)
  on the embedded generic carrier.
  Treat this as the stable pressure owner boundary for now:
  do not add further non-Hecke consumers unless a concrete cross-domain
  pressure comparison actually needs the generic carrier.
- The three-body test case is now scaffolded repo-side as a theorem-thin
  regime-classification surface under `DASHI/Physics/ThreeBody/`.
  The intended reading is:
  state carrier + step operator + local energy/action +
  contractive/boundary/non-contracting regime split +
  wave-facing admissible path kernel.
  It does not claim a closed-form solution or a global contraction theorem.
  The next landed layer now also separates
  local state/regime improvement
  from
  global forecast depth:
  `Delta3Body`,
  `EnergyΔ3`,
  `Action3`,
  `LocalPredictiveHorizon`,
  and `ChaosBoundary`
  live in the same namespace so the three-body lane can express
  \"better local prediction over time\" without claiming unlimited
  long-horizon predictability in chaotic regions.
  `DASHI/Physics/ThreeBody/Bridge.agda`
  is now also explicitly anchored to the same basin-facing admissibility
  surface already carried by
  `DASHI/Physics/ThreeBody/PredictiveBoundary.agda`,
  rather than introducing a second bridge-local admissibility notion.
  `DASHI/Physics/ThreeBody/TheoremSurface.agda`
  now publicly re-exports that bridge surface alongside the theorem-thin
  predictability and branching surfaces, so downstream consumers can import
  one entrypoint and still reach the basin-anchored bridge package.
  The same namespace now also carries an interference/path-family layer:
  admissible paths aggregate into regime amplitudes, regime weights, regime
  distributions, and a boundary-generated branching surface.
  This lets the repo state the intended Dashi reading of chaos more sharply:
  point prediction degrades, but structured future branch weights can still
  be modeled as action-weighted interference over regimes.

## Visual Guides

The repo now carries a small figure set for the newer three-body and zeta
analysis lanes.

Figure provenance:

- the stable repo copies live under `Docs/Images/three-body/` and
  `Docs/Images/zeta/`;
- they were imported from the delivered external artifact drop in
  `temp-DOWNLOADED/`;
- the associated external Agda sketch is
  `temp-DOWNLOADED/ThreeBodyPredictability.agda`;
- the current repo-native formalism surfaces remain the authoritative source
  for names and claim boundaries.

### Three-body predictability view

![Illustrative three-body trajectory in a projected admissibility cone](Docs/Images/three-body/threebody_projected_admissibility_cone.png)

What this figure is for:

- It visualizes the current three-body lane as a projected
  admissibility/cone picture rather than as a closed-form trajectory solver.
- The lower-left interior region is the intended analogue of a more stable,
  more locally coherent regime.
- The orange boundary curve marks the transition surface where predictive
  horizon is expected to shrink and branching becomes more relevant.
- The upper/right region is the intended non-contracting or unstable side,
  where point prediction degrades and branch-structured forecasts matter more.

Relevant formalism sources:

- [`DASHI/Physics/ThreeBody/PredictiveBoundary.agda`](DASHI/Physics/ThreeBody/PredictiveBoundary.agda)
- [`DASHI/Physics/ThreeBody/Interference.agda`](DASHI/Physics/ThreeBody/Interference.agda)
- [`DASHI/Physics/ThreeBody/BundleIntensity.agda`](DASHI/Physics/ThreeBody/BundleIntensity.agda)
- [`DASHI/Physics/ThreeBody/PredictabilityTheorem.agda`](DASHI/Physics/ThreeBody/PredictabilityTheorem.agda)
- [`temp-DOWNLOADED/ThreeBodyPredictability.agda`](temp-DOWNLOADED/ThreeBodyPredictability.agda)

Interpretation boundary:

- This is an illustrative regime map.
- It is not a proved cone theorem for Newtonian three-body dynamics.
- It is useful because it matches the current theorem-thin repo split:
  cone interior, cone boundary, local contraction, local Lyapunov surfaces,
  basin-relative predictive horizon, and boundary-generated branching.

### Goldbach formal-object lane

The refreshed `Dashi on Quantum Computing` thread landed the Goldbach lane as
analysis-side formal objects rather than as a solved number-theory claim.

Relevant formalism sources:

- [`DASHI/Analysis/GoldbachFormalObjects.agda`](DASHI/Analysis/GoldbachFormalObjects.agda)
- [`CHANGELOG.md`](CHANGELOG.md)
- [`TODO.md`](TODO.md)

What this lane is for:

- It records the program surfaces `EnergyΔ`, `GoldbachCone`,
  `GoldbachAmplitude`, `GoldbachTheoremLadder`, and `GoldbachProgramPack`.
- It now also carries concrete sample-side witnesses rather than only abstract
  constructors:
  `sampleGoldbachExistenceWitness` for `2 + 2 = 4` and
  `sampleGoldbachExistenceWitness8` for `3 + 5 = 8`.
- It keeps the intended reading explicit: Goldbach is being formalized as a
  theorem-thin analysis/program lane, not claimed as a proof of strong
  Goldbach.
- It also keeps the zeta/Riemann connection in the same analysis-only
  boundary class: useful as a program direction, but not a proof of RH.

Interpretation boundary:

- This is a formal-object lane, not a solved Goldbach theorem.
- It does not claim a proof of strong Goldbach.
- It does not claim a proof of the Riemann hypothesis.
- It is intended to make the Goldbach program surface explicit while keeping
  closure claims out of the README.

### Zeta visualization pack

#### Critical-line magnitude

![Critical line magnitude plot for log absolute zeta](Docs/Images/zeta/zeta_logabs_critical_line.png)

Reading:

- The deep troughs are zero neighborhoods for `ζ(1/2 + it)`.
- This is the cleanest first visualization of where critical-line structure
  is concentrated.

Relevant formalism sources:

- [`DASHI/Analysis/AbelZeta.agda`](DASHI/Analysis/AbelZeta.agda)
- [`DASHI/Analysis/ZetaVisualization.agda`](DASHI/Analysis/ZetaVisualization.agda)

Interpretation boundary:

- This is a visualization surface, not an RH proof surface.
- In repo terms it belongs to `Analysis`, not `Physics`.
- The current repo-native observation family now includes:
  `ZetaBoundaryContrastView` and `ZetaEtaTransferView`,
  both derived only from the Abel-summed sample surface.

#### Argument flow near the critical line

![Argument flow of zeta near the critical line](Docs/Images/zeta/zeta_argument_flow_strip.png)

Reading:

- The sharp seam near `σ = 1/2` is the main feature.
- This is the closest direct visual analogue to a phase-flow or boundary-crossing
  picture in the current Dashi language.

Relevant formalism sources:

- [`DASHI/Analysis/ZetaVisualization.agda`](DASHI/Analysis/ZetaVisualization.agda)

Interpretation boundary:

- The current repo only packages a visualization scaffold here.
- No analytic continuation, zero-density theorem, or spectral closure claim is
  encoded by this image alone.

#### Consecutive zero spacings

![Spacing of consecutive nontrivial zeta zeros](Docs/Images/zeta/zeta_zero_spacings.png)

Reading:

- The spacing sequence is irregular but visibly structured.
- This is the simplest figure for talking about local spacing regimes without
  pretending the repo already carries a canonical zero-statistics theorem.

Relevant formalism sources:

- [`DASHI/Analysis/ZetaVisualization.agda`](DASHI/Analysis/ZetaVisualization.agda)

Interpretation boundary:

- This is an exploratory spacing plot.
- It is not a GUE claim, pair-correlation theorem, or RH consequence theorem.

#### Dashi-projected zeta feature plot

![Dashi-projected zeta feature plot](Docs/Images/zeta/zeta_dashi_projected_feature_plot.png)

Reading:

- The x-axis is a phase-velocity-style feature.
- The y-axis is a zero-neighborhood-style score.
- Color is a local action-like score.
- The right-side high-phase cluster is the interesting regime in current
  Dashi language: it is the nearest analogue to a boundary/action/regime
  concentration rather than a flat cloud.

Relevant formalism sources:

- [`DASHI/Analysis/ZetaVisualization.agda`](DASHI/Analysis/ZetaVisualization.agda)
- [`DASHI/Analysis/AbelZeta.agda`](DASHI/Analysis/AbelZeta.agda)
- external source pack:
  [`temp-DOWNLOADED/zeta_visualization_pack/`](temp-DOWNLOADED/zeta_visualization_pack/)

Interpretation boundary:

- This figure is intentionally exploratory.
- It combines phase, local scoring, and zero-neighborhood heuristics.
- It is useful for regime thinking and visualization design, but it is not yet
  a canonical theorem object in the repo.
- Current validation snapshot:
  reference signed-permutation self-check = `exactMatch`,
  synthetic one-minus admissible candidate = `exactMatch`,
  Bool inversion secondary admissible candidate = `signatureOnlyMatch`,
  tail-permutation negative control = `mismatch`.
- Preferred next realization target:
  a Coxeter / Weyl-style 4D shell-orbit realization, beginning with an
  independent `B₄` shell/profile report and later promoted into the admissible
  harness only if its shell class becomes Lorentz-compatible and
  orientation/signature are justified.
- New Lorentz-neighborhood shell-side comparison:
  an independent synthetic one-minus-family candidate now matches the shift
  shell-1 and shell-2 profiles exactly and now serves as the canonical
  admissible alternate realization on the current Stage C path.
- New Lorentz-neighborhood dynamic search surface:
  a typed synthetic dynamics witness and a minimal independent-dynamics
  candidate now exist so the search for a second Lorentz-family realization
  is no longer shell-only.
- New synthetic-promotion status surface:
  the repo now records the exact blocker between the synthetic profile-aware
  candidate and admissible-harness promotion, instead of leaving that gap
  implicit.
- Synthetic promotion status is now complete on the current path:
  orientation and signature are bridged, a minimal independent-dynamics
  witness is present, and the synthetic one-minus candidate now enters the
  admissible rigidity harness.
- Stronger dynamics baseline:
  the canonical shift dynamics package now carries an explicit status object
  for propagation, causal admissibility, monotone quantity, and effective
  geometry, plus a semantics-bearing dynamics witness companion exported on
  the canonical path.
- New closure runway status surfaces:
  the canonical Stage C path now exports a concrete minimal
  constraint-closure status and a known-limits status surface so broader
  physics work can be staged without overstating recovery.
- New closure runway witnesses:
  the canonical Stage C path now also exports a first known-limits recovery
  witness and a witness-bearing spin/Dirac consumer surface.
- New closure runway theorem surfaces:
  the canonical Stage C path now also exports a concrete minimal
  constraint-closure witness and a stronger known-limits recovery witness that
  carries actual propagation and effective-geometry witnesses, not only status
  tags.
- New closure runway theorem slices:
  the canonical Stage C path now also exports:
  a minimal algebraic-closure theorem for the concrete three-generator system,
  a scoped known-limits local-recovery theorem for the current local
  Lorentz + propagation slice,
  and a scoped effective-geometry theorem for the same local recovery regime.
- Next canonical runway theorem slices:
  a scoped gauge-contract theorem on top of the canonical concrete closure
  baseline,
  and a scoped spin/local-Lorentz bridge theorem on top of the local recovery
  and effective-geometry baseline.
- Those two scoped runway theorems now live on the canonical Stage C path.
- The current widening beyond those scoped slices is now landed:
  a carrier-parametric gauge/constraint theorem with the current concrete
  carrier as its first instance, plus a second realized carrier instance,
  and a local causal-effective propagation theorem with a further local
  geometry-transport theorem on the current recovery baseline.
- Next widening step:
  a package-parametric gauge-constraint bridge theorem on top of the current
  carrier-parametric theorem, and a local causal-geometry coherence theorem
  above the transport slice.
- Those widening slices are now landed.
  Current newest physics-first widening is also landed:
  a stronger local recovery theorem beyond the current coherence slice,
  plus a stronger algebraic-coherence theorem beyond the current
  package-parametric bridge.
- That next physics-first widening is now landed:
  one stronger local recovered-regime theorem on top of the current local
  physics coherence slice,
  and one stronger algebraic-stability theorem on top of the current
  algebraic-coherence slice.
- That next physics-first cycle is now landed:
  one stronger recovered-dynamics theorem above the current complete-local
  regime slice,
  one stronger algebraic-consistency theorem above the current
  algebraic-bundle/stability slice,
  one geometry-facing downstream consumer on the widened canonical ladder,
  and one richer moonshine comparison bundle on the prototype track.
- Current next physics-first cycle is now landed:
  one stronger recovered-wave-geometry theorem above the current
  recovered-wavefront slice,
  one stronger algebraic regime-invariance theorem above the current
  transport-invariance slice,
  one wave-geometry-facing downstream consumer on the widened canonical
  ladder,
  and one richer moonshine twined-wave family summary on the prototype track.
- Current newest physics-first cycle is now landed:
  one stronger recovered-wave-regime theorem above the current
  recovered-wave-geometry slice,
  one stronger algebraic regime-persistence theorem above the current
  regime-invariance slice,
  one wave-regime-facing downstream consumer on the widened canonical
  ladder,
  and one richer moonshine twined-wave-regime summary on the prototype track.
- Current latest physics-first cycle is now landed:
  one stronger recovered-wave-observables theorem above the current
  recovered-wave-regime slice,
  one stronger algebraic regime-coherence theorem above the current
  regime-persistence slice,
  one wave-observable-facing downstream consumer on the widened canonical
  ladder,
  and one richer moonshine twined-wave-observable summary on the prototype track.
- Current algebraic milestone:
  use the already-landed finite orbit-shell generating-series layer for the
  current shift profile, then use it for standalone `B₄` comparison and a
  prototype wave lift.
- Safe symmetry-interpretation order:
  treat the current orbit profile as living first in a
  Weyl/root-system/theta-like neighborhood;
  only ask Niemeier/umbral-style questions if a genuine root-lattice shell
  realization appears;
  reserve Monster/Moonshine language for a future graded-module / trace bridge.
- Current moonshine-facing prototype:
  finite graded shell series and twined fixed-point traces are now present for
  the shift signed action and the standalone `B₄` Weyl action; canonical
  closure now carries a theorem-backed `Quadratic⇒Clifford → WaveLift⇒Even`
  factorization bridge, while the moonshine trace adapter remains prototype.
  Richer twiner libraries and a first graded/twined comparison report surface
  are now landed.
  A richer comparison bundle now sits over the existing detailed report and
  wave summary while staying pre-moonshine and non-modular.
  Safe interpretation policy:
  if a Monster-labeled anomaly report only shows a small rigid substructure
  without clear baseline/control separation, treat it as a non-unique
  structural regularity, not a Monster-specific fingerprint.
  Current measurement discipline:
  the DA51 / exponent-vector embedding is presently a representation-level
  structural probe, not a reliable semantic classifier for Monster-labeled
  proofs.
  Use JMD-side regime metadata (`eigenspace`, `bott`, `Hecke`, `orbifold`,
  `DA51`, `j-fixed`) for occupancy/divergence questions, and use DASHI-side
  delta/cone/Fejér/trace tests for dynamical questions.
  In particular, `p47` / `j-fixed` is currently best read as a baseline gauge
  constraint or normalization, not as a Monster-specific invariant.
  A local CSV-driven analysis harness now lives at
  `scripts/regime_test.py` for matched JMD regime tests, DASHI-side
  transition-table comparisons, and stepwise cone / Fejér checks from trace
  CSVs.
  For existing `dashifine` step embeddings, the direct entrypoint is:
  `python scripts/regime_test.py cone ../dashifine/hepdata_lyapunov_test_out/dashi_idk_out.csv/closure_embedding_per_step.csv --preset dashifine-closure-embedding`.
  That preset now reports the split explicitly:
  learned structural-cone pass,
  separate arrow-monotonicity pass,
  and the joint pass rate.
  Current direct result on the sibling-repo trace is:
  `structural_cone_pass_rate=1.0`,
  `arrow_pass_rate=0.9333`,
  `joint_pass_rate=0.9333`,
  with residual failures localized to `phistar_50_76` on `v_arrow`.
  The next cone-mode refinement is ultrametric/ternary boundary reporting:
  structural sign patterns, magnitude buckets, and nearest admissible pattern
  distance for localized violations.
  That ultrametric/ternary boundary report is now available in the same
  command output and confirms the current `phistar_50_76` failures are
  arrow-only boundary cases rather than structural-signature escapes.
  The same command now also performs an arrow-guard sweep, which on the
  current `dashifine` trace shows:
  `eps=1e-4 -> joint_pass_rate=0.95`,
  `eps=1e-3 -> 0.9667`,
  `eps=1e-2 -> 0.9833`,
  `eps=1e-1 -> 1.0`.
  The next refinement is an explicit boundary-class export so arrow-only cases
  are reported separately from true structural-cone failures.
  That boundary-class export is now present:
  the checked sibling-repo trace splits into `56` `interior` steps and `4`
  `arrow_boundary` steps, and the boundary cases can be written to CSV for
  downstream witness or review flows.
  That same harness now also carries canonical arrow profiles:
  `strict` (`arrow_eps=0`),
  `boundary` (`arrow_eps=1e-2`),
  and `lenient` (`arrow_eps=1e-1`).
  On the checked sibling-repo trace those give:
  `56/4`, `59/1`, and `60/0` for
  `interior/arrow_boundary` counts respectively.
  The current stable exported boundary artifact is
  `artifacts/regime_test/arrow_boundary_latest.csv`.
  The execution-admissibility bridge is now also landed:
  `scripts/regime_test.py cone` can export
  `artifacts/regime_test/execution_admissibility_latest.json`,
  `artifacts/regime_test/eigen_overlap_latest.csv`,
  and a concrete Agda witness module at
  `DASHI/Physics/Closure/ExecutionAdmissibilityCurrentTraceWitness.agda`.
  The same bridge now also exports a family-level Agda witness module at
  `DASHI/Physics/Closure/ExecutionAdmissibilityCurrentFamilyWitness.agda`,
  threaded through `PhysicsClosureCoreWitness` and surfaced from
  `MinimalCrediblePhysicsClosure`.
  The current strict-profile export still classifies the checked trace family
  as `56` `Interior` and `4` `ArrowBoundary`, with no structural-boundary or
  outside-class cases.
  The JMD-side scaffold is now seeded rather than empty:
  `scripts/build_jmd_regime_table.py` merges
  `data/regime_test/jmd_regime_seed.csv` into the Agda-tree scan and rebuilds
  `artifacts/regime_test/jmd_regime_table.csv`.
  Current first seeded occupancy read on the matched `7` Monster and `6`
  control rows is:
  `eigenspace JS=0.5569`,
  `bott JS=0.0608`,
  `joint(eigenspace,bott,hecke) JS=0.6176`,
  with the categorical comparison now running on the actual `M/O` subset
  rather than leaking unlabeled rows into the permutation/classification pass.
  The current seeded regime columns are still graph/seed proxies rather than a
  theorem-grade semantic ground truth, so they are suitable for local
  comparison scaffolding but not yet for strong symmetry claims.
  Source-side clarification:
  the explicit DASL / Monster address grammar now identified for this bridge
  lives in the sibling repo `../kant-zk-pastebin`.
  There, `src/dasl.rs` fixes the `0xDA51` address format, Monster primes,
  attack triple `(47,59,71)`, and orbifold coordinates;
  `src/sheaf.rs` fixes `EigenSpace`, encoding→prime assignment, and Bott/Hecke
  address fields;
  `src/ipfs.rs` wraps content in a DASL/CBOR envelope carrying those fields.
  So the repo now treats `kant-zk-pastebin` as the source-side `Σ_src` anchor
  for `Basin` / `Eigen` questions, while this repo remains the execution-side
  admissibility layer.
  A separate Lean-side check of `../dashi_lean4` does not change that.
  That repo is useful as a Lean witness for DA51/moonshine numerics and schema
  transport, but it does not provide the missing JMD-side class/projection
  layer:
  no DASL address grammar, no `EigenSpace` / `Earth|Spoke|Hub|Clock`, and no
  Bott/Hecke/orbifold class table for the HEPData family projection problem.
  Immediate implementation consequence:
  the next harness pass should load that DASL source model directly so
  `basin_ok` and source-backed eigen overlap are computed against an explicit
  source lattice grammar rather than only trace heuristics or seeded JMD rows.
  Current semantics note:
  `basin_ok` in the local artifacts presently means support under the parsed
  DASL eigenspace prior, not a full class-level source projection theorem.
  The runtime exports now carry the more explicit `source_support_ok` alias as
  well, and `basin_ok` should be read as that proxy until the source projector
  is richer.
  That first-pass source integration is now landed in `scripts/regime_test.py`:
  `cone` mode can parse the DASL source grammar from `../kant-zk-pastebin`,
  emit `artifacts/regime_test/dasl_source_lattice_latest.json`,
  and report a DASL-backed eigen prior plus a first-pass source-support
  `basin_ok`.
  On the checked `dashifine` trace family, that source-backed pass leaves the
  structural/arrow split unchanged (`56` `Interior`, `4` `ArrowBoundary`) but
  now also reports a narrower source mismatch:
  `48/60` steps are source-supported while `12/60` steps from `pTll_76_106`
  currently miss the parsed DASL eigenspace support because the trace-side
  heuristic lands them in `Hub` while the parsed DASL encoding prior is
  `Earth/Spoke`-only.
  Safe reading:
  this source anchor is enough to make first-pass source predicates
  computable, but it is not yet a proof that DASHI projection preserves the
  shared `p47`/gauge constraint automatically.
  Immediate next refinement:
  replace the current trace-side `Hub` heuristic with a profile-based
  eigenspace classifier and export both legacy and refined trace labels in the
  eigen/execution artifacts, since the present `pTll_76_106` mismatch is
  concentrated in that heuristic boundary.
  That refinement is now landed.
  The current artifacts export both `legacy_trace_eigenspace` and refined
  `trace_eigenspace`, and the direct `dashifine` rerun shows:
  `legacy_vs_refined_trace_agreement=4/5`, with the only changed family
  `pTll_76_106` moving from legacy `Hub` to refined `Spoke`.
  Under that refined classifier, the source-support proxy now clears the whole
  checked five-trace family: `60/60 source_support_ok`.
  Immediate next source-side refinement:
  the DASL loader should stop treating the source model as only the small
  encoding prior and instead lift the full `15`-prime Monster catalog already
  fixed in `../kant-zk-pastebin/src/dasl.rs`.
  That would make the exported source model explicitly carry `Earth/Spoke/Hub/Clock`
  support from the whole prime basis rather than only the encoding subset.
  That source-catalog promotion is now landed.
  The default DASL source mode is now `monster-primes`, and the emitted source
  JSON records all `15` primes plus the current eigenspace distribution
  `Earth=0.4667`, `Spoke=0.4`, `Hub=0.0667`, `Clock=0.0667`.
  On the checked `dashifine` trace this richer source model still preserves the
  same execution picture:
  `56 Interior`, `4 ArrowBoundary`, `60/60 source_support_ok`.
  The harness now also exposes an explicit source-projection proxy on top of
  that richer catalog.
  For the current checked traces, the canonical class-to-prime projection is:
  Earth-family traces → `p2 / T_2 / exponent 46`,
  and the refined `Spoke` trace family `pTll_76_106` → `p17 / T_17 / exponent 1`.
  This is a canonical source-projection surface, not yet a geometric
  nearest-neighbor theorem.
  Immediate next refinement:
  enrich that proxy into a scored source-prime ranking over the current source
  catalog, so the artifacts expose more than class membership and a single
  exponent tie-break while still staying short of a geometric nearest-neighbor
  claim.
  That scored ranking is now landed too.
  The artifacts now export a top-ranked source-prime shortlist per trace family.
  On the checked traces:
  Earth-family traces still rank `p2` first,
  while the refined `Spoke` family `pTll_76_106` shows a meaningful split:
  the canonical proxy remains `p17`, but the scored shortlist ranks
  `p59` and `p71` above it because they combine the same `Spoke` class with the
  attack-triple bonus.
  Treat that as a ranking heuristic signal, not yet as a promoted projection
  theorem.
  Immediate next refinement:
  expose an explicit primary source-projection mode so the repo can keep the
  conservative canonical proxy as default while also supporting a scored-primary
  projection mode for experiments.
  That explicit primary mode is now landed.
  `scripts/regime_test.py cone` keeps the canonical
  `source_projection_*` fields as the repo-default bridge surface, and also
  exports `primary_source_projection_*` fields driven by
  `--source-projection-primary canonical|scored`.
  Default remains `canonical`; `scored` is for experimental ranking-led runs.
  The artifacts now also export `projection_conflict` so rows like
  `pTll_76_106` can be marked explicitly when the canonical representative and
  the primary-selected experimental representative diverge.
  The scored ranking is now also canonical-anchored rather than
  attack-triple-led in isolation, and the exported shortlist is labeled
  explicitly as a diagnostic shortlist rather than a promoted primary
  projection surface.
  The artifacts now also expose score-component breakdowns for the ranked and
  primary source projections, so later source-side refinements can target the
  metric weights explicitly instead of treating the ranking as opaque.
  Canonical export cleanup also removed the legacy assumption-first closure
  instance from the public `PhysicsClosureSummary` and `Everything` surfaces;
  the compatibility module remains on disk, but it is no longer publicly
  re-exported on the canonical path, and the umbrella import no longer pulls
  in the empirical-to-full adapter either. The external full-closure
  constructor and the provider-based constructor are now named as legacy
  adapters, so the canonical naming no longer implies that the outside-wired
  routes are authoritative.
  The canonical `physicsClosureFullFromCoreWitness` path now assembles the
  full closure directly from the core witness, instead of bouncing through the
  legacy external adapter.
  The canonical contraction→quadratic theorem constructor now also delegates
  through the strong package’s canonical identity witness, so the uniqueness
  transport seam is less duplicated.
  The current score now includes source-side `Hecke` proximity and a weak
  `Bott` cycle prior in addition to trace support, exponent, canonical
  alignment, and attack-triple bonus.
  A three-batch `dashifine` rerun is now recorded in
  `artifacts/regime_test/dashifine_trace_batch_latest.json`.
  Across the current `out`, `out_new`, and `out_all` trace sets, source support
  stays fully intact and the refined `Spoke` family stays canonically at `p17`;
  the main new movement is on the execution side, where larger batches add
  `ttbar_mtt_8tev_cms` and `z_pt_7tev_atlas` to the arrow-boundary family list.
  The harness now also exports a per-family boundary summary at
  `artifacts/regime_test/arrow_boundary_family_latest.json` for the default
  checked run, and the larger-batch read is now sharper:
  `phistar_50_76` is a small arrow-only tolerance ladder,
  `z_pt_7tev_atlas` is a single moderate arrow break,
  and `ttbar_mtt_8tev_cms` is the strongest current outlier because it couples
  large arrow violations with `v_dnorm` failures.
  Focused family drilldowns are now exportable too.
  The current `ttbar_mtt_8tev_cms` read is especially specific:
  it stays interior until a late onset at `t=10->11`, where a sign flip in the
  arrow coordinate coincides with the first mixed `v_arrow`/`v_dnorm` failure
  without an immediate structural-signature change.
  A terminal-step autopsy now also records raw axis values, per-axis deltas,
  and alternate `v_dnorm` normalizations for that family.
  On the current larger-batch run, those alternate `v_dnorm` views do not
  remove the two terminal positive `v_dnorm` deltas; they remain positive under
  raw, log-absolute, robust-z, winsorized, and family-minmax transforms.
  The important scale caveat is that those `v_dnorm` reversals are tiny
  (`~9.4e-13` and `~1.6e-13`) and sit at a near-zero floor, so the current best
  reading is late terminal-phase stiffness or tail-edge sensitivity in the
  representation, not a broad failure of the learned structural cone.
  The focused export now also carries observable-side context:
  `ttbar_mtt_8tev_cms` is a `7`-bin spectrum whose last bin (`x≈1350`) has the
  largest fractional uncertainty (`~8.19%`), and the first failing step occurs
  at the late `alpha=1e4 -> 1e5` jump.
  The same local provenance pass also shows that this family still has
  `closestpoint_frac=1.0` and `fejer_set_frac=1.0` in the sibling-repo reports,
  while the explicit failure sits on the MDL-exact surface
  (`MDL_monotone=False`, `2` violations, worst increase `0.694577`).
  So the current disciplined reading is:
  localized late MDL/tail-bin stiffness inside an otherwise closest-point /
  Fejér-admissible family, not a general collapse of the closure geometry.
  The local harness now reflects that directly at the family-summary layer:
  `ttbar_mtt_8tev_cms` is promoted from the generic
  `mixed_hard_axis_outlier` bucket to the narrower `mdl_tail_boundary` class,
  while the per-step witness remains unchanged as `ArrowBoundary`.
  That interpretation is now also encoded in
  `DASHI/Physics/Closure/TailBoundaryLemma.agda`:
  on the current family witness there exists an
  `MDLTailBoundaryFamily` whose family-level witness still satisfies
  cone / Fejér / closest-point admissibility while failing only at the
  stricter MDL-exact layer.
  The current empirical count artifact is
  `artifacts/regime_test/tail_boundary_lemma_latest.json`, which on the
  checked larger `dashifine` family set reports `1` `mdl_tail_boundary`
  family out of `9`, and that current case is both tail-localized and
  terminal-boundary by the local summary rule.
  The widened three-batch aggregate is now recorded in
  `artifacts/regime_test/tail_boundary_batch_latest.json`, produced by
  `scripts/tail_boundary_batch.py`.
  On the currently compatible `dashifine` batches it reports
  `2` `mdl_tail_boundary` instances across `3` datasets, with only one unique
  family (`ttbar_mtt_8tev_cms`), and both observed instances remain
  tail-localized, terminal-boundary, cone/Fejér/closest-point admissible, and
  MDL-exact-failing.
  The same aggregate now also makes the control split explicit:
  repeated `pTll` families plus `dijet_chi_7tev_cms` and `hgg_pt_8tev_atlas`
  remain interior controls, `phistar_50_76` repeats only as
  `arrow_ladder`, `z_pt_7tev_atlas` repeats only as `single_arrow_break`,
  and only `ttbar_mtt_8tev_cms` repeats as `mdl_tail_boundary`.
  The aggregate now also records the current expansion inventory directly:
  there are `3` compatible step files in `dashifine`,
  `7` current tail-candidate families,
  and among those only `ttbar_mtt_8tev_cms` and `z_pt_7tev_atlas` currently
  leave the interior.
  The next-priority tail candidates after `ttbar` are therefore
  `z_pt_7tev_atlas`, then the still-interior heavy-spectrum candidates
  `atlas_4l_m4l_8tev`, `atlas_4l_pt4l_8tev`,
  `dijet_chi_13tev_cms_mgt6`, `dijet_chi_7tev_cms`, and
  `hgg_pt_8tev_atlas`.
  The current focused `z_pt_7tev_atlas` drilldown now sharpens that next step:
  it is not another `mdl_tail_boundary`.
  It remains a milder `single_arrow_break`: one late tail-localized boundary
  step at `t=9->10`, `arrow_delta≈0.0305551`, no non-arrow failure, all tested
  `v_dnorm` variants remain nonincreasing there, and the family clears under
  the `lenient` arrow profile.
  The first still-interior heavy-spectrum candidate is now checked too:
  `atlas_4l_m4l_8tev` stays fully interior on the same all-batch run.
  Current focused read:
  `12` steps, `0` boundary steps, `closestpoint_frac=1.0`,
  `fejer_set_frac=1.0`, `MDL_monotone=True`, no onset event, and its last bin
  is not the maximum-fractional-uncertainty tail bin.
  The next heavy-spectrum control `atlas_4l_pt4l_8tev` is now checked as well
  and stays fully interior too:
  `12` steps, `0` boundary steps, `closestpoint_frac=1.0`,
  `fejer_set_frac=1.0`, `MDL_monotone=True`, no onset event, and its last bin
  is likewise not the maximum-fractional-uncertainty tail bin.
- Next theorem milestone:
  the bounded one-minus shell family is now the base layer and the parametric
  shell-1 theorem is now in place; the next theorem milestone is a second
  Lorentz-family realization and stronger shell-2 / orientation follow-through.
- Current closure hardening target:
  keep the canonical Stage C path, the empirical full adapter, and the legacy
  assumed closure surface on the same concrete constraint-closure witness, and
  keep the canonical Stage C entrypoint explicit in code rather than only in
  summary prose.
- Next runnable benchmark:
  Fejér-over-χ² monotonicity, starting from a typed shift reference harness
  with theorem-backed Fejér / closest-point / MDL witnesses and an explicit
  χ² falsifier-status boundary.
- Newly landed benchmark surface:
  observable-space collapse is now exposed as a typed shift benchmark backed
  by the observable fixed-point and uniqueness witnesses in the real closure
  kit.
- Current Fejér benchmark snapshot:
  positive side established and carried directly by the benchmark harness,
  χ² side now has a concrete shift-side boundary witness,
  that witness now sits inside a small explicit shift-side boundary library,
  and the standalone snap-threshold benchmark now includes secondary and
  tertiary shift-side boundary cases beyond the reference witness.
- Non-shift snap-threshold coverage now includes:
  a synthetic one-minus harness with a non-shift policy derived from its
  witness state type, a Bool inversion-specific harness with its own witness
  selection, and a standalone `B₄` harness.
- Lemma A/B constructive eliminators are now in place inside
  `CausalForcesLorentz31`; prioritized next steps (condensed):
  1) keep closure-pipeline labels and repo-facing citation order synchronized
     as modules are promoted,
  2) re-run direct `PhysicsClosureValidationSummary.agda` timing/validation when
     a longer runtime budget is available.

The repo does **not** currently claim full physics closure or “solved
physics”.

Note on `DASHI/Unifier.agda`:
it is a stub-style unification sketch that exposes axiomatized/placeholder
interfaces (not theorem-backed), and it is not part of the canonical Stage C
closure pipeline.

For the current forward-claim shortlist and falsifiability criteria, see
`Docs/MinimalCrediblePhysicsClosure.md`.
For the math-prof outreach framing and archive crosswalk, see
`Docs/MathProfOutreachSummary.md`.

Cleanup note:
- the current maintenance turn freezes new local wave-regime rungs,
  treats the grouped ladder modules as the authoritative internal API,
  and keeps the old per-rung modules only as compatibility surfaces.
- widening resumes only after canonical Stage C and the repo-facing summaries
  depend on the grouped surfaces rather than direct per-rung imports.
For the current milestone order, see `Docs/PhysicsClosurePriorities.md`.
For the current orbit-shell / Lorentz-signature framing, see
`Docs/OrbitShellProfilesAndLorentzSignature.md`.
For the authoritative Stage C theorem chain and module labels, see
`Docs/ClosurePipeline.md`.

## Typecheck Performance Policy (Current)

- Keep theorem certainty unchanged: performance work must not replace proven
  theorems with postulates.
- Use `abstract` for heavy theorem terms when downstream modules only need the
  theorem type, not internal definitional unfolding.
- First rollout target: repo-facing closure summary aliases in
  `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`.
- Second rollout target: aggregate theorem/summary record values in
  `DASHI/Physics/Closure/CanonicalStageCTheoremBundle.agda` and
  `DASHI/Physics/Closure/CanonicalStageCSummaryBundle.agda`.
- Third rollout target: remaining moonshine/regime summary aliases in
  `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`.
- Keep computational kernels transparent where reduction is part of behavior.
- For cyclic Base369 operators, prefer closed-form index arithmetic companions
  and explicit correctness bridges from recursive `spin` forms.

# I. State Space 

### 1. Carrier

Let

[
T = {-1, 0, +1}
]

Interpretation:

* (+1) = constructive / help
* (0) = neutral / indeterminate
* (-1) = destructive / harm

---

### 2. 3×3 Reasoning Tensor

[
S \in T^{L \times \tau}
]

Where:

**Lenses**
[
L = {3,6,9}
]

* 3 = Self
* 6 = Norm
* 9 = Mirror

**Temporal gates**
[
\tau = {p,0,f}
]

* p = past
* 0 = present
* f = future

Cardinality:

[
|T^{9}| = 3^9 = 19,683
]

This is the full virtual state sheet.

---

# II. Extracted Invariants

The supervisor does **not** reason over all 19,683 states directly.

It extracts an invariant tuple:

[
I(S) = (b_0, \sigma, \Delta_m, T, Z)
]

---

## 1. Present Backbone

[
b_0 = (S_{3,0}, S_{6,0}, S_{9,0}) \in T^3
]

This is the “spine”.

---

## 2. Temporal Instability per lens

[
\sigma_\ell = #{t_i \neq t_{i+1}}
]

Total instability:

[
\sigma = \sigma_3 + \sigma_6 + \sigma_9
]

---

## 3. Mirror Asymmetry

[
\Delta_m = \sum_{t \in \tau}
\mathbf{1}[S_{9,t} \neq \text{mirror_check}(S_{*,t})]
]

Measures conjugation failure.

---

## 4. Tension Mass

[
T = #(+) \cdot #(-)
]

High when help/harm coexist strongly.

---

## 5. Neutral Load

[
Z = #(0)
]

Tracks indeterminacy.

---

# III. Deterministic Motif Classifier

Define

[
\mathcal{M} : T^9 \to {M_1,\dots,M_9}
]

Ordered by priority rules.

---

## M1 – Robust Allow

Condition:

* (b_0 = (+,+,+))
* (\sigma = 0)
* (\Delta_m = 0)

Interpretation:
Full constructive interference.

Action:
Allow.

---

## M2 – Time-Gated Allow

Condition:

* (S_{3,0}=+)
* (S_{6,0}=+)
* (S_{9,0}=+)
* (S_{9,f} = -)

Interpretation:
Future instability only.

Action:
Add timing fence.

---

## M3 – Role-Gated

Condition:

* (S_{3,0}=+)
* (S_{9,0}=+)
* (S_{6,0}=-)

Interpretation:
Norm conflict only.

Action:
Restrict by role.

---

## M4 – Substrate Fail

Condition:

* (S_{6,0} \ge 0)
* (S_{9,0} \ge 0)
* (S_{3,0} \le 0)

Interpretation:
Externally coherent but locally harmful.

Action:
Redesign substrate.

---

## M5 – Mirror-Unstable

Condition:

* (S_{3,0}=+)
* (S_{6,0}=+)
* (S_{9,0}=-)

Interpretation:
Present looks fine but fails reflection.

Action:
Buffer. Do not generalize.

---

## M6 – Redesign Lane

Condition:

* (b_0 = (-,-,-)) OR strongly negative present
* but ∃ t ∈ {p,f} s.t. (S_{9,t} = +)

Interpretation:
Non-local constructive path exists.

Action:
Reframe (dose/time/product).

---

## M7 – Tolerance Rim

Condition:

* (S_{3,0}=+)
* but (\sigma) large
* flips toward negative over time

Interpretation:
Dynamical fatigue.

Action:
Frequency control.

---

## M8 – Programmatic Only

Condition:

* Sparse positive occupancy
* Most entries negative

Interpretation:
Filamentary viability only.

Action:
Structured program only.

---

## M9 – Retire / Prohibit

Condition:

[
b_0 = (-,-,-)
]

Interpretation:
All-red spine.

Action:
Disallow.

---

# IV. Topological Interpretation (Optional Layer)

You can interpret motifs as equivalence classes under symmetry:

[
G = S_3^{time} \times C_2^{mirror}
]

Motifs are orbits in quotient:

[
T^9 / G
]

Examples:

| Motif | Geometry        |
| ----- | --------------- |
| M1    | Stable sink     |
| M5    | Saddle          |
| M7    | Spiral          |
| M9    | Absorbing basin |

This is explanatory, not required for classification.

---

# V. M10 – Voxel Overflow

M10 is not a motif in the same equivalence class.

It is a **resolution jump**.

Define capacity:

[
C = 9
]

Overflow trigger:

[
Z + T > C
]

Interpretation:
Local invariant compression insufficient.

Operation:
Lift

[
T^9 \to T^{9} \times T
]

i.e., introduce new coordinate axis.

This is a carry operation (p-adic style).

Result:
New voxel.

---

# VI. Structural Summary

You now have:

* Finite state space (3^9)
* Deterministic invariant extraction
* Deterministic classification
* Explicit overflow rule
* No metaphors required
Current refactor status:
- the local Stage C wave-regime ladder is frozen for now
- grouped ladder modules are the authoritative internal import path
- widening resumes only after canonical code is routed through those grouped surfaces

## Local Nix / Zkperf Merge Surface

The repo now carries a local merge-prep Nix surface intended to harden an
upstream `nix`/`zkperf` merge without overstating what it validates.

- `nix build .#check` is the authoritative Nix check and mirrors the current
  GitHub workflow by typechecking `DASHI/Everything.agda`.
- `nix build .#merge-smoke` is the recursive merge-prep smoke check and walks
  the merge-relevant standalone roots plus recursive `Kernel/`, `Monster/`,
  and `Verification/` modules.
- The merge-prep target list is centralized in
  `scripts/list_merge_agda_targets.sh`, and the actual recursive compiler pass
  is wrapped by `scripts/run_agda_merge_smoke.sh`.
- `agda-record-all` is expected to recurse over that same merge-prep target
  surface rather than only top-level files.
- `dashi-agda.agda-lib` is now present as the local library surface used by
  this tooling layer.
- Any tracked DA51 / zkperf JSONL examples should be read as sample witness
  outputs, not as canonical reproducibility fixtures.

Merge-prep status:
the local Nix / zkperf surface is complete and validated, so active work now
returns to the physics closure spine and the existing tail-boundary follow-up
track.

## RG Toy Next Phase

The RG toy is now past pure shell/plumbing work.
It has operator families, mixed coarse/evolve schedules, endpoint and rich
benchmark layers, and a trace-aware mixed benchmark surface.

The next RG implementation work is split deliberately:

- Phase 2: enrich the operator/state hierarchy.
  Add multiple coarse schemes, multiple evolve modes, and a less trivial
  fixed-point/family structure so universality is not being tested against one
  stylized route.
- Phase 3: restate the current comparison and benchmark theorems against that
  richer hierarchy.
  The target is endpoint agreement with room for path/scale disagreement,
  rather than more collapse lemmas on the current toy encoding.
