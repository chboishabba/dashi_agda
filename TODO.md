# TODO

## Track P — Photonuclear Numerical Prototype (2026-03-30)

Priority bucket: `P0`

- [x] Document the photonuclear bridge, charm observable map, saturation layer,
  and CMS capstone under `Docs/`.
- [x] Split the reduced executable prototype into explicit layers:
  observable extraction,
  reduced response families,
  and runner/comparison entrypoints.
- [x] Add the first two hand-constructed example states for near-miss and
  head-on explanatory inspection.
- [x] Add a second reduced model family (`IPsat`-style) so explanation is not
  tied to a single GBW surrogate.
- [x] Add a batch prediction matrix runner over example states and model
  families so the current prototype exposes cross-channel and cross-model
  explanations in one artifact.
- [x] Replace hand-constructed example states with a small state-emitter
  derived from the actual Dashi shift geometry / admissibility pipeline.
- [ ] Next follow-up: add one more reduced response family (for example
  `rcBK`-style) or prune the current families if one proves redundant under the
  explanatory matrix.
- [x] Define a non-fitting scorecard for “best explanation” that compares
  residuals and MDL burden without claiming empirical fit to CMS data.
- [x] Teach the matrix/comparison runners to invoke the shift example emitter
  automatically when the canonical emitted example files are missing or stale.
- [x] Add the same auto-refresh path to the single-state model comparison
  runner.
- [ ] Next follow-up: decide whether the base runner should expose the same
  canonical-example auto-refresh and scorecard output by default.

## Track G — Dynamics / Invariants Closure Gap (2026-03-30)

Priority bucket: `P0`

- [x] Add a repo-accurate checklist separating truly missing theorem families
  from structures that already exist as canonical or partially trivial
  witnesses.
- [ ] Current Hecke-side long-compute lane: do not re-run the heavy
  refinement/decomposition checks interactively. The live implementation
  surfaces are now
  `Ontology/Hecke/DefectOrbitSummaryRefinement.agda`,
  `Ontology/Hecke/ForcedStableCountDecomposition.agda`,
  `Ontology/Hecke/TriadIndexedDefectOrbitSummaryRefinement.agda`, and
  `Ontology/Hecke/CurrentSaturatedTriadHistogramSeparation.agda`, plus the
  concrete current-scope packaged-data companion
  `Ontology/Hecke/CurrentSaturatedSectorHistogramComputations.agda`, and the
  status package `Ontology/Hecke/SaturatedInvariantRefinementStatus.agda`.
  The next fixed-domain target is to decide whether the triad-indexed
  histogram separates any classes in the already-classified saturated
  generator taxonomy. The immediate next proof order is now:
  sector-level separation on the packaged current-scope computations, then
  whole-package separation, and only after that interpret the result as
  `3 × 5`, `9 + 6`, or another structural factorization.
- [ ] Keep `Ontology/Hecke/CurrentSaturatedPredictedPairComparisons.agda` in
  sync with the actual Layer 2 proof order. The current first-pair sequence
  is:
  `balancedCycle` vs `supportCascade`,
  `balancedComposed` vs `supportCascade`,
  then `denseComposed` vs `fullSupportCascade`.
  Treat it as the narrow pairwise target surface for the current saturated
  branch, not as a new summary layer and not as a reason to broaden the
  taxonomy.
- [ ] If the triad-histogram lane collapses on those fixed-domain pairs, move
  immediately to
  `Ontology/Hecke/TriadSectorCorrelationRefinement.agda`
  rather than inventing new totals. The correlation fallback is now defined as
  `(v₀·v₁, v₁·v₂, v₂·v₀)` on the ordered sector histograms, and
  `Ontology/Hecke/CurrentSaturatedPredictedPairComparisons.agda` now carries
  the matching predicted-pair comparison targets.
- [ ] Keep the new
  `Ontology/Hecke/Layer2FiniteSearch.agda`
  surface thin. It is only the bounded Layer 2 packaging of the current
  fixed-domain proof order
  (`sector -> package -> correlation` on the three predicted pairs),
  not a new invariant surface and not a reason to re-run the heavy histogram
  modules interactively. If this lane is automated later, follow the sibling
  `../agda` proposal/replay/promote shape: bounded attempts first, promotion
  only after actual separator or exhaustion discharge.
- [ ] Treat
  `Ontology/Hecke/Layer2FiniteSearchShell.agda`
  as the truly compile-thin control surface for Layer 2.
  It intentionally postulates the fixed targets instead of importing the
  histogram lane, so it is the safe interactive typecheck when we only want
  to validate pair ordering / stage ordering without reopening the heavy
  transitive chain.
- [ ] Use
  `scripts/generate_layer2_long_compute_queue.py`
  as the canonical long-compute queue emitter for the current saturated
  Layer 2 speedrun. It should remain a pure control-plane helper with
  two explicit batches:
  compile-thin shell checks first, then the offline-heavy fixed pair / fixed
  stage replay queue. Keep the optional `agda --parallel` command templates,
  and the grouped by-pair / by-stage artifact writing, but no proof-side
  execution and no mutation of the heavy lane.
  Keep the emitted artifact directories self-indexing via `index.txt` and
  `index.json`, so offline handoff does not require directory inspection.
- [ ] Use
  `scripts/render_layer2_batch_commands.py`
  when a materialized Layer 2 batch JSON needs to be turned into executable
  command lines or a runnable shell script for offline handoff.
  Keep this wrapper read-only with respect to the heavy proof lane:
  it should render commands, not execute them.
  Use the dedup mode when the batch carries repeated identical `agda`
  invocations and the right artifact is a unique command list rather than a
  step-by-step replay script.
- [ ] Use
  `scripts/route_agda_by_layer.py`
  as the canonical execution-policy helper before running Agda targets in
  session. Keep the stratification explicit:
  `L0` interactive,
  `L1` bounded,
  `L2` offline only.
  In particular, route the current heavy Hecke Layer 2 implementation lane to
  queue generation rather than running those modules interactively.
- [x] Add a simple easiest-to-hardest runner above the existing policy and
  queue tools for the already-validated light and medium targets.
  `scripts/run_agda_easy_to_hard.py` now runs the current thin sequence in the
  intended order:
  `Layer2FiniteSearchShell`,
  `Kernel/Monoid`,
  `Verification/Prelude`,
  the five canonical-prime bridge/invariance/concentration/selector/isolation modules,
  then optionally the bounded status module
  `Ontology/Hecke/SaturatedInvariantRefinementStatus.agda`,
  and finally optional Layer 2 queue generation.
  Keep it out of the heavy theorem lane:
  it should stop at queue emission rather than trying to execute the current
  long-compute Hecke batch.
- [ ] Status boundary reminder for Track G: treat the current state as
  `Layer 1 closed / Layer 2 open`, not as a total theory. The only live
  mathematical bottleneck on the current generator universe is the next
  separating invariant `I₂` on the saturated branch. Do not spend cycles on
  new generators, new coarse taxonomies, or broader claims until that lane is
  discharged one way or the other.
- [x] Separate the cheap carrier-level Monster/Ogg match from the still-open
  saturated-scalar interpretation.
  `Ontology/Hecke/MoonshinePrimeCarrierMatch.agda` now proves that the
  intrinsic `SSP` carrier is exactly the canonical 15-prime list
  `2,3,5,7,11,13,17,19,23,29,31,41,47,59,71`, and
  `scripts/check_monster_prime_carrier_match.py` checks the same equality on
  the Python side.
  Keep the signature-level equality as an explicit target surface, and do not
  describe `forcedStableCount = 15` as an Ogg/Monster theorem.
- [x] Land the first non-accidental canonical prime-selection/signature bridge
  surface without touching the heavy Hecke long-compute lane.
  `DASHI/Physics/Closure/CanonicalPrimeSelectionBridge.agda` now packages the
  current closure-side witnesses that really exist:
  prime witness on the transported 15-lane carrier,
  coarse/step commutation on the transported prime embedding,
  coarse/step commutation on the transported Hecke signature,
  and the current lower-bound bridge
  `illegalCount_chamber <= forcedStableCount_hist`.
  `scripts/check_canonical_prime_selection_bridge.py` now provides the matching
  cheap runtime support/subset check on `MoonshinePrimeState` JSON payloads.
  Keep `PrimeInvarianceTarget` and `PrimeIsolationTarget` as explicit open
  theorem targets until the MDL concentration / isolation clauses are actually
  discharged.
- [x] Split the first light prime-selection invariance layer away from the
  broader bridge and keep it support-level rather than whole-vector-level.
  `DASHI/Physics/Closure/CanonicalPrimeInvariance.agda` now proves support
  transport across the already-landed coarse/step commutation law for the
  transported prime embedding, and it now also proves the current
  support-level no-growth statement over the existing execution-admissibility
  boundary.
  Keep full MDL concentration and isolation as explicit later theorem work,
  because the stronger whole-vector/selective concentration story still does
  not follow from this support-level theorem.
- [x] Add the first exponent-level concentration surface above support so the
  next open theorem is no longer phrased on a saturated support notion.
  `DASHI/Physics/Closure/CanonicalPrimeConcentration.agda` now defines
  `PrimeWeight`, `PrimeDominates`, and `PrimeConcentrated` on the canonical
  15-prime carrier, and proves weight transport across the already-landed
  coarse/step commutation law.
  `scripts/check_canonical_prime_concentration.py` now exposes the matching
  cheap dominant-prime runtime check on `MoonshinePrimeState` payloads.
  Keep existence and no-loss of concentration as the next explicit theorem
  targets on this lane.
- [x] Add the first thin selector surface above exponent-level concentration.
  `DASHI/Physics/Closure/CanonicalPrimeSelector.agda` now packages the
  selector problem concretely rather than vaguely.
  The selector is now explicit on the Agda side and `selector-sound` is
  discharged there: highest exponent, lowest prime on ties.
  `scripts/select_canonical_prime.py` now implements the current explicit
  runtime selector rule and matches the Agda surface.
  Keep selector no-loss and selector/coarse-step commutation as the remaining
  theorem-bearing open claims.
- [x] Add a cheap Python falsification/probe surface for the still-open
  selector commutation theorem before retrying Agda.
  `scripts/check_selector_step_coarse.py` now compares two concrete
  `MoonshinePrimeState` payloads interpreted as `coarse(step(x))` and
  `step(coarse(x))`, and reports whether the explicit selector agrees on both
  sides.
  Use this to gather cheap evidence or a counterexample first; do not treat it
  as a proof of `selector-step-coarse-target`.
- [x] Add a repo-native bundle builder for that selector commutation probe so
  the first runtime check no longer depends on hand-written
  `MoonshinePrimeState` JSON.
  `scripts/build_selector_step_coarse_bundle.py` now reuses the current
  Agda-backed orientation-prime adapter from
  `scripts/moonshine_prime_from_twined_trace_shift.py` and emits the required
  `coarse_step` / `step_coarse` bundle shape directly.
  Keep the boundary explicit:
  this is a bridge-aligned runtime probe, not a full evaluator of the live
  `shiftCoarse` / `shiftStep` schedule.
- [ ] Physics-side execution-contract follow-up: now that
  `scripts/run_execution_contract_on_closure_csv.py` wires the reusable
  projected-delta enforcer onto `closure_embedding_per_step.csv` and
  `scripts/tail_boundary_batch.py` carries those receipts per dataset,
  replace any remaining residual absolute-state `Q(x)` or raw `j-fixed`
  screening in the deeper older analysis path with the five-clause contract:
  arrow,
  projected-delta cone,
  MDL,
  basin,
  eigen overlap.
  `scripts/regime_test.py` now drives `joint_ok` / `status_class` from that
  contract, so the remaining cleanup is narrower: remove or rename any
  misleading legacy `structural_*` references that still look like acceptance
  rather than diagnostics.
- [ ] Closure-side projection follow-up: now that
  `DASHI/Physics/Closure/Projection.agda` exists and
  `ExecutionContract.agda` consumes it directly, instantiate that interface
  with the nearest nontrivial source-side closure/eigen basis instead of
  keeping the projection object only abstract.
- [x] LILA bridge follow-up: instantiate
  `DASHI/Physics/Closure/LilaDashiBridge.agda` with a concrete execution
  carrier and a real trace family so the LILA-side execution story stays
  separated from the DASHI-side admissibility receipt.
  The first pass now exists as `DASHI/Physics/Closure/LilaTraceFamily.agda`,
  plus the companion scripts `scripts/delta_cone_lila.py` and
  `scripts/checkpoint_prime_vectors.py`.
- [x] LILA comparison pack follow-up: keep the PR-foot-forward bundle minimal
  by pairing the delta-cone analyzer with `scripts/run_compare.sh` and
  `scripts/plot_training_dynamics.py` so baseline-vs-LILA credibility checks
  stay simple and reproducible.
- [x] Make the bridge pack one-command runnable with `scripts/run_all.sh` and
  add a short PlantUML-backed usage page so the PR stays legible at a glance.
- [ ] Closure-side basin follow-up: now that
  `DASHI/Physics/Closure/Basin.agda` exists and the contract consumes it,
  replace the remaining heuristic basin choices with realization-sensitive
  attractor witnesses on the projected observable space.
- [ ] Agda-side execution-contract follow-up: extend the new readable receipt
  layer in `DASHI/Physics/Closure/ExecutionContractLaws.agda` into the
  nearest nontrivial shift/bundle witnesses instead of leaving it only as a
  generic law surface above `ExecutionContract.agda`.
- [ ] Archive provenance reminder for Track G: the canonical thread
  `Dashi and Physics Insights`
  (`69ca43a9-09fc-839b-8cc3-e5ce3868eef5`,
  canonical ID `ad17536d8eeb320106585654a0950424abafa93b`, source `db`)
  still justifies the older `Forced-Stable Transfer Bridge` priority as the
  right earlier bridge theorem. Keep that as historical provenance, but do
  not let it displace the current tighter Layer 2 bottleneck on the fixed
  saturated branch.
- [x] Replace the trivial execution-side eigen witness in
  `ShiftLorentzEmergenceInstance.agda` with one that is genuinely tied to the
  RG observable lane.
- [x] Lift the strengthened execution/invariant witness surface into the
  abstract bundle layer so it is no longer confined to the canonical shift
  carrier.
- [x] Promote the existing signature-lock stack into that same abstract bundle
  surface instead of leaving it as a strong but local canonical result.
- [x] Replace the shared-core/canonical anchor with an honest anchor-state
  import from the live shift RG surface once that module is revalidated on its
  own theorem path.
- [x] Generalize that anchor-state import into a carrier-level transport
  theorem surface from the live shift RG surface into the abstract
  gauge/matter bundle.
- [x] Replace the constant target-side transport with a first
  source-dependent carrier-level law factoring through the concrete canonical
  generators.
- [x] Make that carrier-level transport sensitive at the `RGObservable` level
  by letting the bundle observable follow the transported shift state through
  the live shift surface.
- [x] Replace the identity bundle dynamics with a first non-identity carrier
  law on the canonical three-generator carrier.
- [x] Replace the canonical bundle's constant-zero MDL placeholder with
  `mdlLevel` imported from the transported live `RGObservable`.
- [x] Replace the synthetic canonical carrier cycle with a first
  closure-derived dynamics law, namely the canonical bracket action
  `x ↦ [ CR , x ]`.
- [x] Strengthen the conserved quantity from gauge-only to the first
  defensible transported RG invariant under the closure-derived law:
  `Gauge × mdlLevel × motifClass`.
- [x] Next follow-up: determine whether the conserved quantity can be widened
  beyond `Gauge × mdlLevel × motifClass`. Current landed target:
  `Gauge × basinLabel × mdlLevel × motifClass × eigenShadow`, with
  `eigenShadow = (earth , hub)` as the first preserved quotient of
  `eigenSummary`.
- [ ] Current blocker on that widening: the minimal transported bridge is now
  explicit in
  `DASHI/Physics/Closure/CanonicalClosureShiftScheduleBridge.agda`
  (closure transport into the shift `shiftCoarse/step` schedule surface),
  and the first honest canonical closure→schedule bridge now lands on the
  smaller quotient `Gauge × basinLabel × motifClass`; but the stronger
  raw-eigen closure/schedule identification and the larger projected-charge
  bridge `Gauge × basinLabel × mdlLevel × motifClass × eigenShadow` are both
  formally obstructed on `CP`. The remaining gap is therefore not “any bridge”
  but a stronger canonical closure-to-shift bridge that survives those `CP`
  obstructions before retrying any wider `eigenSummary` lift.
- [ ] Reporter boundary reminder: until the closure-to-shift schedule map is
  strengthened beyond the current motif-level quotient, and the raw
  `heckeSignature`/`eigenSummary` plus projected-charge obstructions on `CP`
  are resolved, all public descriptions must stay on the representation-layer
  Hecke/FRACTRAN stack, the forced-stable inequality ladder, and the new
  motif-level closure→schedule bridge (see `Docs/HeckeRepresentationLayer.md`
  and the recent CHANGELOG entries).
- [x] New closure-target follow-up: define the maximal closure-invariant
  observable package explicitly on the current canonical carrier, rather than
  leaving the boundary as prose. `CanonicalClosureCoarseObservable.agda` now
  formalizes the maximal currently bridged package
  `Gauge × basinLabel × motifClass` as a reusable canonical projection
  surface, with factorization through the landed motif-level bridge and
  obstruction-facing wrappers for the wider `CP` failures.
- [ ] Paired classification follow-up: add an explicit obstruction/defect
  classification for the channels that fail to descend on `CP`, namely
  bridge-level `mdlLevel`, bridge-level `eigenShadow`, raw `eigenSummary`,
  and raw `heckeSignature`, so the repo distinguishes physical quotient data
  from defect/fibre data instead of leaving those failures as scattered local
  theorems.
- [x] Follow-up on that split: define the closure fibre over a coarse
  `Gauge × basinLabel × motifClass` class and state the first Hecke/eigen
  fibre-field surface on it, so the lost channels are not only called
  "obstructed" but are exposed as structured internal variation.
- [x] First fibre-law follow-up: state the thin fibre encoding explicitly
  (`Σ ClosureState (λ x → π x ≡ q)`) and lift the current Hecke/eigen
  observables to fibre-indexed fields on that carrier.
- [x] First control theorem on that fibre surface: prove a histogram-level or
  defect-compatibility law showing that Hecke/eigen variation on a fibre is
  constrained by the already-landed defect/correspondence machinery, rather
  than arbitrary.
- [x] Next fibre-law follow-up: strengthen the current canonical control law
  from forced-stable/illegal-count preservation on transported pair chambers
  to a richer factorization through the landed defect-profile or histogram
  carriers on each coarse closure fibre.
- [x] Check whether `eigenShadow` is already closure-quotient determined on
  the canonical coarse fibre before trying to factor it further: it is not.
  `CanonicalClosureFibreEigenShadowObstruction.agda` now gives a same-fibre
  witness (`CR` vs `CP`) showing `eigenShadowField` varies inside
  `Gauge × basinLabel × motifClass`.
- [ ] Next follow-up after that factorization landing: strengthen the current
  canonical control story from orbit-summary implications into explicit
  quotient/factor maps for the actual Hecke/eigen fibre fields through the
  landed defect-profile, histogram, or orbit-summary carriers, rather than
  only inheriting count-level bounds and entry-wise stability.
- [x] Next targeted fibre-law theorem: show whether `eigenShadowField`
  variation on the canonical coarse fibre is controlled by the landed
  defect-profile or orbit-summary carriers, instead of continuing to test it
  as a candidate descending observable. `CanonicalClosureFibreOrbitSummaryControl.agda`
  now proves the control theorem on the canonical carrier:
  equality of the `p2` orbit-summary coordinate forces equality of
  `eigenShadowField` on the coarse fibre.
- [x] First concrete detection check for that targeted theorem:
  `CanonicalClosureFibreOrbitSummaryControl.agda` now proves that the richer
  orbit-summary family already distinguishes the same-fibre `CR`/`CP` pair
  that witnesses `eigenShadow` variation.
- [x] Narrow that detection once: the same module now proves that the single
  `p2` orbit-summary coordinate already separates the same-fibre `CR`/`CP`
  witness pair.
- [x] Next strengthening step after that detection result: prove a more
  structural control statement relating `eigenShadowField` variation to a
  specific orbit-summary or defect-profile quotient, rather than only knowing
  that one concrete orbit-summary coordinate separates one concrete same-fibre
  pair. On the canonical carrier, `p2` is now that first structural control
  surface rather than only a witness separator.
- [x] Package that canonical `p2` control as an explicit quotient-facing
  factor law rather than only as an implication theorem.
  `CanonicalClosureFibreOrbitSummaryControl.agda` now exposes
  `P2EigenShadowFactorLaw` and the canonical instance
  `canonicalP2EigenShadowFactorLaw`.
- [x] Archive-guided follow-up: test whether `heckeSignature` or an
  arrow-separated delta quotient is the next honest widening target before
  retrying `eigenSummary`.
- [ ] Resulting follow-up: `heckeSignature` fails on the concrete `CP` branch
  under the current closure-derived law, so the next widening attempt should
  target a coarser RG quotient or a stronger/noncanonical transport family,
  not another direct raw-Hecke lift; the first successful quotient is now
  `eigenShadow = (earth , hub)`, and the raw-`eigenSummary` obstruction is
  now explicit as `canonicalEigenLevel-CP-obstructed`; see
  `Docs/HeckeRepresentationLayer.md`.
- [x] First canonical fibre-control theorem for `heckeField`:
  `CanonicalClosureFibreOrbitSummaryControl.agda` now proves
  `p2-controls-hecke-on-canonical-fibre`, so equality of the `p2`
  orbit-summary coordinate already forces equality of `heckeField` on the
  canonical coarse fibre.
- [x] Next follow-up after that `heckeField` control result: package the
  corresponding explicit factor map or quotient-facing law, then test whether
  the same control shape lifts noncanonically.
  `CanonicalClosureFibreOrbitSummaryControl.agda` now exposes
  `P2HeckeFactorLaw` and the canonical instance
  `canonicalP2HeckeFactorLaw`.
- [x] Broaden the current bridge/profile replay beyond the tiny canonical
  `CR/CP/CC` carrier using the existing observable-transport and
  prime-compatibility tower. `ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda`
  now exercises that lift on full `ShiftContractState`, recovering the same
  witness-level bridge and `illegalCount-chamber ≤ forcedStableCount-hist`
  surface on a broader carrier without changing the current honesty boundary.
- [x] Next generalization step after that replay: lift the new coarse package
  onto a broader noncanonical carrier, instead of keeping it only on the tiny
  canonical fibre. `ShiftContractCoarseObservable.agda` now packages the same
  coarse observable surface on `ShiftContractState` and factors it through the
  existing observable-transport witness and bundle observable surfaces.
- [ ] Next generalization step after that noncanonical coarse lift: lift the
  new fibre-control story itself beyond the tiny canonical carrier, starting
  with the nearest honest analogue of the `p2` control surface on
  `ShiftContractState`. The prerequisite vocabulary is now landed:
  `ShiftContractCoarseFibre.agda` defines the thin noncanonical coarse fibre
  and `ShiftContractCoarseFibreFields.agda` lifts the first noncanonical
  Hecke/eigen/prime/count/orbit-summary fields onto it. The first direct
  obstruction is now explicit as well:
  `ShiftContractNoncanonicalP2ControlObstruction.agda` shows the current
  coarse package is too weak for a canonical-style `p2` factor law, so the
  next positive attempt must strengthen the invariant package rather than
  reuse `π-max` unchanged. That cheapest strengthening is now formalized as a
  reusable normalized package in
  `ShiftContractMdlLevelCoarseObservable.agda` and
  `ShiftContractMdlLevelCoarseFibre.agda`; the corresponding stronger fibre
  vocabulary is now in `ShiftContractMdlLevelCoarseFibreFields.agda`. A first
  narrow positive theorem is now landed in
  `ShiftContractMdlLevelP2ControlAttempt.agda`: equality of the package
  determines both the `mdlLevel` coordinate and the old coarse observable.
  `ShiftContractMdlLevelCounterexampleAudit.agda` now also records that the
  original coarse obstruction pair is no longer the active blocker on that
  stronger surface. So the next honest step is no longer candidate search and
  no longer just "prove anything positive"; it is to find the new witness or
  the first genuine prime-image control theorem on
  `mdlLevel × π-max`. The intermediate orbit-summary step is now landed in
  `ShiftContractMdlLevelOrbitSummaryControlAttempt.agda`:
  prime equality on the mdl-level fibre already forces equality of
  `orbitSummaryField p2`, and `ShiftContractMdlLevelP2PrimeBridge.agda`
  already packages the resulting full orbit-summary coordinate consequences.
  `ShiftContractMdlLevelPrimeImageSubfamilyAttempt.agda` now also gives the
  first singleton-subfamily prime-image theorem, while
  `ShiftContractMdlLevelPrimeImageSubfamilyRefinement.agda` wraps the current
  in-tree explicit witnesses into a two-point family whose mixed case is
  already excluded at `π-mdl-max`.
  `ShiftContractMdlLevelWitnessSearchAudit.agda` packages the bounded
  same-carrier search state explicitly: among the current in-repo
  `ShiftContractState` witnesses, no fresh equal-`π-mdl-max` /
  unequal-prime-image pair has yet been recovered.
  `ShiftContractMdlLevelWitnessSourceAudit.agda` now packages that same
  exhaustion boundary at the witness-source level.
  `ShiftContractMdlLevelExplicitStateSearchAudit.agda` closes the obvious
  direct explicit-state pool on the actual `ShiftContractState` carrier:
  the one-hot and neg/pos tail candidates are now recorded as checked without
  yielding a fresh witness.
  Meanwhile
  `ShiftContractMdlLevelChi2WitnessAudit.agda` records that the current chi2
  witness pool is carrier-mismatched for this seam. The immediate remaining
  gap is therefore prime-image control itself beyond that trivial subfamily,
  with
  `eigenShadow × π-max` now packaged as the immediate fallback in
  `ShiftContractEigenShadowP2ControlCandidate.agda`; and
  `ShiftContractEigenShadowOrbitSummaryObstruction.agda` shows that this
  fallback still does not control the canonical `p2` orbit-summary key.
  `ShiftContractEigenShadowOrbitSummaryControlAttempt.agda` now packages that
  same failure as a direct no-go control schema, so the fallback is no longer
  merely unproven; it is blocked at the canonical `p2` seam. The problem is
  therefore no longer another nearby widening attempt. It is now a same-carrier
  source-generation problem: the first same-carrier triadic family is now
  landed in `ShiftContractTriadicFamily.agda`, and a broader support-width-two
  cyclic family is now landed in
  `ShiftContractAnchoredTriadicFamily.agda`. `ShiftContractDenseTriadicFamily.agda`
  now extends that positive cyclic branch to support width three.
  `ShiftContractParametricTriadicFamily.agda` now packages that cyclic branch
  itself as a normalized width-indexed surface.
  `ShiftContractStateFamily.agda` now adds the matching repo-native family
  schema on the actual `ShiftContractState` carrier, with the live coarse
  surface `π-mdl-max`, the transported prime image, a generic same-carrier
  family record, and a cyclic-3 specialization instantiated at support
  widths 1, 2, and 3.
  `ShiftContractTriadic3CycleInstance.agda` now also lands the first fully
  concrete balanced tail-cycle inhabitant of that schema on the live carrier:
  with head fixed at `pos`, the cycle
  `(pos , zer , neg) -> (zer , neg , pos) -> (neg , pos , zer)` preserves
  `π-mdl-max` and still splits pairwise at the transported prime image.
  `ShiftContractBalancedComposedFamily.agda` now proves that the same
  balanced cycle is also recovered by the composed-generator lane from
  `fullSupport` plus varying cut and neg-restore masks.
  `ShiftContractParametricTrajectoryCompositionFamily.agda` now packages the
  successful same-carrier 3-state prefixes into one normalized
  generator-class surface: explicit cyclic, concrete balanced cyclic, dense
  composed, balanced composed, and anchored trajectory.
  `ShiftContractGeneratorFourthStepBoundary.agda` now adds the first reusable
  live fourth-step classifier above that surface: anchored trajectory and
  explicit width-two certify fourth-step exits, balanced explicit/composed
  cycles certify exits into the anchored branch, and explicit width-three
  plus dense composed certify one more same-fibre live step.
  `ShiftContractMixedScaleTrajectoryFamily.agda` now packages the mixed-scale
  trajectory branch above that surface too: dense support cascade is the
  canonical stay-then-exit family, and full-support cascade is the canonical
  immediate-exit family.
  `ShiftContractGeneratorTaxonomy.agda` now connects the normalized prefix
  and mixed-scale branches into one higher-level taxonomy: prefix classes
  carry explicit fourth-step shape labels, while mixed-scale classes carry
  their own normalized trajectory families.
  `ShiftContractCollapseTime.agda` now turns that taxonomy into a coarse
  collapse-time observable, and `Ontology/Hecke/DefectOrbitCollapseBridge.agda`
  now adds the first honest Hecke-side lower-bound bridge from collapse class
  to defect/orbit data through representative live states.
  `Ontology/Hecke/DefectOrbitCollapsePressure.agda` now packages the next
  coarse Hecke-side layer above that bridge as a named pressure
  classification plus representative `p2` pressure summaries, and
  `Ontology/Hecke/DefectProfileCollapseFactorization.agda` now lands the
  first explicit factorization scaffold from collapse time through that
  coarse defect-pressure summary.
  `Ontology/Hecke/StaysOneMoreStepRepresentativeComputations.agda` now makes
  the stay-class representatives explicit, and
  `Ontology/Hecke/DefectOrbitPressureOrder.agda` now adds the first ordered
  pressure theorem between the coarse collapse classes.
  The next stronger numeric/order and factorization targets are now also
  explicit as guarded theorem surfaces rather than only as prose, and
  `Ontology/Hecke/ImmediateExitRepresentativeComputations.agda` now mirrors
  the stay-class computation package on the immediate-exit side.
  `Ontology/Hecke/ExitToAnchoredRepresentativeComputations.agda` now makes
  the intermediate branch explicit too, and the current exact `p2` count
  surface is now known on the classified prefix branch:
  immediate/anchored classes sit at `15`, while the current stay branch
  splits as `explicitWidth1 ↦ 2` and
  `explicitWidth3, denseComposed ↦ 15`.
  `Ontology/Hecke/StaysVsImmediateRepresentativeOrder.agda` now discharges
  the current certified stay-vs-immediate and anchored-vs-immediate orbit
  order witnesses directly from those exact counts.
  `Ontology/Hecke/CertifiedRepresentativePersistence.agda` now adds the
  first genuinely collapse-free numeric quotient on that current certified
  representative set: the Hecke-side `forcedStableCountOrbitP2` count
  determines a small persistence tier, with `explicitWidth1` reduced and the
  rest of the current certified set saturated. And
  `Ontology/Hecke/DefectProfileCollapseFactorization.agda` now records the
  corresponding certified representative orbit-count factorization.
  `Ontology/Hecke/CertifiedRepresentativeOrbitSummaryPersistence.agda` now
  lifts that same certified quotient through the full Hecke-side
  `DefectOrbitSummary` by projecting its `forcedStableCount` field.
  `Ontology/Hecke/DefectPersistenceRefinement.agda` now turns that certified
  quotient into the smallest honest refinement law above collapse time:
  `explicitWidth1` is `lowStay`,
  `explicitWidth3` and `denseComposed` are `highStay`,
  and the current anchored/immediate representatives are `nonStay`.
  So the active Hecke-side gap is no longer "does collapse time determine
  pressure?" It does not. The active gap is now to lift this
  `(collapseTime, stayRefinement)` law beyond the current certified set, or
  to split the still-saturated side with a richer Hecke-side summary than the
  current `forcedStableCount`-only persistence tier.
  `Ontology/Hecke/SupportCascadePersistence.agda` now gives the first such
  extension beyond the original certified finite quotient:
  the mixed-scale `supportCascade` class is a further `staysOneMoreStep`
  case with exact `forcedStableCount = 15` at `p2`.
  `Ontology/Hecke/CertifiedSaturatedForcedStableCollapse.agda` now also
  records the opposite boundary explicitly: every current saturated certified
  representative already has `forcedStableCount = 15`, so that field cannot
  split the saturated side any further.
  `Ontology/Hecke/CurrentGeneratorPersistenceRefinement.agda` now lifts the
  positive refinement law to the full current generator taxonomy, and
  `Ontology/Hecke/CurrentSaturatedForcedStableCollapse.agda` lifts the
  matching negative `forcedStableCount = 15` obstruction to that same scope.
  `Ontology/Hecke/CurrentSaturatedOrbitSummaryCollapse.agda` now strengthens
  that obstruction one rung further:
  the whole current `DefectOrbitSummary` at `p2` already collapses to the
  same fully stable summary on the full saturated current taxonomy.
  The next Hecke-side step is therefore narrower:
  either keep extending the `(collapseTime, stayRefinement)` law beyond the
  current landed taxonomy if new generator classes appear, or find a richer
  Hecke-side summary/package than the currently landed `DefectOrbitSummary`,
  because the whole current orbit summary is now exhausted on the saturated
  side of the whole current taxonomy. Treat `15` as an emergent saturated
  value of the present `p2` summary surface, not as a primitive constant:
  the next structural test is whether that `15` decomposes into a triadic
  core plus an interface/coupling contribution, for example a candidate
  `9 + 6` split, or factorizes more naturally as `3 × 5` with triadic sectors
  times symmetry-reduced local classes, rather than assuming `15` itself is
  fundamental.
  `Ontology/Hecke/DefectOrbitSummaryRefinement.agda` and
  `Ontology/Hecke/ForcedStableCountDecomposition.agda` now exist as the first
  implementation surfaces for that test, and
  `Ontology/Hecke/TriadIndexedDefectOrbitSummaryRefinement.agda` now adds the
  next candidate refinement above the flat histogram as a triad-indexed
  `3 × 5` surface. Their Agda checks belong on the long-compute list rather
  than the interactive validation loop.
  The prefix-side `boundaryUnknown` seam is now closed as well:
  `explicitWidth1` stays in the same `π-mdl-max` fibre for one more live
  step.
  `ShiftContractComposedFamily.agda` now adds the first same-carrier
  compositional generator surface: a ternary interaction rule over
  base/cut/restore states that already recovers the dense width-three cyclic
  branch exactly.
  `ShiftContractAnchoredTrajectoryFamily.agda`
  now also lands the first live-step family on the same seam, so the next
  step is to strengthen the new collapse-to-pressure dictionary beyond the
  current representative-state lower-bound bridge, coarse pressure scaffold,
  pressure-order theorem, exact current `p2` count surfaces, and current
  discharged representative-order witnesses, and the new certified
  representative orbit-count quotient, and the richer certified
  orbit-summary factorization, ideally by lifting those quotients beyond the
  current certified set or by replacing them with a Hecke-determined
  persistence/defect-summary theorem that also separates the current
  saturated classes;
  failing that, extend that higher-level taxonomy beyond the current
  explicit/composed/anchored/mixed-scale cases or add a genuinely new
  `ShiftContractState` generator class above the current hand-written,
  balanced-cycle, and first composed finite families, or to a richer parametric
  trajectory/composition family whose `π-mdl-max` image can be tested
  against transported prime-image variation.
  `ShiftContractSupportCascadeTrajectory.agda` now also lands the first
  mixed-scale cascade on the same seam.
  `ShiftContractFullSupportTrajectory.agda` adds a distinct full-support seed
  whose live trajectory cascades `4 -> 3 -> 2 -> 1`.
  `ShiftContractTailPatternTrajectoryObstruction.agda`
  now also closes the obvious negative dynamic branch: direct neg/pos
  tail-pattern seeds leave the `π-mdl-max` fibre immediately under the live
  step. Do not spend more time on direct tail-pattern or immediate
  `eigenShadow × π-max` retries unless a new generating surface justifies
  them.
- [ ] Next noncanonical control step: add at least one genuinely new
  `ShiftContractState` family generator beyond the landed explicit cyclic and
  first live-step trajectory families, and test whether it yields either: a
  nontrivial same-carrier
  prime-image control theorem on `mdlLevel × π-max`, or a fresh
  equal-`π-mdl-max` / unequal-prime-image witness.
- [ ] Constrain that next noncanonical family generator explicitly before
  implementing it:
  require moves in
  `ker(π-mdl-max) \ ker(primeImage)`,
  treat cyclic/triadic structure as the current positive pattern,
  do not exclude one-hot or anchored support-width-two patterns a priori,
  and prefer that over another pair-generated probe unless
  a new theorem surface justifies a smaller witness.
- [x] Add a first local reverse-Hecke surface on the representation layer,
  explicitly separate from the canonical conserved witness.
- [x] Add a first local equivalence/setoid plus quotient-facing Hecke surface
  on the representation layer, explicitly separate from the contractive
  closure bundle.
- [x] Instantiate
  `Ontology/Hecke/ReverseRepresentation.agda`
  and `Ontology/Hecke/QuotientRepresentation.agda`
  on a first concrete prime-address family.
- [ ] Next Hecke representation-layer upgrade:
  connect the current prime-lane bumping / local prime-flow transport in
  `Ontology/Hecke/FactorVecInstances.agda`
  and the new signed transfer law in
  `Ontology/Hecke/FactorVecSignedTransport.agda`
  to a more meaningful prime-address family or scan pipeline; the first
  coarser agreement quotient is now landed as the `SupportMask` class carrier,
  and the current signed transport no longer descends honestly to that coarse
  quotient. A stronger finite multiplicity-saturation quotient was also tried
  and backed out: the decrement boundary still loses exact count information.
  This is now proved in general for positive bounded saturation quotients in
  `Ontology/Hecke/SignedTransportObstruction.agda`.
  The support-mask obstruction is now formalized in
  `Ontology/Hecke/SignedTransportObstruction.agda`. The first signed scan/motif
  attachment is now landed in `Ontology/Hecke/FactorVecSignedScan.agda`, and
  the first mode-labelled multi-lane interface plus `FactorVec` inhabitant are
  now landed in `Ontology/Hecke/MultiLaneSignedTransport.agda` and
  `Ontology/Hecke/FactorVecMultiLaneTransport.agda`. The first exact chamber
  carrier is now also landed in `Ontology/Hecke/TransportChambers.agda` and
  `Ontology/Hecke/FactorVecTransportChambers.agda`, so the next step is to
  compare or cluster signed legality/signature classes inside those exact
  chambers rather than guessing another coarse quotient blindly. The first
  defect-comparison layer is now landed in
  `Ontology/Hecke/FactorVecMultiLaneDefects.agda`, so the next sharp seam is
  to relate exact chamber agreement to restrictions on defect classes. The
  first chamber-to-defect restriction is now landed in
  `Ontology/Hecke/FactorVecChamberDefectRestrictions.agda`, so the next seam
  is to strengthen beyond illegal-mode stability into histogram-level chamber
  laws on the defect correspondence fiber. The same illegal-mode restriction
  is now also lifted to the full profile carrier in
  `Ontology/Hecke/FactorVecChamberDefectProfileCorrespondence.agda`, forcing
  zero drift, fixed motif, and `Stable` defect on illegal entries across an
  exact chamber. Exact legality-signature chambers, finite defect histograms,
  and chamber-stability for the forced-stable / illegal count are now all
  landed, and a concrete obstruction now shows that the full defect histogram
  is not chamber-invariant on exact legality data alone. So the next honest
  steps are:
  test chamber or orbit-style stability for fuller defect profiles,
  and identify which components of the new orbit-summary layer remain stable.
  The first such component is now only partially controlled:
  the orbit-summary `forcedStableCount` field dominates the already-landed
  histogram-layer forced-stable / illegal count, but is not collapsed to it.
  So the remaining work is still on the other orbit-summary components, and on
  determining whether this first component has a stronger chamber or orbit law
  than the current lower bound, since the full orbit summary is still not
  determined by the same legality-signature data alone. Only after that should it be treated as
  a real orbit carrier.
  The immediate bridge follow-up is the forced-stable transfer ladder:
  the abstract ladder surface is now landed in
  `Ontology/Hecke/ForcedStableTransferBridge.agda`,
  packaging:
  `illegalCount_chamber` chamber constancy,
  an assumed bridge inequality
  `illegalCount_chamber(x,p) ≤ forcedStableCount_hist(S x,p)`,
  and the derived orbit bound
  `illegalCount_chamber(x,p) ≤ forcedStableCount_orbit(S x,p)`.
  A first concrete canonical inhabitant is now also landed in
  `DASHI/Physics/Closure/CanonicalForcedStableTransferBridgeInstance.agda`
  using
  `canonicalTransportState -> canonicalShiftHeckeState -> shiftPrimeEmbedding`,
  but its chamber count is still defined from the transported shift image, so
  the next proof step is to inhabit the smaller
  `Ontology/Hecke/ChamberToShiftWitnessBridge.agda` surface with a real
  closure-native illegal mask and witness, replacing that transported/reflexive
  count before attempting the compatibility equality refinement. A first
  canonical inhabitant of that smaller surface is now landed in
  `DASHI/Physics/Closure/CanonicalChamberToShiftWitnessBridgeInstance.agda`,
  and it now uses a closure-native compatibility profile on the canonical
  three-generator carrier. That profile is now factored through
  `DASHI/Physics/Closure/PrimeCompatibilityProfile.agda`.
  Broader transported families can now also target the same witness surface via
  `DASHI/Physics/Closure/TransportedPrimeCompatibilityProfile.agda`, and
  bundle-level closure carriers can do the same through
  `DASHI/Physics/Closure/ObservableTransportPrimeCompatibilityProfile.agda`.
  The transported route is now also exercised concretely in
  `DASHI/Physics/Closure/CanonicalTransportedPrimeCompatibilityProfileInstance.agda`,
  where it agrees with the closure-native prime embedding on `CR/CP/CC`.
  A first broader concrete carrier is now also landed in
  `DASHI/Physics/Closure/ShiftGeoVPrimeCompatibilityProfileInstance.agda`,
  instantiating both the witness-level inequality and the orbit-side forced-
  stable bridge on the full `ShiftGeoV` state family.
  A second broader concrete family is now also landed in
  `DASHI/Physics/Closure/ShiftContractStatePrimeCompatibilityProfileInstance.agda`,
  lifting the same bridge surfaces to full shift execution-contract states via
  `canonicalShiftHeckeState -> shiftPrimeEmbedding`.
  The bundle-level `ObservableTransportWitness` route is now also exercised
  concretely in
  `DASHI/Physics/Closure/CanonicalObservableTransportPrimeCompatibilityProfileInstance.agda`,
  using the canonical abstract gauge/matter bundle carrier together with
  `canonicalShiftHeckeState -> shiftPrimeEmbedding`.
  The next step is therefore no longer “find any broader carrier”, and no
  longer “exercise the bundle lift once”, but instead either:
  widen the bundle-level lift beyond the canonical leaf, or widen the canonical
  AGMB continuum lane from its first honest projected target. The continuum
  witness now preserves a projected continuum observable
  (`Gauge × basinLabel × mdlLevel × motifClass × eigenShadow`) through an
  explicit carrier-side scaling map, where
  `eigenShadow = (earth , hub)` is the first preserved quotient of
  `eigenSummary`, so the canonical instance compiles again; any stronger
  continuum target still conflicts with the current closure-derived law because
  `canonicalRGObservableOf` is not preserved on the `CP` branch.
  Compressed chamber quotients, orbit classes, weighted correspondences, and
  spectral operators remain open rather than implied by the current exact
  chamber surface.
- [x] Add a first genuine finite correspondence class and sum-over-fiber
  Hecke operator on the representation layer, separate from the transport
  diagnostic.
- [x] Add a first scan/defect-derived finite correspondence and averaging
  operator, so correspondence generation is no longer only marked-prime based.
- [x] Lift the defect-derived correspondence to full finite defect profiles and
  add the first chamber-side restriction directly on correspondence entries.

- [x] Start a separate DNA-first supervoxel lane with a local note and Agda
  carrier rather than leaving the archive discussion external only.
- [x] Add a first DNA 4/16/64/256 carrier and chemistry quotient surface under
  `Ontology/DNA/`.
- [ ] Next DNA supervoxel step:
  strengthen the concrete `DNA256` chemistry screen beyond the current local
  repeat/complement ban; the bounded span-2 complement screen, 4-window
  GC-extreme ban, 4-window reverse-complement palindrome ban, and bounded
  6-window hairpin-style law are now landed, so the next step is a longer-
  window reverse-complement, stronger GC-window, or richer hairpin/dimer law.
- [x] Promote the current phase-aware shift universality result into a
  realization-independent offset theorem surface above the current canonical
  shift instance.
- [x] Add an explicit `ProjectionDeltaCompatibility` theorem surface above the
  current shift RG schedules and instantiate it from the live
  `shiftCoarse` / `shiftCoarseAlt` cone-preserving pair.
- [x] Connect the already-landed offset-universality surface into the abstract
  gauge/matter bundle layer.
- [x] Lift the new projection/Δ compatibility surface into the abstract
  gauge/matter bundle layer and expose the canonical converted witness there.
- [x] Add a first quotient-sensitive canonical bundle projection/Δ witness over
  the transported live `RGObservable`, using the shift RG observable quotient
  instead of plain equality on the full bundle observable.
- [x] Add a first transport-attached target-side projection/Δ witness on the
  live shift carrier, so the canonical bundle exports the actual shift-side
  schedules and cone transport lemmas through the existing transport layer.
- [x] Generalize that transport-attached witness into a reusable
  `TransportedProjectionDeltaWitness` theorem surface in the abstract bundle
  layer.
- [x] Inhabit the transported projection/Δ witness surface with a second live
  shift phase family beyond the first base schedule pair.
- [ ] Next follow-up: move beyond the current live shift target families and
  inhabit the transported projection/Δ witness surface with a genuinely
  noncanonical transport/state family.
- [ ] Reassessed follow-up: adding more canonical transported phase families is
  now lower value than either:
  - inhabiting the transported projection/Δ surface with a genuinely
    noncanonical target family, or
  - strengthening the closure-derived dynamics law so more RG channels can
    honestly survive.
- [x] Make transported projection/Δ compatibility part of the abstract
  recovery theorem surface itself instead of leaving it only as a parallel
  bundle export.
- [x] Promote the alternate transported phase family into the abstract
  recovery theorem surface too, so the theorem is no longer tied to a single
  target-side schedule pair.
- [x] Replace the nominal continuum witness with a theorem-bearing
  `ContinuumLimit`-style record carrying scaling and
  invariant-preservation obligations.
- [ ] Next follow-up: strengthen the current canonical continuum inhabitant so
  its limit carrier/scaling map go beyond the current first quotient-like
  carrier given by the transported `RGObservable`.
- [ ] Archive-guided follow-up: use the current physical bridge threads
  (`Branch · Topology and MDA/MDL` and the light-transport / phase-sync lane)
  to define a more physical scaling object than a finite RG quotient alone.

## Track H — Archive-Guided Physics Closure (2026-03-31)

Priority bucket: `P0/P1 governance`

- [x] Record the current high-signal archive coverage map in
  `Docs/PhysicsArchiveCoverageMap.md`.
- [x] Record the resolved local DB thread metadata and decisions in
  `COMPACTIFIED_CONTEXT.md`.
- [ ] Keep the next P0 theorem work pinned to the archive-backed priority
  order:
  derived dynamics law,
  realization-independent projection/delta theorem,
  signature forcing / execution-delta interface,
  continuum scaling law.
- [ ] Treat the wavefield / phase-synchronization material as a P1 physical
  bridge lane unless and until it lands as a local theorem or prototype.
- [ ] Keep algebraic-carrier / moonshine-adjacent archive material off the
  critical physics path unless it directly reduces one of the P0 proof gaps.

## Documentation Follow-Up

Priority bucket: `P2`

- [x] Add a compact repo note separating optical colour, perceptual colour, and
  QCD colour in Dashi language, with explicit claim boundaries.
- [ ] If colour language is reused in later physics/representation notes, keep
  it aligned with `Docs/ColourInDashi.md` so quotient/reconstruction claims do
  not get blurred together.
- [x] Add a compact repo note fixing the claim boundary between a triadic
  3-sector carrier and actual `SU(3)`-like internal symmetry.
- [x] Add a compact repo note and toy implementation for the stronger musical
  symmetry target: MDL/compression plus contraction, without explicit symmetry
  reward.
- [ ] If the musical MDL toy becomes a maintained research surface, promote its
  current compression proxy into a more explicit code-length model and compare
  multiple symmetry operators on the same basin protocol.

## Track M — Moonshine Prime Proof Program (2026-03-30)

Priority bucket: `P1`

- [x] Formalize the observed moonshine-prime object:
  quotient map, spectrum, basin count, factorization surface, and
  eigen numerator/denominator schema.
- [x] Define the non-accident / null-model suite and explicit stop condition.
- [x] Document the strongest current algebraic carrier/factorization
  candidates.
- [x] State the canonical prime-selection law and the proof obligations needed
  before any Ogg/Monster comparison.
- [x] State the legal moonshine-match test forms.
- [x] State the promotion gate from prime coincidence to modular objects.
- [x] Consolidate the staged proof program in
  `Docs/MoonshineProofChecklist.md`.
- [x] Make the observed object executable in one lane-local
  script or data schema, so the null models and prime-selection property can be
  tested against a concrete artifact instead of notes alone.
- [x] Attach that schema to a real repo-native emitted state source
  (starting with `scripts/examples/near_miss_state.json`) instead of relying on
  hand-written sample payloads.
- [x] Add a moonshine-native source-family manifest so the proof program stops
  borrowing photonuclear example states and instead points at
  `DASHI/Physics/Moonshine` trace/graded/twined families.
- [x] Build the first moonshine-native adapter from
  `FiniteTwinedShellTraceShift.agda`, even if it only lifts the explicit
  orientation-prime hook and family provenance before full trace counts are
  extracted.
- [x] Validate that first orientation-prime adapter end to end through
  `moonshine_prime_object.py` and keep the emitted state explicitly marked as
  `orientation_prime_only` until stronger trace fields are sourced from a
  report or bundle surface.
- [x] Next follow-up: extract stronger finite-twined trace fields from a
  report or bundle surface so the moonshine-native emitted state is no
  longer limited to the explicit orientation-prime hook.
- [x] Keep the current strengthened trace fields auxiliary until there is a
  documented lift from report/bundle metadata into the normalized
  moonshine-prime observable.
- [x] Next follow-up: define and implement the first principled lift from
  finite-twined report metadata into the normalized observable instead of
  leaving it in `traceReport`.
- [ ] Next follow-up: widen that first principled lift beyond report counts and
  labels so the normalized observable is fed by richer finite-twined structure
  than verdict-slot/cardinality metadata alone.
- [x] Implement the null-model harness and stop rule before any
  Monster comparison logic is coded.
- [ ] Next follow-up: widen the schema-level null harness into the full
  research-target nulls (matched basin graphs and PCA/control over real derived
  artifacts) once the observed-object pipeline is attached to real emitted
  states.

## Track N — Merge-Prep Nix / Zkperf Surface (2026-03-23)

Priority bucket: `P1`

- [x] Import the PR `#1` Agda source patchset that adds
  `Kernel/KAlgebra.agda`, `Monster/MUltrametric.agda`, `Moonshine.agda`,
  `MoonshineEarn.agda`, `JFixedPoint.agda`, `PerfHistory.agda`, and
  `perf_da51.py`, then rewire the existing modules to those names.
- [x] Add a local `flake.nix` that mirrors the existing authoritative GitHub
  typecheck route through `DASHI/Everything.agda`.
- [x] Add a second Nix smoke-check surface for merge-relevant standalone roots
  plus recursive `Kernel/`, `Monster/`, and `Verification/` modules.
- [x] Add a local `dashi-agda.agda-lib` so Nix/dev-shell tooling has an
  explicit library surface to point at.
- [x] Make local `agda-record-all` recurse over the same merge-prep target
  surface instead of top-level files only.
- [x] Keep demo DA51/zkperf JSONL artifacts, if merged, documented as sample
  witness outputs rather than canonical reproducibility fixtures.
- [x] Generate and keep a local `flake.lock` for the merge-prep Nix surface.
- [x] Follow-up after the writable-source fix:
  rerun `nix flake check`, `nix build .#check`, and
  `nix build .#merge-smoke` end to end and record the final outcome.
- [x] Merge-prep Nix / zkperf surface is complete; return active attention to the
  physics closure spine and tail-boundary follow-ups below.

## Track U — Physics Closure Spine Completion (2026-03-12)

Priority bucket: `P0`

- [x] Execute checklist in `Docs/PhysicsClosureImplementationChecklist.md` in
  strict order.
- [x] Keep contraction→quadratic uniqueness transport centralized in
  `ContractionForcesQuadraticStrong`.
- [x] Keep profile forcing surface narrow:
  `ConeArrowIsotropyForcesProfile` + shift instance only.
- [x] Upgrade `DecimationToClifford` from interface shell to theorem-bearing
  factorization surface.
- [x] Convert `PhysicsClosureFull` from supplied-field record to
  theorem-derived assembly where possible.
- [x] Eliminate assumption-first canonical seams from
  `PhysicsClosureInstanceAssumed` and canonical constraint-closure route.
- [x] Enforce canonical export path in:
  `CanonicalStageC`, `AxiomSet` (`AxiomLaws`), and `Everything`.
- [x] Keep the remaining theorem-checklist / bridge-package surface on the direct core-witness route instead of converting the full closure through the constructor theorem.

Progress note:
the legacy assumed closure instance is now kept out of the public
`PhysicsClosureSummary` and `Everything` export surfaces; the compatibility
module remains on disk, but the canonical path no longer publicly re-exports
it.
Progress note:
the canonical quadratic theorem constructor now delegates to the strong
package’s canonical identity witness instead of reconstructing the split
package inline, so the uniqueness transport seam is a little more centralized.
Progress note:
the external full-closure and provider-based constructors have been renamed to
legacy adapters, so the canonical naming no longer suggests that the
outside-wired routes are authoritative.
Progress note:
`physicsClosureFullFromCoreWitness` now assembles the canonical full closure
directly from the core witness, rather than bouncing through the legacy
external adapter.

## Cleanup / Consolidation

- Runtime policy:
  do not run `PhysicsClosureValidationSummary.agda` in routine validation until
  runtime bounds are acceptable (currently ~1.25 hours).
- [x] Closure hygiene policy:
  `scripts/run_closure_hygiene.py` and
  `scripts/run_closure_hygiene.sh` now skip learned `heavy` and
  `aggregator` tasks by default, with an explicit `--include-heavy` flag for
  aggregate integration runs.
- Canonical pipeline policy:
  use `Docs/ClosurePipeline.md` as the single Stage C claim path, and label new
  closure modules as `canonical`, `supporting`, or `experimental`.
- Make grouped wave-regime ladder modules authoritative for new imports:
  - `Closure/Algebra/WaveRegime.agda`
  - `Closure/Recovery/WaveRegime.agda`
  - `Closure/Consumers/WaveRegime.agda`
  - `Moonshine/Reports/WaveRegime.agda`
- Rewire canonical Stage C bundles and repo-facing summaries to use grouped
  ladder modules instead of direct per-rung imports where practical.
- Keep per-rung modules as compatibility wrappers only.
- Keep top-level compile green while doing the refactor.

## Base369 Normalization Hardening

Priority bucket: `P1`

- [x] Add closed-form cyclic constructors:
  `fromTriIndex`, `fromHexIndex`, `fromNonaryIndex`.
- [x] Add closed-form cyclic operators in `Base369.agda`:
  `triXor-closed`, `hexXor-closed`, `nonaryXor-closed`.
- [x] Prove triadic bridge first:
  `triXor-spin-correct : triXor-spin a b ≡ triXor a b`.
- [x] Keep existing recursive `spin`-based operators as compatibility
  definitions until downstream imports switch.
- [x] Follow-up: swap canonical exports to closed-form operators now that tri,
  hex, and nonary correctness bridges are in place.
- [x] Add first `abstract` barriers around heavy closure theorem-bundle
  summary aliases in `PhysicsClosureValidationSummary`.
- [x] Follow-up: extend `abstract` barriers to
  `CanonicalStageCTheoremBundle` and `CanonicalStageCSummaryBundle`, then
  re-measure targeted closure-summary typecheck time.
- [x] Next follow-up: expand the same pattern to remaining heavy
  moonshine/regime aliases in `PhysicsClosureValidationSummary` and re-check
  targeted bundle modules.
- [ ] Next follow-up: re-run direct
  `PhysicsClosureValidationSummary.agda` timing/validation when a longer
  runtime budget is available.
- [x] Pipeline enforcement: tag existing closure-relevant modules in docs as
  `canonical` / `supporting` / `experimental` and remove ambiguous duplicates
  from repo-facing claims.
- [x] Keep `Docs/ClosurePipeline.md` label registry current whenever new
  closure modules are added or promoted. (Refreshed 2026-03-25 with split/
  parallelogram route, spin/Dirac bridge, PhysicsClosureFull, and
  QuadraticFromProjection classification.)
- [x] Add canonical quadratic-to-Clifford bridge theorem module:
  `DASHI/Physics/Closure/QuadraticToCliffordBridgeTheorem.agda`, deriving a
  canonical bilinear form from normalized quadratic output
  (`ContractionForcesQuadraticStrong.uniqueUpToScaleWitness`) and exposing a
  universal-property seam on the theorem surface.
- [x] Wire canonical contraction-to-Clifford bridge exports to include the new
  quadratic-to-Clifford theorem surface in
  `CanonicalContractionToCliffordBridgeTheorem`.

## Track S — Canonical Spine Simplification

Priority bucket: `P0`

- [x] Declare the canonical closure spine in theorem-bundle and summary docs:
  `ProjectionDefect → ProjectionDefectSplitForcesParallelogram
  → ProjectionDefectToParallelogram → QuadraticForm
  → ContractionForcesQuadraticStrong → ContractionForcesQuadraticTheorem
  → CausalForcesLorentz31 → ContractionQuadraticToSignatureBridgeTheorem
  → QuadraticToCliffordBridgeTheorem → ContractionSignatureToSpinDiracBridgeTheorem
  → CliffordToEvenWaveLiftBridgeTheorem → PhysicsClosureFull`.
- [x] Classify quadratic/signature parallel routes as one of:
  `alternative`, `validation`, `experimental`.
- [x] Rewire canonical Stage C and closure summaries so canonical claims do not
  depend on `QuadraticEmergence` / `QuadraticFormEmergence` as required steps.
- [x] Keep `ProjectionDefectToParallelogram` and
  `ContractionForcesQuadraticStrong` as canonical bottleneck bridge modules.
- [x] Keep a single seam registry on canonical modules only; remove duplicated seam
  placeholders from non-canonical derivation surfaces.

## Track T — Dynamical / Theorem Closure

Priority bucket: `P0`

Open physics-side requirements that remain genuinely unresolved:

- natural physical dynamics law
- conserved physical quantity with clear interpretation
- explicit continuum-limit theorem
- realization-independent proof
- full gauge/matter recovery as theorem rather than program

Current `P0` docs lane status:

- [x] Added realization-independence, natural-dynamics,
  conserved-quantities, continuum-limit, and gauge/matter capstone notes under
  `Docs/`.
- [x] Added an implementation-facing abstraction note for the next proof seam:
  `Docs/AbstractGaugeMatterBundle.md`.
- [x] Implement the first abstract carrier layer above the current
  package-parametric gauge theorem:
  add an Agda scaffold for an abstract gauge/matter bundle with
  natural-dynamics, conserved-observable, and continuum-lift witnesses.
- [x] Instantiate that abstract bundle with the current canonical
  constraint/gauge package using the minimal lawful identity dynamics and the
  gauge label as the first conserved observable.
- [x] Strengthen the first canonical instance so its observable layer carries a
  minimal `RGObservable`-typed payload alongside the gauge label, without
  pretending the canonical package already computes the shift RG surface.
- [x] Replace the placeholder RG payload in that instance with the observed
  value at `canonicalShiftStateWitness`, making the lift an anchor-state
  transport from the real shift RG surface.
- [ ] Next follow-up: generalize the current anchor-state lift into a
  carrier-level conserved-observable transport through the existing live
  shift RG surface.

Current focus:
`DASHI/Geometry/ProjectionDefectToParallelogram.agda` and
`DASHI/Physics/Closure/ContractionForcesQuadraticStrong.agda`

- [x] Replace the raw `Set` seam in `ContractionForcesQuadraticStrong` with a
  named uniqueness/compatibility seam record.
- [x] Replace the placeholder-style pending field in
  `ContractionQuadraticToSignatureBridgeTheorem` with a named bridge seam
  record that makes the remaining quadratic/signature compatibility gap
  explicit.
- [x] Add canonical split/parallelogram bridge module:
  `DASHI/Geometry/ProjectionDefectSplitForcesParallelogram.agda`, and route
  contraction→quadratic theorem surfaces through it.
- [x] Replace passthrough fields in
  `quadraticEmergenceFromProjectionDefectSplit`
  (`Additive-On-Orth`, `PD-splits`) with direct derivations from the
  no-leakage/orthogonality + energy-split theorem pipeline.
- [x] Complete the quadratic-to-signature classification internals using the
  normalized quadratic from
  `ContractionForcesQuadraticStrong.uniqueUpToScaleWitness`, with theorem
  source rooted in causal/symmetry data instead of profile-only forcing.
- [x] Land explicit Lemma A in the canonical signature route:
  eliminate Euclidean/degenerate competitors via cone/arrow compatibility.
- [x] Land explicit Lemma B in the canonical signature route:
  spatial isotropy + one arrow direction + finite speed force `(3,1)`.
- [x] Keep orbit-profile equality as a secondary witness and negative-control
  eliminator on the signature route, not the primary theorem engine.
- [x] Add a theorem-level Lorentz lock package that separates:
  `(3,1)` witness,
  uniqueness of admissible signature,
  and non-admissibility of rival signatures (`sig13`, `other`,
  plus explicit rival tags `sig40`, `sig22`, `sig04`).
- [x] Strengthen `QuadraticToCliffordBridgeTheorem` from a raw
  presentation-level seam to an explicit factorization interface carrying:
  target carrier, factor map, and generator-compatibility law.
- [x] Complete canonical `Quadratic⇒Clifford` theorem surface as the exclusive
  upstream for `WaveLift⇒Even`.
- [x] Add canonical Clifford grading + even-subalgebra interfaces on
  `DASHI.Physics.CliffordEvenLiftBridge`.
- [x] Define canonical wave lift on the same closure state/carrier pipeline and
  ensure its image is built from even words.
- [x] Prove `WaveLift⇒Even` as factorization through `EvenSubalgebra.incl`
  (witness form), not only a loose parity predicate.
- [x] Thread the completed `WaveLift⇒Even` theorem into canonical bridge
  bundles (`CanonicalContractionToCliffordBridgeTheorem`,
  `KnownLimitsQFTBridgeTheorem`) without adding a parallel wave algebra.

- Replace trivial closure fallbacks on the minimum credible path.
  Current priority:
  `PhysicsClosureFullInstance` and `PhysicsClosureEmpiricalToFull` should use
  the real shift dynamics package, the intrinsic `(3,1)` theorem path, and
  the same concrete constraint-closure witness.
- Tighten downstream closure consumers so they depend on theorem-backed closure
  data, not only type-level metric availability.
- Extend the dynamics package beyond Fejer/closest-point/MDL if a concrete
  causal propagation or effective-geometry witness becomes available.
- Add a typed dynamics-status surface to the canonical shift package:
  propagation,
  causal admissibility,
  monotone quantity,
  effective geometry.
- Add a semantics-bearing dynamics witness companion to the canonical shift
  package and thread it through canonical Stage C and spin/Dirac consumers.
- Add a canonical constraint-closure status surface and a known-limits status
  surface so the broader physics runway is explicit without overstating
  recovery.
- Land the first scoped known-limits recovery witness on the canonical path
  and keep the next recovery target narrow:
  stronger local propagation / local-Lorentz follow-through before any GR/QFT
  claim.
- Keep the witness-bearing canonical spin/Dirac consumer on the authoritative
  Stage C path and treat broader matter/gauge recovery as the next runway
  layer, not as already solved closure.
- Add a concrete canonical constraint-closure witness on the authoritative
  Stage C path and use it as the baseline for the next minimal algebraic
  closure theorem beyond pure status tracking.
- Add a stronger known-limits recovery witness that carries actual propagation
  and effective-geometry witnesses, then target the next scoped theorem at
  stronger local propagation / local-Lorentz follow-through.
- Keep the canonical path on:
  a minimal algebraic-closure theorem for the concrete three-generator system,
  and a scoped known-limits local-recovery theorem for the current local
  Lorentz + propagation slice,
  plus a scoped effective-geometry theorem for that same regime,
  before widening toward richer gauge or GR/QFT claims.
- Land the next two scoped runway theorems in this order:
  a canonical gauge-contract theorem on top of the concrete closure baseline,
  then a canonical spin/local-Lorentz bridge theorem on top of the local
  recovery/effective-geometry baseline.
- Both scoped runway theorems are now on the canonical Stage C path.
  Next widening step:
  move beyond these scoped slices to a less toy gauge theorem or a broader
  known-limits recovery theorem.
- Next widening step:
  add a carrier-parametric gauge/constraint theorem with the current concrete
  carrier as its first instance,
  and add a local causal-effective propagation theorem beyond the current
  local propagation/spin bridge.
- After that:
  add a package-parametric gauge-constraint bridge theorem on the algebra
  side,
  and widen known-limits beyond the current local causal/effective propagation
  regime with a local causal-geometry coherence theorem.
- Keep legacy assumption-backed modules outside the canonical Stage C story.
  Current explicit legacy surfaces:
  `PhysicsClosureInstanceAssumed`,
  generic cone/isotropy compatibility placeholders,
  and prototype wave/unification modules.

## Track H — HME Pipeline & Export

- [x] Drop a curated JSON of DA51 traces (exponents length 15 plus `hot`, `cold`,
  `basin`, `j_fixed`) into `scripts/data/` or document an existing source so
  `scripts/hme_cli.py` has deterministic inputs.
- [x] Run `python scripts/hme_cli.py scripts/data/da51_traces.json --k 3 --threshold 0.9993`
  (with attractors if available) and emit the resulting canonical witnesses.
- [x] Feed that JSON through `scripts/hme_emit_agda.py` to regenerate
  `DASHI/HME/Generated/Witnesses.agda`, then point a new sample `WitnessBundle`
  (e.g. in `DASHI/HME/Integration.agda`) at `canonicalWitnesses` plus a real
  `Admissible` path to demonstrate the contract is wired end-to-end.
- [x] Ingest `SensibLaw/scripts/qg_unification_smoke.py` output into `scripts/data/qg_trace.json`,
  `scripts/data/qg_witness.json`, and `scripts/data/qg_smoke_raw.json` so the
  recorded canonical witness matches the QG smoke sample.

## Track E — Observable Consequences / Forward Predictions

Priority bucket: `P0` first, then `P1`

- Package the current shift observables into one typed interface with three
  buckets:
  proved outputs,
  excluded alternatives,
  forward prediction claims.
- Keep the current proved outputs explicit:
  orbit-profile/signature consistency, seam certificates, MDL descent witness,
  exact shell-1/shell-2 profile outputs, and full 4D candidate exclusion.
- Add forward prediction claims separately.
  Current leading candidates:
  profile rigidity across new realizations,
  Fejer-over-χ² monotonicity,
  observable-space collapse,
  snap-threshold transition laws,
  witness-policy robustness,
  cone-split persistence.
- Add a parallel symmetry prototype track:
  finite graded shell series,
  finite signed/Weyl actions on shell states,
  twined fixed-point traces,
  and a wave-facing graded adapter.
- Treat the current finite graded/twined layer as landed infrastructure and
  move the next moonshine-facing work to:
  explicit twiner libraries, richer grading choices, and only then later
  modularity/umbral tests.
- Current immediate moonshine hardening target:
  add explicit twiner libraries for shift and `B₄`, plus a first
  graded/twined comparison report surface.
- Those are now landed.
  Next moonshine hardening target:
  broaden twiner coverage and expose a richer graded/twined comparison
  summary, then strengthen the wave-grading prototype summary.
- Keep that track explicitly pre-moonshine:
  no modularity theorem,
  no umbral identification,
  no Monster trace claim yet.
- Keep anomaly-report wording strict:
  if Monster-labeled samples do not separate from controls under the current
  embedding, report that result as non-separation with at most a non-unique
  rigid substructure, not as a Monster fingerprint.
- Next moonshine-adjacent validation task:
  require baseline/control comparison tables for any rigid-slot or anomaly
  summary before promoting it into repo-facing docs.
- Next JMD-side anomaly test:
  build a matched Monster-vs-control regime table using
  `eigenspace`, `bott`, `Hecke`, `orbifold`, `DA51`, `j-fixed`,
  proof depth/reach/import counts, and trivector coordinates.
- Script scaffold status:
  `scripts/regime_test.py` is now the canonical local harness for these
  CSV-driven JMD regime occupancy/divergence checks.
- Run regime occupancy/divergence checks before any further Monster-language
  interpretation:
  Fisher/chi-square for categorical occupancy,
  Jensen-Shannon or related divergence on single and joint regime tuples,
  then small-sample leave-one-out classification if signal appears.
- Next DASHI-side anomaly test:
  build a delta-regime/source-vs-trace harness using `Δx`,
  cone compatibility, contraction/Fejér behavior, and transition frequencies
  rather than raw global vector similarity.
- Script scaffold status:
  use the `transitions` mode of `scripts/regime_test.py` once stepwise
  source/trace or regime-transition rows are available.
- Current cone-test scaffold status:
  use the `cone` mode of `scripts/regime_test.py` when stepwise trace rows are
  available with `mass`, `cycles`, `instr`, and related structural columns.
- Existing sibling-repo shortcut:
  the `dashifine-closure-embedding` preset now reads
  `../dashifine/.../closure_embedding_per_step.csv` directly without a manual
  reshape step.
- Current empirical reading from that shortcut:
  the structural cone itself is not the blocker on the checked trace family;
  the next DASHI-side refinement should focus on arrow canonicalization or
  guard tuning around the localized `phistar_50_76` `v_arrow` failures.
- Immediate diagnostics follow-up:
  extend `scripts/regime_test.py cone` with ultrametric/ternary violation
  reporting so those localized failures are grouped by structural signature,
  bucket radius, and nearest admissible-pattern distance.
- Current outcome:
  the localized `phistar_50_76` failures remain on an admissible structural
  ternary signature with zero nearest-signature distance, so the next
  refinement should target arrow guard semantics rather than structural cone
  relearning.
- Current bracket from the new arrow sweep:
  the remaining `phistar_50_76` arrow-only boundary cases clear progressively
  across tolerances near `4e-5`, `8e-4`, `8e-3`, and `8e-2`.
- Next decision:
  choose whether the repo wants
  1. a single canonical arrow tolerance,
  2. a boundary/interior split with explicit exception class,
  or 3. an arrow canonicalization step upstream of the guard.
- Active choice:
  implement option `2` first, so the current arrow-only cases become an
  explicit boundary class in the local diagnostics and any exported witness
  tables.
- Current result:
  that split is now implemented and the observed `dashifine` trace has only
  `arrow_boundary` exceptions.
  The next design choice is whether those four steps should remain explicit
  boundary witnesses or be absorbed by a canonical nonzero arrow tolerance.
- Current implementation status:
  the arrow-guard sweep is now landed, along with named arrow profiles:
  `strict`, `boundary`, and `lenient`.
  The local `dashifine` run currently resolves those as
  `56/4`, `59/1`, and `60/0` for `interior/arrow_boundary`.
- Stable local artifact status:
  `scripts/regime_test.py cone` can now write the current boundary witnesses to
  `artifacts/regime_test/arrow_boundary_latest.csv`.
- Current JMD-builder status:
  `scripts/build_jmd_regime_table.py` now emits a seeded
  `artifacts/regime_test/jmd_regime_table.csv` from the Agda tree and
  currently finds `844` rows total with `7` Monster rows and `6` matched
  control rows.
- Current seeded occupancy read:
  `eigenspace JS=0.5569`,
  `bott JS=0.0608`,
  `joint(eigenspace,bott,hecke) JS=0.6176`,
  and the leave-one-out classification now runs only on the matched `M/O`
  subset instead of leaking unlabeled `U` rows.
- New source-lattice anchor:
  treat the sibling repo `../kant-zk-pastebin` as the current explicit DASL
  source model for the bridge.
  The authoritative source grammar for this pass lives in
  `src/dasl.rs`, `src/sheaf.rs`, and `src/ipfs.rs` there.
- Cross-check on alternate sibling repo:
  `../dashi_lean4` is present locally and still does not fill the current
  JMD-side gap.
  It carries Lean-side DA51/moonshine/schema witnesses
  (`Main.lean`, `MoonshineFractran.lean`, `DashiPerf/Schema.lean`,
  `DashiPerf/Audit.lean`), but not the missing class/projection layer for
  `Basin` / `Eigen`: no DASL address grammar, no explicit `EigenSpace`, and
  no Bott/Hecke/orbifold class table for the HEPData family projection
  problem.
- Immediate source-integration task:
  extend `scripts/regime_test.py cone` with a parser/loader for that sibling
  repo so the execution export gains:
  a source-backed DASL eigen prior,
  a first-pass `basin_ok` grounded in source support/projection,
  and a stable JSON artifact for the parsed source model.
- Current source-integration result:
  that loader is now landed.
  On the checked `dashifine` trace family it preserves the existing
  structural/arrow split but adds a first source-backed mismatch:
  `48/60` steps are source-supported and `12/60` steps
  (all from `pTll_76_106`) currently miss support because the trace heuristic
  assigns `Hub` while the parsed DASL encoding prior is `Earth/Spoke`-only.
- Current witness status:
  `mdl_tail_boundary` is now promoted into the Agda family-classification
  witness and threaded through `PhysicsClosureCoreWitness`; the next decision
  is whether to keep that family witness as a parallel exported surface or
  integrate it into broader theorem/checklist modules.
- Current claim boundary for that task:
  do not upgrade this into a full class-projection theorem or a proof that
  `p47` is preserved automatically.
  The first pass should report explicit source support/projection metrics while
  keeping stronger gauge-compatibility claims deferred.
- Artifact semantics note:
  keep `source_support_ok` as the explicit runtime/export name for this current
  predicate.
  Treat `basin_ok` only as the bridge-facing compatibility alias until a richer
  source projector or class table is in place.
- Current execution-admissibility bridge status:
  `scripts/regime_test.py cone` can now export
  `execution_admissibility_latest.json`,
  `eigen_overlap_latest.csv`,
  and a concrete Agda witness module for the strict-profile checked trace.
- Immediate next JMD task:
  replace the current seed/graph-proxy regime values with stronger semantic
  metadata for the matched subset, especially for `Hecke`, `DA51`,
  `orbifold`, and `j-fixed`, before treating the JMD table as anything more
  than a local comparison scaffold.
- Immediate next DASHI-side task:
  decide whether the current `ArrowBoundary` cases remain the canonical witness
  class or whether an upstream arrow normalization step should absorb them
  while keeping the structural cone fixed.
- Immediate next source-bridge task:
  refine the current DASL-backed projector so `basin_ok` is not only a
  support-on-dominant-eigenspace check.
  In particular, decide whether `pTll_76_106` is:
  1. a real source mismatch,
  2. a trace-side `Hub` heuristic artifact,
  or 3. evidence that the parsed DASL source grammar needs a richer class table
  than the current encoding prior.
- Immediate sub-step:
  replace the current trace-side `Hub` heuristic first and rerun only the five
  current trace families with side-by-side legacy vs refined eigenspace labels.
  If `pTll_76_106` stops landing in `Hub`, treat the current unsupported block
  as a labeler artifact rather than a source miss.
- Current result:
  that classifier refinement is now landed and the current checked five-trace
  family does exactly that.
  `legacy_vs_refined_trace_agreement=4/5`;
  `pTll_76_106` moves from legacy `Hub` to refined `Spoke`;
  and the current strict-profile source-support proxy now clears all
  `60/60` steps.
- Immediate next source-side task:
  because the checked mismatch evaporated under the better labeler, the next
  worthwhile source-bridge step is no longer mismatch triage.
  It is enriching the DASL loader beyond the encoding prior so future source
  predicates can move from eigenspace support toward richer class-level
  projection.
- Immediate implementation target:
  promote the parsed DASL source prior from the small encoding subset to the
  full Monster-prime catalog already present in `../kant-zk-pastebin`.
  The next bridge rerun should therefore use a source model that explicitly
  includes all `15` Monster primes and their
  `Earth/Spoke/Hub/Clock` partition, not just the encoding-level map.
- Current result:
  that loader upgrade is now landed.
  The default DASL source mode is now `monster-primes`, the exported source
  catalog contains all `15` Monster primes, and the current eigenspace
  distribution is
  `Earth=0.4667`, `Spoke=0.4`, `Hub=0.0667`, `Clock=0.0667`.
  The checked `dashifine` trace remains stable under that richer source model:
  `56 Interior`, `4 ArrowBoundary`, `60/60 source_support_ok`.
- Immediate next source-side task:
  use the richer `monster-primes` source catalog to move beyond support-only
  checks and toward an explicit nearest-class or nearest-prime projection
  surface, rather than only dominant-eigenspace support.
- Current result:
  that explicit projection surface is now landed as a canonical
  class-to-prime proxy.
  On the checked five-trace family, Earth-family traces currently project to
  `p2 / T_2 / exponent 46`, while the refined `Spoke` family `pTll_76_106`
  projects to `p17 / T_17 / exponent 1`.
- Current claim boundary:
  this is a canonical source-projection proxy, not yet a geometric
  nearest-neighbor or full class-level projection theorem.
- Immediate next source-side task:
  add a less coarse distance or ranking on top of the current projection proxy,
  so source projection can be compared by more than eigenspace class and
  exponent ordering alone.
- Immediate implementation target:
  add a scored source-prime ranking surface over the current source catalog and
  export the top candidates in the runtime artifacts.
  Keep the claim boundary explicit:
  that scored ranking surface is now landed.
  Current result:
  an explicit primary source-projection mode is now landed so the repo can keep the
  conservative canonical projection as default while also supporting a
  scored-primary projection for experimental runs without rewriting the
  bridge-facing canonical fields.
  this should still be a controlled ranking heuristic, not a geometric
  nearest-neighbor theorem.
- Current result:
  that scored ranking surface is now landed.
  On the checked traces, Earth-family rows still rank `p2` first.
  The refined `Spoke` family `pTll_76_106` now shows the first interesting
  ranked split:
  canonical proxy = `p17`,
  scored shortlist = `p59`, `p71`, then `p17`.
- Current implementation target:
  keep the canonical projection rule unchanged, but export an explicit
  `projection_conflict` marker for rows where the canonical and
  primary-selected source representatives diverge.
- Current implementation target:
  keep the shortlist diagnostic even when scored ranking is enabled, and anchor
  the score to canonical consistency so conflicts mean more than attack-triple
  bonus alone.
- Current implementation target:
  export score-component breakdowns for the ranked and primary source
  projections so the next source-side passes can tune the metric explicitly.
- Current implementation target:
  add richer within-class terms from source-side metadata, especially `Hecke`
  proximity and a weak `Bott` cycle prior, then rerun the bridge on a larger
  set of compatible `dashifine` trace files rather than only the original
  five-family set.
- Current result:
  the richer score is landed and a three-batch `dashifine` summary is now
  recorded at `artifacts/regime_test/dashifine_trace_batch_latest.json`.
  Across `out`, `out_new`, and `out_all`, source support stays fully intact and
  the refined `Spoke` family remains canonically `p17`.
  The next local execution-side target is narrower:
  inspect the additional arrow-boundary families that appear in the larger
  batches, especially `ttbar_mtt_8tev_cms` and `z_pt_7tev_atlas`.
- Current result:
  that family-level inspection surface is now landed.
  `scripts/regime_test.py cone` now emits per-family arrow-boundary summaries,
  and the current larger-batch read is:
  `phistar_50_76` = small arrow-only tolerance ladder,
  `z_pt_7tev_atlas` = single moderate arrow break,
  `ttbar_mtt_8tev_cms` = strongest current outlier because it couples large
  arrow violations with `v_dnorm` failures.
- Current result:
  focused family drilldowns are now exportable.
  The current `ttbar_mtt_8tev_cms` onset is late and mixed-axis:
  first boundary at `t=10->11`,
  arrow sign flip = yes,
  immediate failure mode = `v_arrow` + `v_dnorm`,
  immediate signature change = no.
- Current terminal-step autopsy result:
  alternate `v_dnorm` constructions
  (`raw`, `log_abs`, `robust_z`, `winsor95`, `family_minmax`)
  still leave both terminal `ttbar_mtt_8tev_cms` `v_dnorm` deltas positive.
  Those reversals are numerically tiny (`~9.4e-13`, `~1.6e-13`), so the next
  check should map the failing steps to the underlying tail-bin physics or
  normalization pipeline rather than changing the cone geometry.
- Current raw-context read:
  the same focused export now shows `ttbar_mtt_8tev_cms` is a `7`-bin spectrum
  whose last bin (`x≈1350`) has the largest fractional uncertainty
  (`~8.19%`), and the first boundary onset lands at the late
  `alpha=1e4 -> 1e5` jump.
- Current stronger-witness read:
  despite that late mixed-axis boundary, the same family still has
  `closestpoint_frac=1.0` and `fejer_set_frac=1.0` in the local `dashifine`
  reports, while the explicit exception is on the MDL-exact descent surface
  (`MDL_monotone=False`, `2` violations, worst increase `0.694577`).
- Current classification result:
  the local family-summary surface now promotes `ttbar_mtt_8tev_cms` to the
  narrower `mdl_tail_boundary` class, instead of leaving it in the generic
  `mixed_hard_axis_outlier` bucket.
- Current lemma/count status:
  `TailBoundaryLemma.agda` now encodes the modest current-witness claim that
  an `MDLTailBoundaryFamily` can remain cone / Fejér / closest-point
  admissible while failing only at the MDL-exact layer.
  The current larger-trace count artifact reports `1/9` such families, and
  that one current case is both tail-localized and terminal-boundary.
- Current widened batch count:
  `scripts/tail_boundary_batch.py` now aggregates the currently compatible
  `dashifine` batches into `artifacts/regime_test/tail_boundary_batch_latest.json`.
  On the current three-batch set it reports `2` `mdl_tail_boundary` instances
  across `3` datasets, but still only one unique family:
  `ttbar_mtt_8tev_cms`.
  The same aggregate also now separates repeated controls cleanly:
  repeated `pTll` families plus `dijet_chi_7tev_cms` and `hgg_pt_8tev_atlas`
  stay interior, while `phistar_50_76` and `z_pt_7tev_atlas` repeat only in
  non-MDL boundary classes.
- Current compatible-dataset inventory:
  the same aggregate now records that there are only `3` compatible
  `closure_embedding_per_step.csv` batches currently available in
  `dashifine`.
  Among the `7` current tail-candidate families, only
  `ttbar_mtt_8tev_cms` and `z_pt_7tev_atlas` leave the interior.
- Immediate next execution-side task:
  widen that aggregate beyond the currently compatible `dashifine` trio where
  possible, but within the current inventory the next-priority tail candidates
  are now explicit:
  `z_pt_7tev_atlas`, then the still-unresolved interior heavy-spectrum
  candidates `atlas_4l_pt4l_8tev`,
  `dijet_chi_13tev_cms_mgt6`, `dijet_chi_7tev_cms`, and
  `hgg_pt_8tev_atlas`.
- Current `z_pt` refinement:
  the focused `z_pt_7tev_atlas` drilldown confirms it is still a
  `single_arrow_break`, not a second `mdl_tail_boundary`.
  Present read:
  one late tail-localized boundary step at `t=9->10`,
  `arrow_delta≈0.0305551`,
  no non-arrow failure,
  all tested `v_dnorm` variants remain nonincreasing,
  and the family clears under the `lenient` arrow profile.
- Current first interior heavy-spectrum check:
  `atlas_4l_m4l_8tev` has now been drilled directly and stays fully interior:
  `12` steps, `0` boundary steps, `closestpoint_frac=1.0`,
  `fejer_set_frac=1.0`, `MDL_monotone=True`, no onset event, and its last bin
  is not the max-fractional-uncertainty tail bin.
- Current second interior heavy-spectrum check:
  `atlas_4l_pt4l_8tev` has now been drilled directly and also stays fully
  interior:
  `12` steps, `0` boundary steps, `closestpoint_frac=1.0`,
  `fejer_set_frac=1.0`, `MDL_monotone=True`, no onset event, and its last bin
  is not the max-fractional-uncertainty tail bin.
- [x] Add a validation table for each forward claim:
  source modules,
  confidence level,
  falsifier,
  preferred test harness or dataset.
- Prioritize validation in this order:
  profile rigidity,
  Fejer-over-χ²,
  observable-space collapse,
  snap-threshold laws.
- Observable-space collapse benchmark:
  add a typed harness/report sourced from `RealClosureKitFiber.obsFixed` and
  `obsUnique`, then expose its verdict through the repo-facing validation
  summary.
- Snap-threshold benchmark:
  now includes the shift reference plus secondary and tertiary boundary cases
  from the χ²-boundary library; next step is additional realization coverage.
- [x] Next snap-threshold prerequisite:
  define a severity/snap policy plus witness state for a non-shift realization
  (synthetic placeholder), then add its harness to the benchmark.
- [x] Next snap-threshold task:
  replace the synthetic placeholder harness with a synthetic one-minus harness.
- [x] Next snap-threshold task:
  add a closure-compatible non-shift severity/snap policy for the synthetic
  one-minus harness.
- [x] Next snap-threshold extension:
  add a second non-shift realization harness (Bool inversion).
- [x] Next snap-threshold extension:
  add a Bool inversion-specific snap witness and the B₄ harness.
- Next snap-threshold extension:
  lift the standalone `B₄` harness from shell-only severity to an
  orientation/signature-aware admissible witness surface.
- [x] Build the profile-rigidity harness first.
  Concrete sub-tasks:
  define the benchmark interface,
  add an alternate realization slot,
  emit a typed benchmark report,
  connect the report to the minimum-credible closure adapter.
- [x] The tail-permutation comparison is now the first negative control, not the
  first admissible alternate realization.
- Next validation task after the negative control:
  add one genuinely closure-compatible alternate realization that exposes the
  full orientation/profile/signature surface.
- [x] First canonical admissible alternate realization:
  the synthetic one-minus realization on the 4D Lorentz-family profile path.
- [x] Secondary admissible comparison:
  the 4D Bool inversion realization on the `(3,1)` mask.
- Next mathematically serious alternate realization after the current
  synthetic/bool-inversion pair:
  a Coxeter / Weyl-group realization of the same 4D shell-orbit data.
- First implementation step for that realization:
  add an independent `B₄` / hyperoctahedral shell/profile computation from
  explicit root-shell points and a Weyl-style action.
- Next sub-task after the independent report:
  classify the `B₄` shell neighborhood explicitly and only then decide whether
  orientation/signature promotion is even plausible.
- [x] Add an explicit admissible-realization interface so future comparison
  candidates cannot silently omit orientation/signature data.
- [x] Keep the synthetic one-minus admissible result recorded as `exactMatch`.
- [x] Keep the Bool inversion admissible result recorded as
  `signatureOnlyMatch`.
- [x] Add one aggregate validation/report object that exposes:
  self exact match,
  synthetic one-minus admissible result,
  Bool inversion secondary admissible result,
  tail-permutation negative control.
- [x] Lift that aggregate rigidity report into a closure-facing adapter so the
  minimum-credible Stage C entrypoint exposes both:
  theorem-backed closure data and current validation status.
- [x] Add one repo-facing closure summary surface that re-exports the current
  rigidity suite verdicts directly from the minimum-credible validation
  adapter.
- [x] After the summary surface lands, move the next runnable benchmark to:
  Fejer-over-χ² monotonicity.
- [x] Fejer-over-χ² benchmark sub-tasks:
  define the benchmark report type,
  define an explicit χ² falsifier-status type,
  add a shift reference harness,
  expose the current benchmark verdict from theorem-backed Fejér /
  closest-point / MDL witnesses.
- [x] Upgrade the χ² side from `pending` to an intermediate
  `interfaceWired` status when the snap / `chi2Spike` boundary is present.
- [x] Immediate χ²-side hardening:
  landed via a concrete shift-side χ²-boundary witness from the severity/snap
  layer; next decide whether to promote that witness into a broader falsifier
  theorem or an explicit counterexample library.
- [x] Immediate χ²-side implementation step:
  add a small typed shift-side boundary/counterexample library with more than
  one witness state, then surface it through the validation summary before
  attempting a larger falsifier theorem.
- [x] After that, the next Fejér benchmark target is a standalone formalized χ²
  falsifier theorem or counterexample witness.
- [x] Keep the positive side non-placeholder:
  benchmark facts/reports should carry the actual theorem witnesses instead of
  only boolean flags.
- [x] Add one falsifiability / deviation boundary to the same interface.
  Current minimum:
  mirror-signature exclusion plus failure of competing 4D candidate profiles.
- [x] Promote existing CSV/evidence modules into consumers/providers of the same
  observable package instead of parallel wrappers.

## Shared Integration

- Keep Stage A and Stage B documentation aligned with the new Stage C target:
  minimal credible physics closure.
- Keep the stronger archive-backed reading visible in docs and summaries
  without overstating any of the still-open physics gaps.
- Keep the current archive prioritization visible too:
  `Physics Closure in DASHI`,
  `Branch · Cone monotonicity analysis`,
  and `Branch · Snap Filtering Analysis`
  are now direct support lanes for the live physics closure spine.
- Keep the outreach-facing docs aligned with the same evidence boundary:
  theorem-backed,
  scaffold present,
  physics interpretation still open.
- Ensure docs, TODOs, code, and changelog all distinguish:
  proved,
  evidence-backed,
  predicted.
- Refactor the intrinsic shell/orbit theorem path so theorem-critical records
  do not mention finite realization fields.
- Keep the Coxeter/Weyl scaffold explicitly separated from the admissible
  realization harness until the `B₄` realization exposes justified
  orientation/signature data.
- Add and maintain a repo-facing note for the mathematical framing of the
  orbit-shell result:
  `Docs/OrbitShellProfilesAndLorentzSignature.md`.
- Next `B₄` sub-task after the independent shell/profile report:
  add a typed shell-neighborhood status surface and only revisit admissible
  promotion if the neighborhood is Lorentz-compatible.
- Add a canonical shell-neighborhood classification layer shared by the shift
  reference, `B₄`, and future realizations.
- Add a bounded one-minus shell-family theorem for `m = 2..8`.
- Current theorem task:
  use the landed parametric `m` shell-1 theorem as the baseline one-minus
  classifier for the current shift family.
- Follow-on theorem task:
  decide whether the next theorem step is shell-2 / orientation follow-through
  or a second Lorentz-family realization.
- Immediate realization-search step:
  add an independent shell-side one-minus-family candidate for the 4D Lorentz
  neighborhood, classify it explicitly, and keep it non-admissible until the
  missing shell-2/orientation/signature pieces are justified.
- Current status on that search:
  synthetic one-minus candidate now carries shell-1 and shell-2 profiles,
  orientation/signature are bridged, and a minimal independent-dynamics
  witness is present; it now enters the admissible harness.
- Next realization-search implementation:
  grow the prototype Lorentz-neighborhood dynamic candidate scaffold into a
  genuinely independent dynamics-side realization, then decide whether it can
  move beyond prototype-only status.
- Immediate promotion-side implementation:
  add a typed synthetic-promotion bridge that records the current orientation
  and signature blocker explicitly, and only allow admissible-harness
  promotion when both become independently justified.
- Current promotion-side status:
  synthetic promotion bridge is now admissible-ready on the current path.
- Keep the canonical Stage C entrypoint authoritative in code:
  `DASHI.Physics.Closure.CanonicalStageC` is the recommended import surface,
  while legacy assumed/prototype modules remain compatibility-only.
- Current newest physics-first widening is also landed:
  a stronger extended local recovery theorem beyond the current coherence
  slice,
  plus a stronger algebraic-coherence theorem beyond the current
  package-parametric bridge.
- That next physics-first widening is now landed:
  one stronger recovered-local-regime theorem above the current local
  physics-coherence slice,
  and one stronger algebraic-stability theorem above the current
  algebraic-coherence slice.
- That next physics-first cycle is now landed:
  one stronger recovered-dynamics theorem above the current complete-local
  regime slice,
  one stronger algebraic-consistency theorem above the current
  algebraic-bundle/stability slice,
  one geometry-facing downstream consumer on the canonical ladder,
  and one richer moonshine comparison bundle.
- Current next physics-first cycle is now landed:
  one stronger recovered-wave-geometry theorem above the current
  recovered-wavefront slice,
  one stronger algebraic regime-invariance theorem above the current
  transport-invariance slice,
  one wave-geometry-facing downstream consumer on the canonical ladder,
  and one richer moonshine twined-wave family summary.
- Current newest physics-first cycle is now landed:
  one stronger recovered-wave-regime theorem above the current
  recovered-wave-geometry slice,
  one stronger algebraic regime-persistence theorem above the current
  regime-invariance slice,
  one wave-regime-facing downstream consumer on the canonical ladder,
  and one richer moonshine twined-wave-regime summary.
- Current latest physics-first cycle is now landed:
  one stronger recovered-wave-observables theorem above the current
  recovered-wave-regime slice,
  one stronger algebraic regime-coherence theorem above the current
  regime-persistence slice,
  one wave-observable-facing downstream consumer on the canonical ladder,
  and one richer moonshine twined-wave-observable summary.
- After the full parametric theorem lands, the next milestone is:
  a second Lorentz-family realization search.
- Add a finite orbit-shell generating series layer:
  orientation tag plus shell-1 / shell-2 orbit-size multiplicities.
- Build the shift series witness from theorem-backed current profile data.
- Build the standalone `B₄` series and compare it against the shift series
  without changing admissible-harness semantics.
- Add a concrete prototype wave-series module that lifts the finite shift
  series into a grade-0 wave-facing object while staying outside the
  theorem-critical closure path.
- If the series/wave path keeps looking symmetry-rich, keep the interpretation
  order explicit:
  Weyl/root-system/theta-like first,
  then Niemeier/umbral-style only if a genuine root-lattice shell model
  appears,
  and only then Monster/Moonshine once graded-module or trace-level structure
  exists.
- Current landed closure widening:
  wave-observable-transport-geometry coherence now has theorem surfaces,
  a canonical consumer, and summary exports on the authoritative Stage C
  path.

## Deferred Beyond Minimum

Priority bucket: `P2`

- Full realization-independent generalization beyond the current 4D framework.
- Full GR / QFT recovery.
- Niemeier / umbral-style modular organization, but only after a genuine
  root-lattice shell realization exists.
- Monster / Moonshine or broader symmetry closure, but only after a
  graded-module / trace bridge exists.

## Existing Empirical Gate

### Masked Orthogonal Split (empirical gate: PASS)

Layer: 3D closure embedding (`v_pnorm, v_dnorm, v_arrow`).
Quadratic: `G = diag([-1, 0.2034, -1])` (mask-based).
Projector: `P = G-orthogonal projector onto shape coords [0,1]` (`arrow=coord 2`).
Results (n=156 steps, dim=3):

- `||PᵀG − GP||_F = 0.0`
- `max |⟨PΔs, (I−P)Δs⟩_G| = 2.396e−16`
- `max |Q(Δs) − Q(PΔs) − Q((I−P)Δs)| = 6.661e−16`

Interpretation: Case A achieved in cone layer — exact G-self-adjoint
projection, vanishing cross-term, Pythagorean quadratic split holds to machine
precision.
- Current landed closure widening: wave-observable-transport-geometry regime now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime coherence now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime completeness now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime soundness now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime consistency now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime invariance now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime robustness now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime resilience now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime harmony now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime balance now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime symmetry now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime convergence now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime fidelity now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime legibility now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime transparency now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime refinement now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime resolution now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime calibration now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime calibration now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.

## Ultrametric FP formal layer follow-ups (2026-03-29)
- [x] Replace `scalarStep` shrink with a real local relaxation while preserving refinement/recovery theorems.
- [x] Add explicit symmetry action and equivariance proof for scalar tower; extend quotient beyond trivial identity action.
- [x] Thread RG toy through `PhysicalTheory`/`Refinement`/`SymmetryQuotient`/`Observable` with a nontrivial contraction and observable.
- [x] Draft gauge toy quotient + observable and check equivariance/defect descent against the new shell.
- [x] Add changelog entry once the scalar relaxation upgrade lands.
- [x] For each landed toy, instantiate local operator algebra/scaling/observable/quotient witnesses (no relying on global availability).
- [x] Strengthen the scalar approximate-refinement witness from the current coarse boundary witness (`approxEq₀ = ⊤`) to the sharper “all but last coordinate” relation.
- [ ] Push the same nontrivial quotient/witness pattern beyond scalar/RG/gauge to later toys.
- [x] Add a CLOCK/DASHI phase bridge module on the safe schema:
  `phase : S → HexTruth`, `coarse : HexTruth → TriTruth`, `coarse (phase (T² x)) = rotateTri (coarse (phase x))`,
  with cone admissibility, contraction/Lyapunov descent, and MDL as the dynamic constraints.
- [x] Instantiate `CLOCKPhaseBridge` on a concrete state space and prove the `phase-step²` witness, rather than leaving the bridge at the generic packaging level.
- [ ] Add an effective coarse-grained dynamical instance showing how cone admissibility, descent, and possibly contraction arise on top of the periodic CLOCK kinematics without forcing a false strict-contraction claim for the raw cycle.
- [x] Add a stroboscopic coarse CLOCK dynamics theorem on the concrete lagged clock instance, with `T²` descending to triadic coarse evolution.
- [x] Strengthen the RG toy with explicit basin-label / irrelevant-size scaling theorems and observable-collapse lemmas.
- [x] Push the CLOCK bridge beyond kinematics into an actual effective closure instance with admissibility and Lyapunov/descent witnesses on a nontrivial coarse sector.
- [ ] Connect the new `EffectiveClockClosure` surface to a concrete admissibility/cone witness instead of the current generic stroboscopic closure packaging.
- [x] Connect the new `EffectiveClockClosure` surface to a concrete admissibility/cone witness instead of the current generic stroboscopic closure packaging.
- [x] Push CLOCK from cone preservation on `step²` to a tighter bridge between the effective cone package and the generic `PhasePhysicsBridge` surface.
- [x] Decide whether the next CLOCK step should be a true `PhasePhysicsBridge` instance on an effective sector or a deliberately separate step²-only closure hierarchy.
- [x] If CLOCK stays step²-based, add a clearer statement of how the stroboscopic sector substitutes for raw-step contraction in the wider closure story.
- [x] If needed, package the new CLOCK normalization facts into a named “one-step entry to the stroboscopic sector” theorem family for higher-level closure modules.
- [x] If desired, lift the CLOCK normalization/sector-entry package into whichever higher-level closure module will consume the step² bridge.
- [x] Strengthen GaugeShell with recovered-class, observable-stability, and coarse-vacuum class lemmas.
- [ ] Push GaugeShell from recovered/vacuum-class statements to a more explicit gauge-compatible scaling or coarse-step theorem pack.
- [x] Push GaugeShell from recovered/vacuum-class statements to a more explicit gauge-compatible scaling or coarse-step theorem pack.
- [x] Extend GaugeShell from one-step coarse monotonicity to iterated coarse-step or basin-level gauge-invariant scaling.
- [x] Push GaugeShell from iterated monotonicity to a stronger canonical-basin or eventual-collapse statement.
- [x] Extend GaugeShell from recovered-step canonical class to a sharper eventual-collapse bound or a more explicitly gauge-invariant basin theorem.
- [x] If staying with the current toy operator, package the Gauge recovered-tail persistence/collapse lemmas into a named asymptotic bundle parallel to RG.
- [x] If desired, add a named Gauge asymptotic bundle mirroring `rgAsymptotic`, rather than leaving the recovered-tail story as a flat lemma family.
- [x] Strengthen RG with coarse-step approximation and coarse observable stability/monotonicity lemmas.
- [ ] Extend RG from single-step coarse monotonicity to iterated scaling or basin-wise asymptotic statements.
- [x] Extend RG from single-step coarse monotonicity to iterated scaling or basin-wise asymptotic statements.
- [x] Push RG from iterated monotonicity to stronger asymptotic collapse/canonical-basin statements.
- [x] Decide whether the next RG step should target an explicit canonical representative theorem or a more physical coarse-graining operator beyond the current toy asymptotic witness.
- [x] Push RG from canonical recovered-step statements to a less toy coarse-graining operator or an actual eventual-collapse bound.
- [x] If staying with the current toy operator, make the RG recovered-tail persistence/canonical-collapse story explicit as a named higher-level theorem bundle.
- [x] If desired, expose the RG asymptotic and canonical-tail bundles through a higher-level summary module or closure consumer.
- [x] If useful, add a single cross-toy consumer module that imports the new CLOCK/RG/Gauge summary bundles together.
- [x] If staying with the current RG toy state, add a more explicit renormalization operator family on top of `coarsePow`/`stepPow` rather than relying only on flat coarse-step lemmas.
- [x] Wire the packaged toy bundles into at least one closure-side consumer module outside `DASHI/Physics/Toy`.
- [x] If desired, replace the current RG renormalization family with a genuinely richer coarse operator than “coarse then relax once”.
- [x] Add schedule-level comparison theorems on the current RG flow family so longer target-scale evolution at fixed coarse depth is explicitly comparable, not just bounded by the initial state.
- [x] Add a less-factorized fused RG operator in the current encoding, together with an immediate theorem pack, before attempting harder cross-depth comparisons again.
- [x] Extend the fused RG operator with recovered-tail/canonical-collapse persistence so it matches the stronger flow-side regime persistence surface.
- [x] Add a weak but useful fused-vs-flow comparison layer that avoids raw coarse-depth associativity while still comparing the new operator to the old one.
- [x] Add a structural mixed-schedule comparison between `stepPow` after `rgFused` and nearby `rgFlow` schedules that stays within the current encoding and avoids coarse-depth associativity claims.
- [x] Add a minimal prediction/benchmark-facing layer for the RG toy, with total `PredictionTheory`, `BenchmarkTheory′`, and a simple mismatch score.
- [ ] If desired, strengthen the RG flow family beyond `coarsePow` plus `stepPow` into a less factorized operator that is not definitional composition of the existing pieces.
- [ ] If desired, compare different coarse depths or mixed coarse/evolve schedules directly, rather than only fixed-`k` target-scale refinement.
- [x] Add first benchmark-facing RG comparison theorems: fused-vs-flow agreement on `rel#` and stepwise monotonicity on `irr#`.
- [x] Lift the RG benchmark comparison from single observables to the full current mismatch score in the recovered regime.
- [x] Add a schedule-sensitive raw-state RG benchmark surface, with at least one relevance-stability theorem and one irrelevance-monotonicity theorem.
- [x] Strengthen the RG benchmark layer beyond the current simple `rel#`/`irr#` penalty score into a richer observable or schedule-sensitive prediction surface.
- [x] Push the new rich RG benchmark score beyond endpoint-derived proxies into mixed-schedule trace/recovery/scale channels.
- [ ] If desired, replace the current recursive mixed-trace proxies with fuller explicit trace objects and non-proxy recovery-time/scale-profile semantics.
- [x] Phase 2 RG: add at least two coarse schemes so universality is not tested against a single stylized coarsening route.
- [x] Phase 2 RG: add at least two evolve modes so mixed schedules can express different perturbation channels, not only repeated copies of one local step.
- [x] Phase 2 RG: enrich the RG state with a less trivial fixed-point/family label so recovery need not collapse immediately to one vacuum-style target per basin.
- [x] Phase 2 RG: lift mixed schedules onto the new scheme/mode hierarchy rather than keeping them on the older single-scheme/single-mode path surface.
- [x] Phase 3 RG: restate the benchmark comparison theorems against the richer operator/state hierarchy, separating endpoint universality from path/scale nonuniversality.
- [x] Phase 3 RG: add at least one theorem where different schemes share endpoint class but differ on the trace-aware benchmark channels.
- [x] Phase 3 RG: lift the new Phase-3 split beyond the one-layer vacuum witness to a positive-depth uniform mixed schedule on the richer hierarchy.
- [x] Phase 3 RG: lift the new split beyond vacuum-only witnesses to a non-vacuum one-layer `holdMode` comparison on the richer hierarchy.
- [ ] Phase 3 RG: lift the new split beyond `holdMode`-only witnesses to a non-vacuum `relaxMode` or mixed-mode comparison on the richer hierarchy.
- [x] Extend the schedule-sensitive RG benchmark surface from target-scale step schedules to a scale-aware mixed coarse/evolve schedule family on raw pre-coarsened states.
- [ ] Keep CLOCK formalization cyclic (`ℤ/6` / `HexTruth`) and avoid upgrading it to a dihedral / reversal-involution story unless that stronger relation is actually proved in-repo.
Cleanup
- [x] replace stale giant summary exports with ladder-based summary exports
- [x] introduce short-path wrapper modules for closure wave-regime families
- [x] introduce short-path wrapper modules for moonshine wave-regime reports
- [x] add canonical closure and moonshine ladder map modules
- [x] resume `1/2/3/4` widening only after the cleanup compiles cleanly
- Active widening loop:
  next cycle continues with one more algebra rung, one more recovered-local
  rung, one more canonical consumer, and one more pre-moonshine summary on the
  cleaned wave-regime structure.
## Cleanup / Consolidation
- [x] Add a canonical `LocalProgramBundle` for the frozen local ladder.
- [x] Point `Closure/Canonical/Ladder` at grouped ladder surfaces rather than mirroring `CanonicalStageC`.
- [x] Rewire `PhysicsClosureValidationSummary` to grouped wave-regime imports only.
- [x] Rewire remaining canonical modules away from direct per-rung wave-regime imports.
- [x] Add the `Traceability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Auditability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Reliability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Verifiability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Repeatability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Reproducibility` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Portability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Interoperability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Composability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Maintainability` rung across algebra, recovery, consumer, and moonshine grouped summary surfaces.
- [x] Add the `Extensibility` rung across algebra, recovery, consumer, and moonshine grouped summary surfaces.
- [x] Add the `Scalability` rung across algebra, recovery, consumer, and moonshine grouped summary surfaces.
- [x] Add the `Durability` rung across algebra, recovery, consumer, and moonshine grouped summary surfaces.
- [x] Add the `Usability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Operability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Split `Compatibility` / `Composability` aliases on the canonical Stage C import surface so grouped ladder compiles stop depending on import-order collisions.
 - Landed `Sustainability` rung across algebra, recovery, consumer, and moonshine grouped wave-regime ladders.
- 2026-03-11: landed `Stewardship` rung across algebra/recovery/consumer/moonshine grouped wave-regime surfaces.
- 2026-03-11: landed `Accountability` rung across algebra/recovery/consumer/moonshine grouped wave-regime surfaces.
- [x] Strengthen the mixed RG schedule surface with direct mixed-schedule-vs-mixed-schedule relevant-sector comparison and recovered-score collapse theorems.
- [x] Add mixed-schedule recovered-tail and canonical-vacuum theorems parallel to the existing fused/flow tail theorems.
- [x] Add mixed-schedule benchmark-tail theorems that collapse the mixed mismatch score after further target-scale evolution, not just class/observable tails.

- [x] Add a minimal bad-mode suppression surface across the LILA bridge:
  empirical basin dwell/run-length/transition metrics in `DASHIg`,
  and a receipt-side invariant stub in `DASHI/Physics/Closure/BadModeSuppression.agda`.
