# BH4 ↔ physical-tissue future-observation max-cut

Updated 2026-11-07. These two DASHI heads are **separate**, not
a compiled same-object proof:
- developmental-history PR #1471: `chatgpt/biology-history-future-quotient-20261106`;
- Kitzerow source/29×12 BH4 PR #1454:
  `feat/kitzerow-bh4-pathway-ontology-interop`
  (stacked on #1226 and #1159, with historical merge debt).

## Physical theorem and model responsibilities

Let `x` be a source-specific compartment/redox/cell/tissue physical state;
`u` a time-dependent intervention; `K_u` its measured or derived
physical stochastic transition kernel; `O` the measured phenotype;
and `pi` a proposed future-sufficient state projection.

**One selected physical model** must pay:

1. `BH4.sameStateSameCompartmentTime`: explicitly identify original
   BH4 pools, BH2/NAD(P)H, QDPR recycling, TH/TPH/NOS/AGMO demand,
   enzyme abundance, ion/electrochemical state, compartment and clock.
2. `BH4.reactionAndExchangeBalance`: source-pinned Rhea reaction direction
   and measured 29-species exchange + 12-reaction flux intervals,
   and distinct nonfinite chemistry residuals. Use existing
   `BH4SystemStateExact`, `BH4OpenMetabolicNetworkAdapterExact`,
   `BH4JointFluxFeasibilityExact` and `BH4ExchangeIdentifiabilityExact`.
3. `physicalStepRefinesTissue`: for all 27 voxels, the original
   PNP/chemistry/tissue physical step agrees with the nonperiodic
   54-bond biological readout. PR #1471's
   `BiologicalSourcePhysicalTissueSimulationExact` proves the
   arbitrary-history consequence once this one-step source proof exists.
4. `futureDistributionCommutes`: pushforward of the original
   stochastic physical kernel factors through the selected observed
   quotient for each intervention, with properly calibrated conditional
   rates. PR #1471 already proves abstract finite rational-weight
   18-class lumping, including inhomogeneous action histories.
5. `heldoutInterventionDiscriminates`: paired original measurements on
   the *same* samples/compartments/times distinguish allocator against
   parallel redox and context-specific non-allocator models, with
   specimen/experiment disjoint splits and independently replicated tests.

## New exact results, separate branches

- PR #1454: `BH4AllocatorFutureObservationCountermodelExact`
  proves that the same synthesis+recycling supply and an exactly balanced
  selected five-sink budget can produce **different** branch-specific
  responses. Scalar BH4 availability is not future-sufficient for all
  branch observations, even if a mass balance is satisfied.
  `scripts/check_bh4_allocator_future_observer.py` enumerates finite
  nonnegative balanced allocations as a numerical regression.
- PR #1471: `BiologicalSourcePhysicalTissueSimulationExact`
  derives all-action-history 54-bond coarse-phenotype agreement
  pointwise, without function extensionality, from an **explicit**
  PNP-selected physical one-step simulation receipt.

## No unsupported transfers

This bridge is a planned **cross-branch** physical theorem target, not a
claim that Kitzerow's autism/comorbidity hypothesis is confirmed by
planarian experiments, that a dmsC assay measures BH4, or that any
specific person has a disease mechanism. Source-curated Rhea/ChEBI
chemistry predates the proposed allostatic allocation synthesis.

The creator's own public discussion of resource competition, temporal
displacement and the BH4 shunt proposes the mechanistic hypothesis; a
candidate graph is not its kinetic confirmation. In particular 190 SABIO
rows / 932 acquired quantitative values do not automatically establish
same-tissue, same-compartment, same-state 12-reaction and 29-exchange
physiological flux bounds. The author's original chart is not the
independently selected DASHI 12-reaction panel.

**Merge gate:** reconcile the BH4 stacked ancestors with current
developmental biology head, then import both native Agda owners into a
single Golden root; obtain exact-head `parallel_checker` kernel acceptance.
No cross-branch import is added until then. Neither pathway alone
creates an original joint physical dataset, an authenticated source
passage, a reviewed PostgreSQL PNF promotion, or clinical causality.

## Arrow semantics

The arrows in causal/verification diagrams are maps, dependencies
or directed model transformations, not Conway's large-number operators.
Conway's numeric `a -> b` is `a^b`;
`a -> b -> c` is `a ↑^c b`.
This meaning is **not** inherited by a pipeline arrow,
e.g. source → physical state → quotient → observation.


## 2026-11-09 — current-head integration and exact remaining lemmas

Source audit: PR #1471 head observed at `d9f5dd931517a86542b498648e41cb6aea9094cf` before this continuation; PR #1454 at `fdad652d4c9409106d37384cc2bc06112ea60936`. These are **separate draft branches**. This continuation adds `twoNativeCubicalBondTransfersConserveTotal` on PR #1471: a genuine two-step shared-inventory proof using original `Grid.PositiveBond` and the semantic `Cube.Ternary27Point` geometry. This is source-written only: no Agda kernel receipt was obtained in this session.

### Exact maximum-cut register (proposed targets unless an owner is cited)

| Gate | Already source-written / executable | Exact remaining obligation and exit condition |
| --- | --- | --- |
| G0 kernel | Original 3×3×3 field, 54 native bonds, cubical/pants seams, open boundary ledger, selected finite reaction fixtures; two-step shared-state transfer | Run exact-head Agda 2.9 / `parallel_checker` against Golden roots and all transitive imports; archive stdout/stderr and SHA |
| G1 local continuity | `Biological369CubicalOpenSignedChargeExact` establishes **global** open signed charge balance; `check_biological_369_local_charge_continuity.py` tests finite voxelwise cases | `original369LocalSignedContinuityExact`: for every original voxel, integer charge difference + signed incidence-current divergence equals explicit face source/sink, including all native directed histories; verify in Agda |
| G2 original chemistry | `BH4SpatialOriginalQDPRStoichiometryExact` selected five-species QDPR; `check_bh4_original_panel_spatial_events.py` consumes the **original** source certificate when mounted | `original29x12SpatialReactionBalance`: all source-certified 29 species × 12 finite reactions, three nonfinite residuals, and 29 exchange coordinates on **one** 3×3×3 shared inventory, preserving elemental and charge ledgers; no fabricated zero fluxes |
| G3 physical step | Finite nonnegative reaction/transport events and face exchange available | `sameSourcePhysicalReactionTransportStep`: compose source-specific rates, admissible compartments, membrane/vascular permissions, ionic transport, reaction stoichiometry and actual environmental sources into one well-defined evolution |
| G4 same-source refinement | `BiologicalSourcePhysicalTissueSimulationExact` gives all-history consequences **conditional** on one-step premises | `physicalBH4StepCommutes`, `physicalPNPStepCommutesOriginal`, `physicalTissueOneStepRefinement`; if old Boolean tissue rule fails, refine observation rather than assert false commutation |
| G5 future sufficiency | Selected 18-class stochastic quotient and BH4 three-state minimal example | `physicalKernelLumpsUnderInterventions` and `physicalFutureQuotientIsMinimal` for actual admissible interventions, transition kernel and observation language |
| G6 evidence | Source-aware BH4 measurement intake and finite diagnostics | `sourceCalibratedParametersAdmissible` and `heldoutFuturePredictionsDiscriminate`: same-sample compartment/time calibration, model uncertainty, alternatives, independent prospective test |
| G7 integration | Separate Golden roots and source provenance | Reconcile stacked #1159/#1226/#1454 with #1471; source-review ITIR #72 without auto-PNF promotion; combined Golden exact-head acceptance |

### Proof dependency and phased deliverables

- **D0 (acceptance):** exact-head checker receipts for both independent roots, then a reconciled joint root. A source-written declaration is never labelled kernel accepted without its receipt.
- **D1 (shared chemistry):** G1 + G2. Reuse original incidence and molecular matrix owners, without replacing the real 3D cube by a semantic 27-vector.
- **D2 (physical evolution):** G3 with explicit admissibility, time, boundary currents, permeability and energy assumptions.
- **D3 (physical-to-observed):** G4 commutation and consequent history transport, or a recorded physical counterexample.
- **D4 (future quotient):** G5 exact lumpability/refinement and minimality relative to the declared interventions.
- **D5 (science):** G6 measured original kinetics and held-out, uncertainty-bounded longitudinal comparison.
- **D6 (governance):** G7 lineage and independently reviewed evidence.

**No closure claimed** for Agda acceptance, entire 29×12 source certificate execution, calibrated physiological flux, full PNP evolution, real phenotype prediction, causal Kitzerow hypothesis, or branch reconciliation. Local charge continuity currently has a Python regression, **not** an Agda proof.


### 2026-11-09 continuation — substantive P0 local components, exact residual

**Source-written Agda work (no kernel receipt yet):**
- `BiologicalSharedFiniteVectorTransferExact.lookupAfterDebit`: indexed voxel post-debit + actual (0/1) local outflow = original amount; and `lookupAfterCredit`: indexed target gains one.
- `BiologicalOriginal54BondSharedVectorExact.originalBondLocalSourceDebitIsPaid` and `originalBondLocalTargetCreditIsPaid`: specialize those results to actual original nearest-neighbour bond endpoints in ternary 3×3×3 geometry.
- `Biological369CubicalBoundaryMaterialExact.lookupAfterFaceInjection` and `originalBoundaryInjectionLocalReceipt`: exactly account at the exterior voxel, using `OnFace`-qualified original events.
- Existing `originalFullSpatialOpenSignedChargeBalance` still supplies **global** signed open charge; the Python regression still checks **voxelwise** charge continuity.

**Do not prematurely close `original369LocalSignedContinuityExact`.** It still needs a single Agda source for per-voxel integer signed currents combining *executed* cation/anion native-bond histories, boundary withdrawals and injections, a signed incidence divergence, and the all-27-voxel step/history induction. The pointwise local source/target/face lemmas above remove its lowest-level arithmetic obligations only. G1 remains PARTIAL.

**Other progress on companion #1454:** `check_bh4_original_panel_spatial_events.py` now composes each certified original finite reaction event with an actual original native-bond transport and its reverse on the **same** 3×3×3×species inventory, checking nonnegative molecular amounts and conserved CHNOP/charge. The full 29×12 execution remains gated on mounted source certificate and does not claim any of the 29 physiological external fluxes. G2 remains PARTIAL.

**Updated immediate proof order:** local all-voxel charge-current ledger → source-certificate 29×12 same-state histories with explicitly separately tracked environmental exchanges → admissible physical step → PNP/BH4/tissue commutation → intervention-safe stochastic quotient → independent measurements. No rate or clinical causal claim arises from this structural conservation work.


### 2026-11-09 next P0 maximum-cut: actual support locality

This pass adds structural *Agda source* lemmas in the existing original physical owners, not a new parallel physical carrier:
- `lookupDebitAwayFromSource` and `lookupCreditAwayFromTarget`: independent spectator voxels do not change during primitive source debit / target credit.
- `lookupTransferAwayFromEndpoints` and `originalNativeBondUnchangedOutsideEndpoints`: **the existing actual `transferOne` implementation** leaves any observer outside both original native-bond endpoints unchanged, including zero-source/no-op cases.
- `lookupFaceInjectionAwayFromEvent` and `originalFaceInjectionLeavesOtherVoxelUnchanged`: verified `OnFace` influx modifies no off-face selected site.
- `originalFaceDischargeLeavesOtherVoxelUnchanged`: actual available-material extraction modifies no off-event site.
- `scripts/check_biological_369_local_charge_continuity.py` now has an independent event-support negative control, checking absence of remote state changes in addition to signed `ΔQ + div J = q_external` arithmetic.
- `scripts/check_biological_history_future_round23.sh` requires these owner declarations before invoking its preexisting parallel checker.

The source is updated to use Prelude-supported `¬ (_≡_)`; **no Agda executable or exact-head acceptance receipt was available in this session**. The checker script has not been executed on the new head.

**P0 STILL OPEN:** `original369LocalSignedContinuityExact` must prove the actual per-voxel *signed* incidence-current and boundary-event identity for every chronological history, not merely locality and global charge conservation. `original29x12SpatialReactionBalance` additionally needs acquired original matrix bytes and source-consistent compartment/charge bookkeeping; `sameSourcePhysicalReactionTransportStep` needs rates and admissible PNP/circulation couplings. P1–P3 physical and empirical gates unchanged.

**Highest next step:** prove at each source and target the exact executed `transferOne` debit/credit (including empty-source and reversed bonds), and then sum those signed local event receipts through histories. This is now well isolated by the off-endpoint proof and original-face support.


### 2026-11-09 typed original-bond history advance (last P0 pass)

**New Agda source owners on PR #1471:**
- `OriginalDirectedNativeBond` with `forwardNative` and `reverseNative` constructors taking genuine `Grid.PositiveBond`; `applyNativeDirectedBond`, `runOriginalDirectedNativeHistory` execute the existing native `transferOne` on one 3×3×3 inventory.
- `everyChronologicalOriginalDirectedHistoryConserves`: conservation along every typed, chronological actual-bond history, not arbitrary unvalidated Fin pairs.
- `NativeHistoryAvoids` and `nativeHistoryLeavesUnvisitedVoxelUnchanged`: source- and target-avoiding proofs for an original observer voxel persist across all such histories.
- Original source/debit, target/credit and certified outer-face injection/extraction support lemmas are source-written; the Golden script now checks the new exact declarations before invoking the existing parallel checker. The Python signed charge regression checks that every simulated change stays on the selected bond endpoints or face voxel.

**Remaining true P0 lemma frontier:** `original369LocalSignedContinuityExact` still needs source/target *actual moved quantum* equality with signed ion valence, a signed incidence divergence at every voxel, cumulative face inflow/outflow, and induction over mixed original charge-event histories. The new support and typed-history theorems do not establish it by themselves. Source-writing is not Agda 2.9 kernel acceptance.

**Original 29×12 certificate availability:** connected GitHub lookup on PR #1454 of `artifacts/biology/rhea-kitzerow-bh4-reactions.json` returned 404. That verifies the artifact is not present at that tracked path on the branch; it does **not** prove it is absent from a private machine, earlier acquisition store, or other source. The original-panel full test has not been run. Re-acquire or supply the byte-pinned primary certificate before claiming 29×12 completeness. No measured exchange flux is inferred.

P1 actual BH4/PNP/tissue physical same-object steps, P2 physically observed stochastic quotient and P3 rates/held-out data/Golden reconciliation remain OPEN.


### 2026-11-09 P0 executed-current advance (source-written, not yet kernel accepted)

The original 369 P0 cut now has **executed moved-quantum** identities, not just unrelated local debit/credit operations:

- `BiologicalSharedFiniteVectorTransferExact.lookupTransferSourcePaid` proves the *actual* `transferOne` source is debited by its 0/1 available quantum, for distinct endpoints.
- `lookupTransferTargetReceivesActualSource` proves the actual destination is credited by precisely that same amount, also in the empty-source case.
- `BiologicalOriginal54BondSharedVectorExact.tritGridStepNeverStationary`, `originalPositiveBondEndpointsDistinct` and `originalDirectedNativeEndpointsDistinct` discharge the geometric distinctness premise from the **original ternary 3×3×3 native bonds and injective 27-chart**.
- `original369NativeSourceFluxExact`, `original369NativeTargetFluxExact` and `originalNativeVoxelIncidenceBalance` establish the original-bond per-voxel balance `after + actual outgoing = before + actual incoming`, by native source/target/off-endpoint roles.
- `Biological369CubicalOpenSignedChargeExact.original369SignedNativeOneStepContinuity` uses positive/negative ion vectors and the existing integer `integerSignedCharge` to prove signed per-voxel conservation of *one* native ionic bond event.
- `Biological369CubicalBoundaryMaterialExact.originalBoundaryDischargeLocalReceipt` now proves face withdrawal removes precisely the actual available quantum at its source voxel (complementing prior face injection and off-site locality).

A separate local exact-rational/integer diagnostic (not the repository Golden or Agda kernel) enumerated 11,664 physical bond/direction/source-amount/observer combinations: 54 native bonds × 2 directions × 4 source amounts × 27 observers. All satisfied the pointwise unsigned incidence identity. The changed Agda declarations have **not** been checked with Agda 2.9 here; source-writing/spot diagnostics are not kernel receipts.

**Precise remaining lemma for P0:** `original369LocalSignedContinuityExact` now narrows to *role classification at all 27 voxels, the same chronological signed source/target/face current ledger and mixed-history induction*. Do not label it closed from the one-step theorem. The original 29×12 compiled source certificate/matrix, source-specific 29 external exchanges, `sameSourcePhysicalReactionTransportStep`, physical BH4/PNP/tissue commutation, stochastic-physical minimality and held-out validation are still OPEN.

Golden runner: `scripts/check_biological_history_future_round23.sh` now checks that newly named source declarations exist before running its repository parallel-checker; no actual checker execution occurred in this session.


## 2026-11-09 P0 finite signed-local continuity closure candidate — exact-head check outstanding

**Source-written same-object mathematics advanced:** `Biological369MixedNativeFaceSignedContinuityExact.agda` is now imported by `DASHI/EverythingBiologicalHistoryFutureRound23.agda` and registered in `scripts/check_biological_history_future_round23.sh`. Its precise result is `original369LocalSignedContinuityExact`: for any original voxel (`Fin 27` chart for `Ternary27Point`), any chronological sequence of *typed* positive/negative ion transfers over the genuine original 54 cubical bonds, and any sequence of actual six-face `OnFace`-certified ion injections/withdrawals interleaved with those transfers, the integer signed charge of **final local inventory + cumulative local outgoing currents** equals that of **initial local inventory + cumulative incoming currents**. The current magnitude is the actual transported 0/1 quantum for bond transfers, the requested amount for inlet injection, and the available amount for boundary withdrawal; zero-source events are stationary. The signed ledger retains positive and negative ions separately before applying the original `integerSignedCharge` operation. Neither current nor boundary quantity is an invented physiological rate.

**Dependencies source-written this pass:** `lookupTransferSourcePaid`, `lookupTransferTargetReceivesActualSource`, `originalDirectedNativeEndpointsDistinct`, `originalNativeVoxelIncidenceBalance`, `original369SignedNativeOneStepContinuity`, `original369AllVoxelNativeSignedHistoryContinuity`, `originalBoundaryDischargeLocalReceipt`, `originalFaceEveryVoxelBalance`, `positiveMixedHistoryBalance`, `negativeMixedHistoryBalance`. Existing ternary-27/54-bond original geometry, exterior face receipts and historical material/charge owners are reused.

**Acceptance state:** all listed declarations and the Golden import were committed through GitHub. **No Agda executable, original native parallel checker, or exact-head kernel receipt was available here**. The claimed finite theorem is therefore **SOURCE-WRITTEN / KERNEL-PENDING**, not proved accepted. An independent finite arithmetic diagnostic checked 11,664 unsigned and 23,328 signed one-event original-bond/site combinations; this does not verify the newly committed arbitrary-history Agda source. The original physics remains the separate EVIDENCE OPEN gate.

**Revised P0:**
- `original369LocalSignedContinuityExact`: source-written, imported into Golden; kernel typecheck and regression execution **pending**.
- `original29x12SpatialReactionBalance`: **OPEN**, strict byte-pinned 29×12 Rhea source certificate unavailable at the tracked BH4 branch path; do not substitute the selected QDPR self-test. 29 external exchanges and source context unpaid.
- `sameSourcePhysicalReactionTransportStep`: **OPEN**, requires actual 29-species reactions, source-paid rates and boundary/permeability/PNP laws on one state.
- P1 physical BH4, PNP and tissue commuting squares: **OPEN**.
- P2 physical intervention-safe stochastic quotient and minimality: **OPEN**.
- P3 source-calibrated physiological rates, heldout model discrimination, integrated Golden/ITIR evidence reconciliation: **OPEN**.

**Next highest-alpha cut:** execute exact-head Agda Golden checker; repair any type failures in the new original continuity owner, then reconcile the complete real Rhea 29×12 source certificate and chemistry/exchange on the SAME 3×3×3 inventory. Preserve qDHB ≠ generic BH2, attribution, and external sources. Never promote synthetic event arithmetic into empirical Kitzerow clinical causality.
