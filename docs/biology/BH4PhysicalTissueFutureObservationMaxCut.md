# BH4 ↔ physical-tissue future-observation max-cut

## 2026-11-09 — local 29×12 CHNOP/charge finite-volume max-cut (latest)

**New source-written executable implementation on BH4 PR #1454:** `scripts/check_bh4_original_panel_spatial_events.py` now supplies `site_conserved_quantities` and `assert_original_voxel_continuity`, which evaluate the **actual original 3×3×3 physical voxel** inventories as six conserved coordinates: C,H,N,O,P and integer signed charge. Its `run_original_spatial_event_history` executes original acquired finite Rhea reaction columns, native original nearest-neighbour directed species transport and six-face admissible environmental injection/actual extraction **on one chronological inventory**, collecting actual per-voxel native divergence and separately credited true exterior source/sink. After every event and at all 27 voxels it checks
`local_final - local_initial + cumulative_native_divergence == cumulative_actual_environmental_source`
for **all six coordinates**; totals are checked independently, and every native divergence coordinate must cancel globally. Missing source parameters and fluxes are not taken as zero.

**Adversarial control:** the QDPR self-test now constructs an **undeclared transport** that preserves *global* C/H/N/O/P/charge totals but moves one real molecule between native voxels without an incidence ledger. The per-voxel checker **must reject** it, alongside interior-face, missing-reference and empty-source extraction controls. The negative-control species must have a nonzero element or charge component. These tests are **committed but not run during this connector-only turn**.

**Exact separation of claims:** the local six-coordinate Python source-consuming finite-volume checker is an **implementation/regression candidate**, not `original29x12SpatialReactionBalance` kernel acceptance. The strict 29×12 execution still requires the real source-acquired byte-pinned certificate (and three nonfinite residuals) missing from the tracked PR branch. No measured 29 environmental exchange values, original reaction turnover rates, transport permeability or PNP dynamics are supplied; synthetic fixture rates are not original biology. `original369LocalSignedContinuityExact` on #1471 remains *source-written, Golden-imported, kernel pending*.

**Updated remaining theorem order:** (P0.a) exact Agda checker for mixed original ionic continuity; (P0.b) actual original Rhea/ChEBI certificate plus indexed 29×12 matrix and source-referenced 29 exchanges; (P0.c) `original29x12SpatialReactionBalance` in Agda using existing `MetabolicStoichiometricConservation` + `MetabolicOpenSystemBalance` source owners and same 27-voxel carrier; (P0.d) `sameSourcePhysicalReactionTransportStep` with source-paid kinetics, boundary conditions, electrochemical flux and material/charge admissibility; (P1) `physicalBH4StepCommutes`, `physicalPNPStepCommutesOriginal`, `physicalTissueOneStepRefinement`; (P2) original controlled stochastic kernel and minimality; (P3) calibrated held-out independent predictions, merged Golden/ITIR lineage and referee receipts. No fabricated zero exchange, no synthetic matrix substitution, no clinical Kitzerow causality conclusion.


## 2026-11-09 continued P0 original 29×12 spatial chemistry cut

**Latest implementation:** companion BH4 PR #1454 extends `scripts/check_bh4_original_panel_spatial_events.py` without writing a substitute reaction matrix. For each *source-acquired finite original Rhea column*, the validator now checks the stoichiometric delta at **every one of the original 27 cubical positions**, at every molecular coordinate: the selected location changes by exactly the source-column coefficient; every off-location species/voxel pair remains unchanged. It independently audits global CHNOP and integer charge before/after each step. With all 12 original finite columns this implies 324 reaction-location checks and 253,692 coordinate comparisons (29 species × 27 observer voxels × 27 reaction locations × 12 columns). These are **expected counts**, not reported successful runs.

The same validator now has `boundary_species_event` and `run_original_spatial_event_history`: a single shared `3×3×3 × source-species` chronological inventory combining an original finite Rhea reaction, a genuine native 54-bond transport, and one of the six exterior-face species injections or available-material withdrawals. Every external event must have a nonblank source-reference string and an `OnFace`-equivalent genuine boundary location; an extraction removes no more than available molecules. CHNOP atom and signed electric-charge differences are matched exactly against the **explicit actual environmental ledger** at every step and across the complete history. Self-test negative controls reject interior injections and blank provenance; a request to extract from an empty site actually removes zero. Fixture source labels explicitly identify **synthetic tests** and do not count as measured exchange evidence.

**Acceptance firewall:** the amended script is **committed, not executed in this connector-only pass**. The tracked full Rhea certificate `artifacts/biology/rhea-kitzerow-bh4-reactions.json` was unavailable on the PR branch at last lookup. Accordingly, **`original29x12SpatialReactionBalance` remains OPEN as a kernel theorem and full source-backed computation**, even though the Python source-consuming all-voxel/mixed-exchange finite validator has advanced. No original 29 measured environmental exchange values, original kinetic rates or measured membrane conductances have been supplied. A source-reference string is not evidence of a measured rate.

**P0 continuity:** `original369LocalSignedContinuityExact` remains source-written and Golden-imported on #1471, **Agda kernel pending**; no changed source was type-checked here (the local workspace lacks Agda and no native repo checkout was available).

**Exact onward cut:** (1) obtain exact-head Agda acceptance for the mixed signed-current owner, (2) recover byte-pinned actual 29×12/three-residual Rhea certificate and run full original-panel checks, (3) separately source-pay all 29 environmental exchanges/compatible kinetic bounds, (4) prove `sameSourcePhysicalReactionTransportStep` on one admissible selected state, (5) source-specific BH4/PNP/tissue commutation, (6) physical stochastic lumpability/minimality, (7) independent held-out discrimination and governed Golden/ITIR reconciliation. Do not infer clinical Kitzerow causality from structural conservation.


## Canonical completion status — 9 November 2026 (latest source-written cut)

The separate **draft** heads remain developmental PR #1471 and BH4 PR #1454. They have **not** been reconciled into one accepted Golden root. The last source cut is the original `3×3×3` ternary geometry with 27 voxels, 54 real native bonds, six `OnFace` exterior faces, and a shared two-ion finite inventory. The 27-vector remains a storage chart; pants-gluing compatibility is not evidence of a membrane transfer rate.

**P0 finite signed local continuity:** `Biological369MixedNativeFaceSignedContinuityExact.original369LocalSignedContinuityExact` is **source-written and imported** into `EverythingBiologicalHistoryFutureRound23`. It derives per-voxel integer signed final-plus-outgoing = initial-plus-incoming across arbitrary chronological native cation/anion bond events interleaved with original exterior-face injection and available-material extraction. It reuses actual source/target quantum debit, no-loop cube geometry, off-endpoint locality, face-event locality and natural-number history induction. **NOT KERNEL ACCEPTED:** Agda 2.9 / native `parallel_checker` was not available in this work session. The native Golden entry requires it; a symbol grep is not a proof receipt. Separate integer/Python finite tests are not an Agda substitute.

**Other exact gates (proposed names unless source owner cited):**

| Gate | Standing | Exact unpaid result |
| --- | --- | --- |
| P0 — `original369LocalSignedContinuityExact` | Source-written, Golden-imported, **kernel-pending** | Run exact-head Agda checker, repair failures, archive full proof/import receipt |
| P0 — `original29x12SpatialReactionBalance` | OPEN | Actual byte-pinned 29×12 Rhea certificate; three nonfinite residuals; 29 independently source-paid environmental exchanges; original same-compartment balances |
| P0 — `sameSourcePhysicalReactionTransportStep` | OPEN | One nonnegative calibrated reaction–transport–circulation/PNP update with measured or defended rate/permeability/boundary assumptions |
| P1 — BH4/PNP/tissue commuting | OPEN | `physicalBH4StepCommutes`, `physicalPNPStepCommutesOriginal`, `physicalTissueOneStepRefinement` for the same specimen, region, time and physical state |
| P2 — physically minimal future state | OPEN | `physicalKernelLumpsUnderInterventions`, `physicalFutureQuotientIsMinimal` on justified interventions and observations |
| P3 — parameter identification and prediction | OPEN | `sourceCalibratedParametersAdmissible`, `heldoutFuturePredictionsDiscriminate` including alternatives, uncertainty and independent longitudinal tests |
| P3 — integrated Golden and ITIR | OPEN | Reconcile #1471 with stacked #1454; exact-head merged kernel receipt; reviewed source/PNF lineage, no automatic promotion |

**D0–D6 deliverables:** D0 checker and reconciled roots; D1 source-paid original 29×12 and ionic continuity; D2 admissible physical law; D3 tissue projection; D4 future-safe minimal quotient; D5 calibrated held-out predictions; D6 governed evidence release. The missing tracked path `artifacts/biology/rhea-kitzerow-bh4-reactions.json` on #1454 is a reproducibility blocker for the strict full-panel test, not proof the original acquisition never occurred. No Kitzerow-specific clinical causal hypothesis has been validated.

**Finite diagnostics:** independent one-step original signed-bond tests covered 23,328 charge/voxel cases; a separate seeded local diagnostic covered 884,736 signed comparisons across 256 mixed histories × 128 events × 27 voxels. The latter stress pattern was also added to the *committed* Round-23 Python regression, but the committed script itself has not been executed here.

Earlier sections below are historical implementation records; **this canonical table supersedes older OPEN labels for the source-written finite local-continuity declaration**, without upgrading kernel or empirical acceptance.


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


## 2026-11-09 synchronized cross-branch remaining maximum cut

PR #1454 and developmental PR #1471 are **not** one compiled physical state. The latter now includes a same-inventory two-native-bond conservation composition (`twoNativeCubicalBondTransfersConserveTotal`), genuine original 1→3 pants geometry, exterior face balances and finite voxelwise charge-continuity regression. **None of these establish the original physiological transport coefficients.**

| Gate | BH4 source state | Remaining lemma / source payment |
| --- | --- | --- |
| G0 | Five-species QDPR, 3D source/target spatial events, selected three-state future minimality | Exact-head Agda/parallel checker receipts and integration with developmental Golden |
| G1 | Original panel consumer `scripts/check_bh4_original_panel_spatial_events.py` reads existing Rhea/ChEBI acquired certificate; rejects fake zeros | `original29x12SpatialReactionBalance` using all 12 finite source columns, 3 nonfinite residuals and explicit 29 environmental exchange coordinates; run only with actual certificate |
| G2 | Finite shared-state transfers and source-qualified reactions | `sameSourcePhysicalReactionTransportStep` with measured rates, compartment/membrane permissions, turnover and signed currents |
| G3 | All-history conditional source bridge and QDPR redox ordering counterexample | `physicalBH4StepCommutes`, `physicalPNPStepCommutesOriginal`, `physicalTissueOneStepRefinement` on same physical specimen/state/time |
| G4 | Selected chemical future-minimality counterexample | `physicalKernelLumpsUnderInterventions`, `physicalFutureQuotientIsMinimal` for physically admissible observations |
| G5 | Source-aware measurement intake | `sourceCalibratedParametersAdmissible`, `heldoutFuturePredictionsDiscriminate`; distinguish resource allocation, redox and independent regulation |
| G6 | Separate roadmap and governance owners | Stacked #1159/#1226/#1454 + #1471 reconciliation, source-review ITIR #72, exact-head acceptance |

**Deliverables:** D0 kernel and merged-tree receipt; D1 source-paid 29×12 and local continuity; D2 admissible reaction–transport–PNP dynamics; D3 tissue observation refinement; D4 future-safe minimal quotient; D5 calibrated held-out prediction; D6 governed evidence lineage.

**Integrity controls:** geometry is original ternary 3×3×3 with a 27-vector as chart; a pants interface is not a transport coefficient; BH2 and qDHB are not conflated; an exchange coordinate is not a measured flux; exact integer event checks are not longitudinal experiments; no clinical Kitzerow causal conclusion is certified. Both PRs remain draft until independent proofs and data pay the gates.


### 2026-11-09 P0 reaction/transport composition continuation

`scripts/check_bh4_original_panel_spatial_events.py` now constructs, **per genuine original finite Rhea column**, a chemically allowed starting inventory and executes original reaction → native nearest-neighbour product transfer → reverse nearest-neighbour transfer. It asserts return to the postreaction inventory, exact conservation of C/H/N/O/P and integer charge throughout the shared original 3×3×3 state, and absence of negative molecule counts. QDPR self-test expects one composed history; the strict 29×12 path still requires the actual original acquired certificate and three explicit nonfinite residuals.

This is a stronger executable chronology test than isolated reaction and bond fixtures but is **not** physiological kinetics, membrane permeability, 29 source-paid exchange fluxes, an Agda kernel theorem, or proof of same-specimen tissue dynamics.

PR #1471 now source-writes native-bond source debit/target credit and outer-face local injection identities in Agda; these are prerequisites, **not yet** the full 27-voxel signed charge-current continuity theorem. D1 remains PARTIAL; G1/G2 still OPEN for full physical completion.

**Next exact original-P0 cut:** `original369LocalSignedContinuityExact` followed by `original29x12SpatialReactionBalance`, then `sameSourcePhysicalReactionTransportStep`. Only then seek `physicalBH4StepCommutes`, `physicalPNPStepCommutesOriginal`, and `physicalTissueOneStepRefinement` on one selected physical state.


### 2026-11-09 companion original-369 locality status

Developmental PR #1471 adds pointwise original 3×3×3 bond-support invariance for actual `transferOne` (`lookupTransferAwayFromEndpoints`, `originalNativeBondUnchangedOutsideEndpoints`) and certified exterior-face injection/extraction off-site invariance. Its signed-current regression now refuses remote compensating state mutations; native Golden owner-presence gates were added. **These are source-written proof candidates without exact-head Agda acceptance** and do not close local integer signed-current continuity.

BH4 PR #1454's `check_bh4_original_panel_spatial_events.py` still provides original source-consuming reaction→native transport→return regression, not a source-paid 29×12 physiological rate model. The 29 source-specific exchange fluxes, all P0 signed/current/kinetic coupling, P1 tissue/PNP/BH4 commutation, P2 physical minimality, P3 held-out evidence, and combined Golden acceptance all remain OPEN.


### 2026-11-09 typed-history and original source-artifact audit

Companion #1471 has source-written `OriginalDirectedNativeBond` (only genuine original nearest-neighbour forward/reverse steps), `everyChronologicalOriginalDirectedHistoryConserves` and `nativeHistoryLeavesUnvisitedVoxelUnchanged`. They constrain native 3D transport support, not PNP kinetics or measured BH4 transport, and are not exact-head kernel accepted.

**Source gate:** Lookup of `artifacts/biology/rhea-kitzerow-bh4-reactions.json` on this GitHub branch returned 404. Its absence from the tracked branch prevents reproducing strict original-panel execution here; this says nothing about off-repo acquisition receipts. A 29×12 Rhea/ChEBI identity list and a five-species QDPR self-test are not replacements for the byte-pinned full original source matrix. Maintain three nonfinite original residuals and all 29 environmental exchange obligations explicitly.

**Open:** entire signed local charge-current theorem, source-paid 29×12/29 exchange model, physically admissible same-object time evolution, actual BH4/PNP/tissue step, original controlled stochastic kernel/minimality, independent calibration/holdout, two-branch Golden and reviewed ITIR reconciliation.


### 2026-11-09 native signed-current cross-branch proof update

Developmental #1471 adds source-written `original369NativeSourceFluxExact` / `original369NativeTargetFluxExact` (actual shared-state moved quantum, 0/1 including empty source); `originalDirectedNativeEndpointsDistinct` removes external no-loop assumptions using genuine 3×3×3 ternary geometry; `originalNativeVoxelIncidenceBalance` and `original369SignedNativeOneStepContinuity` give selected role-based per-voxel and integer signed cation/anion conservation for **one** original directed native bond event; `originalBoundaryDischargeLocalReceipt` supplies matching actual exterior face debit. No Agda kernel execution receipt has been obtained.

**Still open:** complete signed/local/mixed boundary history induction; source byte-pinned 29×12 original chemistry execution and 29 physiological exchange coordinates; source-calibrated kinetics and permeability; selected physical one-step BH4/PNP/tissue commuting theorems; physical intervention-safe quotient/minimality; independent longitudinal model discrimination; reconciled Golden + authorized ITIR evidence.


## 2026-11-09 original 369 signed-local P0 source candidate

Developmental PR #1471 now contains `Biological369MixedNativeFaceSignedContinuityExact.agda`, imported into the original Round-23 Golden. Proposed `original369LocalSignedContinuityExact` source-writes a **mixed-history signed local current ledger** across actual original 54-bond cation/anion transfers and 6-face `OnFace` inflows/actual withdrawals, for each original 3×3×3 voxel. It accumulates actual nonnegative ionic in/out quanta and converts to integer signed current using existing `integerSignedCharge`. **Kernel checking was not executed; status is source-written / acceptance pending, not a certified theorem.**

Remaining P0 is principally strict exact-head acceptance, original acquired 29×12 matrix/three nonfinite residuals/29 source-paid exchanges and `sameSourcePhysicalReactionTransportStep`. P1 actual BH4/PNP/tissue agreement, P2 physical future quotient and P3 independently calibrated longitudinal discrimination remain OPEN. No Kitzerow clinical causal claim is inferred from finite algebra. Preserve separate PR lineages and existing evidence authority.
