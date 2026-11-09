# BH4 ↔ physical-tissue future-observation max-cut

## P0 highest-alpha source/math advance — 9 November 2026

**Mathematical source, BH4 PR #1454:** `DASHI/Biology/Molecular/BH4PanelStoichiometricMatrixExact.agda` now contains constructive vector-addition/weighted-dot conservation proofs for an actually available finite reaction; `original29x12SpatialReactionBalance` establishes any of five CHNOP invariants at any of the original 27 cubical voxels; `original29x12SpatialSignedChargeBalance` establishes the **net** signed molecular charge cross-sum (not false separate +/− charge-magnitude conservation); and `original29x12SpatialAllHistoryCHNOPBalance` / `original29x12SpatialAllHistorySignedChargeBalance` compose the invariants across arbitrary chronological reactions. The indexed history requires an available-reactant witness at every intermediate state, so no unearned molecule depletion is permitted. **All four statements explicitly require a `SourceCertifiedOriginal29x12` argument. The original source certificate instance remains missing. These newly written Agda declarations are NOT kernel accepted.**

**Actual source-to-Golden route:** `scripts/generate_bh4_original29x12_agda.py` demands the original full 29×12/three-residual Rhea certificate and an independently supplied exact certificate SHA256; it rejects mismatches, reconstructs reactant/product counts from original participant sides and coefficients, and emits a *generated* Agda `SourceCertifiedOriginal29x12` record with literal 29-vectors plus 60 CHNOP and 12 net-charge `refl` proof branches. The new `KitzerowBH4Original29x12SourcePaidEverything.agda` imports that module alongside the existing original BH4 Golden. `BH4_REQUIRE_SOURCE_PAID=1` now requires `BH4_ORIGINAL_CERT_SHA256` and invokes this generated-root native Agda checker, without introducing CI as an authority or filling in missing source rows. **The strict generated module has not been built or typechecked here**, because the exact original certificate is not present.

**Historical vintage correction:** original acquisition `acquire_rhea_chebi_bh4_reactions.py` hardcoded an outdated Rhea release 142 / SPARQL 2026_03 label into arbitrary fresh live responses; now it marks releases unverified by default and optionally parses/compares the live REST homepage with `--require-rhea-release`, refusing an expected-vintage mismatch before acquisition. The Rhea public homepage reports current REST release **143 (2026-11-04)**; the earlier October 2026 certificate cannot be silently reconstructed from today's release and called byte-identical. The actual SPARQL release remains separately unverified. A pure offline release-parser self-test is included in the Golden script. Hashes and source references do not by themselves verify authenticity.

**Remaining max-cut:** P0 original ionic `original369LocalSignedContinuityExact` remains source-written/Agda acceptance pending on PR #1471; BH4 source-*conditional* 29×12 mass and signed history theorems now source-written/Agda pending; **actual Rhea source certificate construction and signed/CHNOP kernel acceptance still OPEN**. `sameSourcePhysicalReactionTransportStep` still lacks a source-paid chemical–PNP constitutive law (permeability, calibrated ionic currents, boundary physics, compartment selection); P1 original BH4/PNP/tissue commuting, P2 physical stochastic lumpability/minimality, P3 independent parameter identification and held-out discrimination plus merged Golden/ITIR review remain open. The self-contained finite algebra has advanced; physical claims are not inferred from it.


**P0 proof-repair checkpoint (9 Nov 2026):** Exact source audit found that `Biological369CubicalOpenSignedChargeExact.swapAccumulatedCurrent` used `sym (+-assoc a b c)` where `+-assoc a b c` was required. On developmental #1471, this has been repaired and simplified to `trans (+-assoc a b c) (Faces.exchangeAssociative a b c)`, consuming the **existing** outer-face arithmetic proof rather than duplicating it. This lemma is used in both chronological positive/negative native-current inductions feeding `original369LocalSignedContinuityExact`. Independently, its arithmetic spine passed 274,625 finite Nat triple tests (0–64 each), which is a numerical check, **not Agda acceptance**. Local toolchain check: no Agda executable installed; Git checkout blocked by DNS; no latest PR workflow run available. Status remains source-corrected, **kernel not run / not closed**. Do not infer the remaining original Rhea 29×12 source certificate or physical PNP/kinetic rates from this correction.


## 2026-11-09 maximum-cut: original flux-bound provenance and Golden acceptance hardening

**Latest implementation on BH4 #1454:** `scripts/check_bh4_original_panel_spatial_events.py` now calls `audit_original_reaction_flux_bounds` before the existing `run_bh4_flux_feasibility.evaluate` for the strict source-backed 29×12 candidate. It rejects duplicate `parameter_id` entries, conflicting paid aliases for the same original Rhea column, unsupported payment statuses, inverted/malformed rational bounds and missing nonblank source references. Missing/unresolved bounds still yield an explicitly **underdetermined** candidate; they are not zeroed or promoted. Its self-test includes synthetic negative controls for duplicates, unknown status, negative ordering, empty provenance and `NaN` bounds. Its result includes an explicit `original_bound_audit` field; source references and statuses remain declarations, *not* independent physical evidence.

The native `scripts/check_bh4_spatial_golden.sh` now has `BH4_REQUIRE_SOURCE_PAID=1` strict input mode. It requires a nonempty original Rhea certificate, quantitative parameter receipt, 12-flux/29-exchange candidate and original longitudinal assay before proceeding. Default mode is still useful for synthetic regressions and Agda checking but prints that real original physical/source evidence remains **OPEN**. Strict completion also explicitly leaves independent kinetic validation and causality OPEN. No CI dependency or altered Agda Golden checker has been introduced.

**Acceptance:** the changes were written and committed through GitHub; neither the changed Python self-test, the native Agda 2.9 checker, nor the complete strict 29×12 calculation has run on this head here. Earlier source-written `original369LocalSignedContinuityExact` on developmental #1471 remains Golden-imported but **kernel-pending**. `original29x12SpatialReactionBalance` and `sameSourcePhysicalReactionTransportStep` remain **OPEN physical/formal gates** despite this stronger executable provenance-and-conservation checking. P1 physical BH4/PNP/tissue commutation, P2 intervention-safe stochastic physical minimality, P3 source-calibrated parameters and independent held-out predictions, and integrated Golden/ITIR evidence receipts remain unpaid. Recover primary source bytes and measured rates; no synthetic sample, balance witness, or source-label string alone pays original physiological flux.


## 2026-11-09 selected assay-to-flux state identity, P3/P0 bridge (latest)

On BH4 PR #1454, `check_bh4_original_panel_spatial_events.py` now optionally accepts `--assay ORIGINAL_LONGITUDINAL_CSV` alongside the strict Rhea certificate, 12-flux/29-exchange candidate and source-bound parameter inputs. It **reuses** the pre-existing `check_bh4_spatial_measurement_payment.read_assay` gate and verifies the submitted candidate identifies an *actual parsed original assay row*: matching whole-assay SHA256, upstream declared source ID and digest, experiment ID, specimen ID, numeric original time, region and compartment. Calibration may use only source-labelled train/validation rows, **never a held-out test row**; missing, mismatched or nonfinite data fail closed. The script includes a reproducible 4-experiment/2-time/2-compartment **synthetic-only self-test** that rejects wrong source SHA, time, region, experiment or held-out specimen. The optional Golden setting is `BH4_ORIGINAL_ASSAY_PATH`. The code only asserts that a candidate refers to a matching assay row; it does **not** derive flux rates from BH4/BH2 concentrations, establish a source physics causal mechanism, validate upstream source digests independently, or prove an Agda commuting theorem.

**Evidence/acceptance:** code and tests are source-written/committed, not executed in this tool session. A locally executable independent 54-bond finite signed-charge spot check passed, but is not the committed full-panel Python suite or an Agda receipt. The original real 29×12 Rhea bytes, source-paid 29 per-species exchanges and kinetic data remain unavailable; `original29x12SpatialReactionBalance`, `sameSourcePhysicalReactionTransportStep`, `physicalBH4StepCommutes`, `physicalPNPStepCommutesOriginal`, `physicalTissueOneStepRefinement`, `physicalKernelLumpsUnderInterventions`, `physicalFutureQuotientIsMinimal`, `sourceCalibratedParametersAdmissible` and `heldoutFuturePredictionsDiscriminate` are still OPEN. The original 369 finite signed continuity owner remains Golden-imported but Agda kernel pending; no inferred clinical Kitzerow mechanism.

**Next max-cut:** run the exact source AST/Python self-test and both Agda Golden roots on checked-out heads; retain negative controls as acceptance criteria; acquire source certificate and actual experimental measurements before instantiating one physically admissible chemical–PNP–tissue state. Match source provenance at specimen/time/region/compartment and enforce train/heldout segregation throughout model fitting. Only after those receipts can evidence-backed P2/P3 promotion and reviewed ITIR reconciliation be considered.


## 2026-11-09 strict-source P0 repair / reproducible receipt (current)

**Implementation repairs, BH4 PR #1454:** three accidental literal `\\n` source tokens that made `check_bh4_original_panel_spatial_events.py` invalid Python were removed; the native BH4 Golden script now AST-parses that file before its fixture and original-certificate runs. Strict source ingestion rejects duplicate JSON keys and nonstandard `NaN`/`Infinity`, and the 29×12 candidate axis guard rejects surplus/invented reaction or species keys without conflating missing values with zero. The optional supplied 12-flux / 29-exchange feasibility check reuses `run_bh4_flux_feasibility`; it returns exit status **2** on incomplete/underdetermined or infeasible candidates rather than appearing to accept them. Its quantitative receipt now pins SHA-256 hashes of the exact Rhea certificate, parameter receipt and candidate bytes, while explicitly retaining `source_digest_independently_verified = false`, `kinetic_measurements_independently_validated = false` and `itir_pnf_promotion_performed = false`. These are reproducibility hashes, not authoritative provenance attestations.

**Exact acceptance boundary:** GitHub fetch-back verifies that the changed source, Golden preflight and roadmap contents are committed. The actual AST preflight, Python self-tests, strict original 29×12 calculation and Agda 2.9 Golden type-check have **not been executed in this environment**; source-writing alone does not close P0. The true original acquired Rhea certificate, source-paid 29 exchange values, physical membrane/PNP laws and independently measured reaction kinetics remain missing from the tracked inputs here. `original369LocalSignedContinuityExact` remains source-written/kernel-pending; `original29x12SpatialReactionBalance` and `sameSourcePhysicalReactionTransportStep` remain OPEN, followed by P1 one-step commutation, P2 physical stochastic minimality, P3 held-out discrimination and integrated Golden/ITIR referee reconciliation.


## 2026-11-09 source-integrity repair and strict quantitative gate (latest)

The latest BH4 #1454 original-panel Python validator contained **three literal escaped `\\n` fragments in source code, making it syntactically invalid**. Commit `4c05562` replaces them with actual source newlines. Subsequent work adds: (a) `require_exact_flux_candidate_axes`, rejecting surplus reaction or molecular-species keys that the existing general feasibility checker could ignore, while preserving **underdetermined** status for missing coordinates; (b) `load_original_receipt_json`, which rejects duplicate object keys and nonfinite `NaN`/`Infinity` literals in the source certificate, rate-bound receipt and candidate, avoiding silent JSON key overwrite; (c) strict `--parameters`+`--candidate` mode exits **nonzero** on any `underdetermined` or `infeasible` result rather than printing an apparent success; and (d) `scripts/check_bh4_spatial_golden.sh` now uses AST syntax parsing **before** executing the source-backed validator.

**Acceptance:** these changes are committed and retrieved from GitHub; an Agda 2.9 kernel receipt or exact execution receipt for the revised original 29×12 validator was **not** obtained. The original source file, 29×12 output matrix, and quantitative parameter receipts remain absent at their expected tracked branch paths. Do not promote a source presence check or AST-in-script existence to successful execution. `original369LocalSignedContinuityExact` remains source-written, imported, *kernel pending*. `original29x12SpatialReactionBalance` and `sameSourcePhysicalReactionTransportStep` remain OPEN beyond the source-aware Python event/flux verification code.

**Next exact max-cut:** run the BH4 Python AST/self-test and the native Round23 + BH4 Agda checkers on their exact heads; correct reported failures; recover the real Rhea certificate and source-measured rates/exchanges; pay the original 29×12 per-species/per-compartment conservation and chemical–PNP physical update; then same-object P1 tissue, P2 physical kernel minimality, P3 independent calibration/held-out prediction and Golden/ITIR reconciliation. No synthetic controls or declared measurement reference alone count as empirical provenance.


## 2026-11-09 — strict original 29×12 flux and 27-voxel local-continuity cut (latest)

The source-owner `scripts/check_bh4_original_panel_spatial_events.py` on BH4 #1454 now (a) verifies **each local C,H,N,O,P and integer signed-charge conservation equation at all 27 original cubical voxels after each chronological finite reaction/native transport/exterior-face exchange event**, using actual available transfer/outflow and signed incidence divergence, and (b) rejects compensating undeclared remote transfers that preserve the global quantities but violate local continuity. The all-voxel exact-coordinate checks now run for all **source-acquired finite** Rhea columns *when the original certificate is mounted*. The changed Python source and self-tests were committed, **not executed in this connector-only session**.

The optional strict quantitative path `--certificate ORIGINAL --parameters SOURCE_BOUNDS --candidate FLUX_EXCHANGE_CANDIDATE` now **reuses** existing `run_bh4_flux_feasibility.evaluate` (rather than inventing a parallel optimizer) to check all 12 original reaction flux coordinates and 29 explicit species exchange coordinates against source-paid bounds and `S v + e = 0`. It returns `underdetermined`/other algebraic status when paid coordinates are missing, and a separated `feasible-algebraic-only` when complete and balanced. Same-state and measurement references must be nonblank/non-synthetic before even exposing a complete witness; these fields are *assertions submitted by the caller*, not independently verified measurements. It **never** reports physiological kinetics, validated membrane flux, a PNP/tissue commuting theorem, disease causality or source calibration as proved.

`scripts/check_bh4_spatial_golden.sh` now optionally invokes the strict candidate bridge when both `BH4_ORIGINAL_PARAMETERS_PATH` and `BH4_ORIGINAL_CANDIDATE_PATH` are supplied and the original Rhea certificate exists. Without complete source evidence it explicitly reports the OPEN PHYSICAL RATE GATE. Default synthetic self-tests remain labelled synthetic. **Neither the new strict quantitative path nor the changed Golden script has been executed here.**

**Updated exact remaining:** `original369LocalSignedContinuityExact` is source-written/Golden-imported on developmental #1471 but **Agda kernel pending**; `original29x12SpatialReactionBalance` remains **open as original certificate-backed Agda proof**, despite its enhanced Python same-object local conservation checks; `sameSourcePhysicalReactionTransportStep` remains **open as calibrated PNP/chemical physical dynamics**. P1 `physicalBH4StepCommutes`, `physicalPNPStepCommutesOriginal`, `physicalTissueOneStepRefinement`, P2 `physicalKernelLumpsUnderInterventions`, `physicalFutureQuotientIsMinimal`, and P3 `sourceCalibratedParametersAdmissible`, `heldoutFuturePredictionsDiscriminate` plus integrated Golden/ITIR remain **open**. Next requirements are original acquired byte-hashed 29×12 Rhea source, rate and compartment evidence, Agda exact-head receipts, physical model selection, independent validation and reviewed reconciliation. Preserve original 3×3×3 and pants semantics, original QDPR species identity, source attribution and no automatic promotion.


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
