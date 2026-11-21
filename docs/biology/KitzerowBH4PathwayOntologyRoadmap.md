# Kitzerow BH4 pathway ontology and executable-network roadmap (2026-11-02)

## Canonical reactive-PNP P0–P3 exact lemma inventory — 2026-11-09

**Current owner:** [BH4ReactivePNPExactRemainingMaxCut.md](https://github.com/chboishabba/dashi_agda/blob/feat/kitzerow-bh4-pathway-ontology-interop/docs/biology/BH4ReactivePNPExactRemainingMaxCut.md). It enumerates G0.01–04, S0.01–04, P0.01–08, P1.01–03, P2.01–02 and P3.01–03; existing declarations are distinguished from proposed declarations and from source/empirical receipts. It supersedes older repeated status summaries below without converting any open physical gate into a proof.

**Attribution:** the user's 369/ternary 3×3×3/pants and actual 54-bond cubical semantics are pre-existing prior art; the externally published reactive-PNP, mass-action thermodynamics and SG method are credited to their researchers; the assistant's three-species numerical reference is implementation assistance and an explicitly synthetic fixture, not BH4 measurement or scientific priority.

**New work:** numerical reference and its 8 tests committed to the BH4 branch; 4 additional local source-adapter negative-control tests passed but adapter remains a local artifact. 12/12 combined local tests; no original 29×12 execution or Agda 2.9 kernel receipt. Strict nonzero-exchange/reactive-electrode and multi-compartment cases remain unimplemented, not 'assumed blocking'. See the canonical gate table before writing new status updates.


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


**Source-artifact reproducibility audit (same branch):** the tracked paths `artifacts/biology/uniprot-kitzerow-bh4-panel-certificate.json`, `artifacts/biology/rhea-kitzerow-bh4-reactions.json`, and `artifacts/biology/bh4-stoichiometric-matrix.json` were not fetchable through GitHub at this head. The original acquisition program `scripts/acquire_rhea_chebi_bh4_reactions.py` **is present**. Re-execute the source-owned acquisition/build chain with versioned original records and independently review byte hashes; do not infer absent historical acquisition, or claim full-panel Golden execution from stored dimension counts.

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


## 2026-11-09 concrete spatial QDPR and future-minimality completion cut

## 2026-11-09 source-guarded original 29×12 spatial chemistry cut

The existing original BH4 acquisition and stoichiometry pipeline is
reused, not forked:

- `acquire_rhea_chebi_bh4_reactions.py` owns the original
  16-protein Rhea/ChEBI source certificate;
- `build_bh4_stoichiometric_matrix.py` owns the original
  deterministic **29-species × 12 finite reaction** matrix and
  three independently retained nonfinite MTOR residuals;
- `run_bh4_reaction_network.py` owns source-specific
  molecular element and charge audits.

New `check_bh4_original_panel_spatial_events.py`
consumes that *actual certificate* (when supplied):

1. Rebuilds the existing matrix and refuses a source
   schema, reaction identity, species count, reaction
   count or residual discrepancy.
2. Re-audits original participants, molecular formulas
   and charges; a mismatched species or unbalanced
   Rhea column is rejected. Zero columns cannot
   silently pay missing chemistry.
3. Constructs **one shared 3×3×3 physical inventory
   with all original source species**.
   Every selected original reaction may execute as
   a finite nonnegative event at a selected voxel
   only if all original reactants exist.
4. Recomputes original CHNOP and native signed
   electric charge before and after each reaction.
   Performs all 54 native bonds × both directions
   × all original source species as one shared-state
   conservative transfer experiment.
5. Explicitly refuses to infer original 29 external
   exchange rates or physiological enzyme/transport
   rates from the internal stoichiometric matrix.

Its source-only `--self-test` consumes real
`RHEA:32253` QDPR molecular chemistry (5 species,
1 original reaction), NOT a fabricated 29×12.
The dedicated `check_bh4_spatial_golden.sh` additionally
runs the strict full 29×12 checker **only when**
`artifacts/biology/rhea-kitzerow-bh4-reactions.json`
is actually present; otherwise it reports an explicit
source-artifact-open residual. The aggregate regression
also runs the nonpromoting QDPR self-test.

The developmental companion #1471 now keeps the semantic
3D cube, pants gluing, six original exterior faces
and exact source/sink signed charge separately from
its lossless `Vec Nat 27` material chart. Its
`allOriginalBoundaryExchangeHistoriesBalance` and
`originalFullSpatialOpenSignedChargeBalance`
provide the formal original-cube open-system
conservation architecture needed by a multi-species
physical source-weld. No automatic informational
pants seam → measured flux is asserted.

**Still outstanding:** actual original certificate
must be mounted and the full 29×12 audit executed;
all 29 environmental exchange rates must be
physically source-paid for a specified shared
specimen/compartment/time; transport/PNP kinetics,
whole-tissue phenotype reduction and independent
measured outcomes remain open. Neither a self-test
nor source-written Agda is kernel/physiology proof.



### 2026-11-09: original five-species Rhea 27-site finite-volume instance

New `scripts/bh4_original_qdpr_spatial_finite_volume.py` is a
concrete, exactly source-identified **internal chemical
reaction plus spatial material transport** model:

- Original source: Rhea `RHEA:32253`, human-cytosol
  Reactome `R-HSA-71130.5`; original five species
  `CHEBI:43120` qDHB, `CHEBI:57945` NADH,
  `CHEBI:15378` proton, `CHEBI:59560` BH4,
  `CHEBI:57540` NAD+. No generic BH2 promotion.
- A single **27-site × five-species shared nonnegative-integer
  inventory**; 54 native actual nonperiodic 3D positive bonds,
  both transfer directions, original species and independently
  explicitly source-qualified transport permissions.
- QDPR chemistry permits selected integer reaction events
  ONLY in source-modelled human cytosol; it deducts all three
  original reactants and credits both actual products.
  Synthetic rate/event count is not measured.
- Every internal selected event preserves the real source
  **CHNOP atom vector and signed net electric charge**.
  Environmental inflow/outflow has independently explicit
  element and charge accounting; no silent exchange or
  "plasma equals cytosol" promotion is possible.
- Synthetic positive chain: source-cytosolic QDPR reaction
  produces original BH4; then a separate *permitted* native
  spatial transfer moves its original species identity to
  another voxel. This does not establish human in-vivo
  intracellular BH4 mobility or cell membrane permeability.
- The self-test exercises all
  **54 bonds × two directions × five actual molecular species =
  540 source-typed internal transfer cases**, plus the original
  QDPR molecular reaction, invalid compartment, denied
  transport, wrong directional Rhea/Reactome identity,
  missing substrate and overdraw.
- Independently reproduced in local exact Python arithmetic:
  540 source-species/edge chemical inventory and charge
  conservation tests passed. This is **not** a run receipt
  for the committed source file.
- The script is registered in `check_kitzerow_bh4_priority_all.py`
  and `check_bh4_spatial_golden.sh` (whose final step invokes
  the native repository parallel Agda checker).

**What L05 now means:** Original Rhea/Reactome *single QDPR
reaction* is source-identified and exact finite molecular
stoichiometry is conserved by the spatial executable model.
The complete actual 29-species × 12-reaction internal panel,
29 environmental exchange/transport intervals, source-qualified
concentration/time-dependent kinetics, PNP coupling and
clinical or physiological validation remain UNPAID. Importing
the executable result into the Agda source-owner kernel
requires a proved same-object refinement, not a receipt name.
No numerical rate or tissue causal inference is asserted.



### Updated 2026-11-09 geometry closure in developmental companion

The developmental PR #1471 has progressed past the previous
27-site Python-only conservation fixture:
`BiologicalSharedFiniteVectorTransferExact` now supplies
a generic **shared `Vec Nat n`** source/target transfer
with exact nonnegative sequential material conservation, and
`BiologicalOriginal54BondSharedVectorExact` builds the
**actual inverse 27-point↔Fin indexing**, transfers original
nearest-neighbour proof witnesses and identifies all 54
native bonds. Its original forward/reverse bond sweeps
and arbitrary histories share one 27-site material state.

This discharges the *source-written single-species original
spatial-incidence conservation* portion of L03, not the
real multi-species 29×12 mass/charge/energy,
membrane permeability, circulation or QDPR kinetic proof.
As #1454 does not yet include the full #1471 Golden
head, these are **cross-branch** owners only; no compiled
merged same-head certificate or original physical law
is asserted. The next highest-value cut is the exact
original QDPR cytosolic chemistry plus selected
species-specific boundary transport and measured rates.



These are newly **constructed selected finite physical dynamics**,
not just typed future interfaces:

- `BH4SharedSourceTargetRedoxDynamicsExact.agda`: one *shared*
  original source BH4/target BH4/target oxidized-pterin inventory.
  Source delivery, local oxidation, recycling and external injection
  all mutate the SAME state; `oneStepOpenSystemBalance` and
  `allControlledHistoriesPreserveOpenBiopterinBalance` prove
  conservative moiety transport (and paid external supply) for
  every chronological intervention word. The witness
  `deliveryAndOxidationDoNotCommute` proves location/control
  timing matters: deliver then oxidize differs from oxidize then
  deliver. The oxidized proxy is not automatically qDHB.
- `BH4SpatialOriginalQDPRStoichiometryExact.agda`: original,
  human cytosol source-pinned chemical reaction
  `RHEA:32253`/`R-HSA-71130.5`:
  **q-6,7-dihydrobiopterin + NADH + H+ -> BH4 + NAD+**.
  Reuses `BH4MolecularStoichiometryExact.qdprAtomsConserved`
  and `qdprChargeConserved` (C30 H41 N12 O17 P2,
  net -1 both sides). `genericBH2IsNotExactQDHB`
  prevents silently promoting an unspecified BH2 measurement
  into the original reaction's qDHB substrate.
  Source species, identities and cytosol are paid; measured
  enzyme rate, transport and same-specimen time course are not.
- `BH4OneMoleculeSpatialFutureMinimalityExact.agda`:
  a selected invariant one-moiety physical subsystem has 3
  local/redox states and 4 controls (hold, deliver,
  oxidize, recycle). `selectedOriginalPhysicalStepCommutes`
  shows the three-state subsystem is the same shared
  redox transport update. Its target-oxidation readout
  distinguishes **all three future classes**;
  `futureEquivalentImpliesIdenticalPhysicalState` and
  `identicalPhysicalStateImpliesFutureEquivalent` prove
  exact minimality for the stated observation/intervention
  language. `globalMoietyCountCannotPredictAllSelectedFutures`
  proves a constant total cannot replace the located state.
- Python strict source/finite regressions:
  `check_bh4_shared_redox_dynamics.py`
  exhausts 125 start states × all selected history words
  of length 0..4 (97,625 exact history combinations).
  `check_bh4_original_qdpr_spatial_reaction.py`
  verifies actual Rhea/Reactome cytosol provenance,
  original molecular species, exact CHNOP and net-charge
  invariants, refuses fabricated plasma compartment and
  reversed/unrelated identifiers.
  `check_bh4_one_molecule_future_minimality.py`
  enumerates all 5,461 controlled future words through
  length 6 per state and checks the exact minimal
  three-class partition.
  All are registered in the original aggregate and in
  `scripts/check_bh4_spatial_golden.sh`.

**Independent source verification on 2026-11-09:**
https://www.rhea-db.org/rhea/32253 ;
https://reactome.org/content/detail/R-HSA-71130.5 ;
https://www.uniprot.org/uniprotkb/P09417/entry .
Rhea 32253 is the **specific directional form** related to
the broader original UniProt 17869 QDPR chemistry.
Source identity does not imply equivalent cellular contexts,
measured rate, patient condition or a validated mechanism
for Kitzerow's proposed allostatic hypotheses.

**Remaining highest-value physical acceptance cut:**
(1) Agda kernel /`parallel_checker` receipts for the exact
new Golden heads; (2) merge/reconcile BH4 #1454 with
developmental #1471 without source ownership loss;
(3) a 27-site/54-bond shared-state Agda transfer with
actual source-reaction/transport and explicit boundary
supply (not merely edge-local proofs or Python fixtures);
(4) measured same-object BH4/qDHB/BH2/NADH/NAD+,
compartment volume, exchange, vascular and membrane
time-course rates; (5) physical-to-tissue stochastic
transition and heldout independent intervention
predictions; (6) retained ITIR source-review/PNF gates.

**This first physical event model is formally meaningful but
not an independently calibrated physiological model, clinical
therapy, diagnosis or proof of the entire mechanism.**

## 2026-11-07: Physical location, connectivity and circulation max-cut

### Source and Golden acceptance command

The spatial BH4 theorem suite now has a dedicated single entry point:

```bash
bash scripts/check_bh4_spatial_golden.sh
```

This runs the finite exact allocation, circulation and source-specific
measurement-schema regressions, performs a source safety scan of the
four Agda spatial/catalytic/physical owners and invokes the
**existing repository-owned parallel Agda checker** against
`DASHI/Biology/KitzerowBH4EvidenceEverything.agda`.
It does not call the Agda executable directly and does not invent
a checker-success receipt. The script is source-written, not executed
on this head. Actual same-source physiological calibration and
independent measured data remain separate gates.



**Correction to well-mixed resource model:** The *physical state*
must include source-qualified **location, compartment, boundary,
connectivity, direction, perfusion, clearance, BH4/BH2 redox state,
substrate access and measurement time**. The selected Rhea/ChEBI
29×12 stoichiometry by itself cannot identify which cells or tissues
receive BH4 or an accessible metabolic precursor.

New original Agda source owners:

1. `BH4SpatialConnectivityCirculationExact.agda`
   reuses `FiniteElectrodiffusiveMovingBoundaryExact` for a finite
   source-to-target conservative transfer. Its selected directed graph
   distinguishes local diffusion, cell-gap junction, plasma membrane,
   vascular perfusion, interstitial transport and BBB transfer.
   `globalInventoryCannotDetermineLocalDelivery` is a genuine
   **same-total, different-target** finite counterexample.
   `reversePathNotProvided` proves that a selected forward
   connection does not automatically supply a reverse route.
   `totalsAloneCannotDetermineLocalCofactor` proves an even stronger
   redox example: the same **global BH4 AND BH2 totals** can have
   different target-local available reduced cofactor.
2. `BH4PNPSamePhysicalHistoryBridgeExact.agda` now requires a
   typed `ContextIndexedCirculation`, a source-identical selected
   PNP model, physical-to-location/compartment maps, and a
   `permittedStepRoute` for each selected physical transition.
   `physicalTrajectoryHasSourcePermittedRoute` proves by
   concatenation that every finite controlled physical history
   follows an admitted original-source directed route. This joins
   the existing BH4 and PNP all-history identities, **but not**
   a calibrated physical circulation law.
3. `scripts/check_bh4_spatial_circulation.py`
   provides a deterministic directed-reachability, conservation,
   local BH4/BH2 and membrane-gating numerical regression.
4. `scripts/check_bh4_spatial_measurement_payment.py`
   is an original-source interface for measured **compartment
   concentration × measured volume = amount**; it requires SHA
   provenance, original source, experiment, specimen, split,
   repeated times, region, compartment, original transport
   reference and both BH4/BH2 measurements. It refuses cross-group
   specimen leakage, unmeasured volume/compartment context and
   unsupported transport modes. Its default aggregate mode is an
   explicitly labeled **synthetic-only self-test**. Real source
   data are *not* bundled and concentration differences are never
   promoted into measured flow rates.
5. Both new executables are wired into
   `scripts/check_kitzerow_bh4_priority_all.py`. The formal owners
   are imported into `KitzerowBH4EvidenceEverything.agda`.

**Primary physiological references and limitations:**
- Tetrahydrobiopterin endothelial recycling/transport review:
  `https://pmc.ncbi.nlm.nih.gov/articles/PMC5357050/`.
  A review source does not itself authenticate experimental
  measurements from every original cited paper.
- Redox, endothelial NOS and compartment-specific BH4/BH2:
  `https://pmc.ncbi.nlm.nih.gov/articles/PMC4038990/`.
- Transport, intracerebral access and BBB:
  `https://pmc.ncbi.nlm.nih.gov/articles/PMC8573752/`.
- Endothelial/vascular treatment differences:
  `https://pmc.ncbi.nlm.nih.gov/articles/PMC4273464/`.

**No clinical promotion.** Mechanistic proposals in the Kitzerow
source registry remain source-graded and distinct from curated
BH4 biochemistry. No tissue-specific numerical permeability, perfusion
pressure, clearance rate or BH4 transport rate has been inferred from
an uncalibrated graph edge. One cannot substitute plasma BH4 for
intracellular BH4, or local tissue adjacency for vascular
connectivity, without independent physical evidence.

The remaining **physical same-object gate** is a source-supported
species- and region-indexed reaction/transport law, matched measured
connectivity and compartment volumes, measured boundary sources,
simultaneous branch/enzyme turnover, and same-specimen time-series.
The 29×12 matrix and 29 exchange coordinates must remain separately
paid. The new ITIR candidate consumer PR #72 preserves these
spatial coordinates without creating a competing PNF compiler.
The PRs remain branch-separated and kernel acceptance pending.



## 2026-11-07: Future-sufficiency and catalytic-throughput exact cut

### Same-source BH4 ↔ electrodiffusion all-history theorem

`BH4PNPSamePhysicalHistoryBridgeExact.agda` imports the *existing*
`BH4CompartmentKineticStateExact` and
`PoissonNernstPlanckElectrodiffusionExact`, rather than constructing
another metabolic or electrochemical state calculus.

Its `SameSourceBH4PNPModel` requires **one** `PhysicalState`
and original source/specimen/compartment/time references. Both the
BH4 quantitative state and PNP coupled state are projections of that
same carrier. The required `bh4StepCommutes` and
`pnStepCommutes` fields are explicit original-physical
model obligations, not postulates of real-world truth.

`allBH4ControlledHistoriesSamePhysicalSource` and
`allPNPControlledHistoriesSamePhysicalSource` prove their respective
all-intervention-history compatibility. The independent
`allHistoriesRemainOnOriginalBH4System` preserves the original
BH4-system identity at every derived physical history state.

This completes the formal **same-source history transport theorem**,
not kinetic calibration or the proof that actual BH4 and ionic
transport states satisfy the selected one-step laws. The corresponding
all-history 54-bond tissue theorem is on separate developmental PR
#1471. The two formal proof owners must be reconciled into one Golden
tree before there can be a *joint* kernel acceptance receipt.



The previous *resource-pool scalar* representation is now subjected to
two independent source-written Agda falsification tests:

- `BH4AllocatorFutureObservationCountermodelExact` supplies two
  selected nonnegative throughput-budget allocations with identical
  total supply (one synthetic unit) and exact finite accounting, but
  different hydroxylase-branch response. It proves
  `supplyOnlyNotSufficientForBranchFuture`. **This is an
  allocation-capacity abstraction**, not a physically calibrated
  stoichiometric BH4 sink equation: BH4 is recyclable.
- `BH4CatalyticTurnoverFutureCountermodelExact` supplies two
  toy catalytic scenarios with the *same BH4 molecule count* but
  different turnover capacities and proves
  `samePoolDoesNotDetermineEffectiveTurnover`.
  Catalytic turnover cannot be inferred from pool amount alone.

Both are imported into `KitzerowBH4EvidenceEverything.agda`.
The exact bounded enumeration in
`scripts/check_bh4_allocator_future_observer.py` is invoked from
`scripts/check_kitzerow_bh4_priority_all.py`.

**Physical implication:** the proposed future-state observer must retain
source-evidenced compartment, recycling/oxidation and effective
branch-specific throughput; mere pathway-ID coverage, steady-state
balance or a scalar BH4 pool cannot uniquely determine downstream
results. No published clinical causal result follows from these
countermodels.

**Cross-branch physical programme:** see
`docs/biology/BH4PhysicalTissueFutureObservationMaxCut.md`.
Developmental PR #1471 separately owns
`BiologicalSourcePhysicalTissueSimulationExact`, which proves the
arbitrary-history 54-bond tissue projection conditional on a
source-paid PNP/physical step. We have not imported either branch into
the other's Golden root, because #1454 is stacked on older ancestors.

**Remaining decisive receipts:** matched original BH4/BH2 redox and
QDPR/TH/TPH/NOS/AGMO kinetics and isotope/recycling rates, enzyme
abundance, transport and compartment/time identities; exact original
29×12 S*v+e evidence, independent kinetic/flux calibration;
controlled model-discriminating interventions, replication and
source-anchored ontology review; exact-head parallel_checker/kernel
acceptance and branch reconciliation.



## Correction: creator's published reaction chart is the first source

On 2026-11-02 we checked Kitzerow's original *BH4/Folate/Cobalamin/
Homocysteine Pathway* (ResearchGate publication 377218425, declared
January 2024, public full text reports later 2025-08-08 upload).
The chart explicitly includes Rhea reaction numbers, enzyme/cofactor labels,
substrates and products. The initial source-observed Rhea-ID index is
docs/biology/KitzerowPublishedRheaChartObservedIndex.v1.json.
There is now a reproducible candidate-only source-text extractor for
a user-authorized local copy of the public chart text. It supports the
publisher's observed private-use glyph representation of "Rhea", records
input SHA-256 plus line/column per occurrence, and does NOT redistribute
source text or turn web-text lines into invented PDF page anchors:

    python3 scripts/index_kitzerow_chart_source_text.py \
      --source-text YOUR_AUTHORIZED_CHART_TEXT.txt \
      --source-revision "publisher display 2025-08-08; independently unverified" \
      -o artifacts/biology/kitzerow-chart-source-text-candidates.json

Each output is explicitly an unverified source-observation candidate until
the real original figure/source and curator-approved mapping are checked.
### Source-observed / golden-panel first comparison (literal Rhea ID only)

The eight independently located identifiers in the publicly displayed
Kitzerow chart have **zero literal-ID overlap** with the twelve finite Rhea
IDs in the existing Agda golden owner
DASHI/Biology/Molecular/BH4ExecutedPanelReactionReceiptExact.agda.
The test scripts/check_kitzerow_primary_chart.py reads that actual
Agda owner, rather than copying a second list, and checks 0/8/12
identity intersection and symmetric differences.

This shows the 12-reaction DASHI subset is not a textual copy of these
eight source-chart reaction references. It does **not** show biochemical
pathway disjointness: directional Rhea IDs, protonation/microspecies,
stoichiometry, nested events, biological compartment and family mappings
may differ. It is not the correct creator-network coverage fraction,
because the entire creator chart and proprietary source network have
not been exhaustively acquired or checked.

The original full chart/PDF binary and layout remain unverified; these
initial eight directly identified codes are a **bounded observation**,
not the creator network's full reaction set. The creator's site says the
underlying complete BioGene network is proprietary.

This corrects the original approach: the independent 16-protein/12-reaction
DASHI selection is a *comparison* panel, not a proxy for the whole original
Kitzerow network. A new exact-ID crosswalk reports intersection,
chart-observed-only, and finite-panel-only without inventing whole-network
coverage:
    
    python3 scripts/compare_kitzerow_primary_chart.py \
      --matrix artifacts/biology/bh4-stoichiometric-matrix.json \
      -o artifacts/biology/kitzerow-primary-chart-rhea-crosswalk.json

### Existing generic ITIR/SensibLaw external-ontology architecture

We missed the original source owner in our earlier roadmap. SensibLaw
already implements a provider-neutral external-graph bridge, revision-pinned
incomplete/complete coverage, typed candidate external attachments,
independent review decisions, and external pressure results.
Its generic CandidateWorldModel and linkage_adapters provide an
existing source -> candidate -> external -> review -> tranche workflow.
ITIR's 2026-07-16 generic world model and 2026-07-04 linkage adapter kit
explicitly prohibit one new compiler per lane.

Native consumer PR: https://github.com/chboishabba/SensibLaw/pull/512
uses only these generic structures; this DASHI branch remains the
formal/source producer. These changes do not assert same-object
runtime correspondence with an independently executed SLR/ITIR/SensibLaw
receipt.

Reactome already provides independently curated **SBML Level 3** and
**BioPAX Level 3** event exports, plus UniProt/ChEBI reaction mapping
files: https://reactome.org/download-data . Rather than reimplementing
existing normative pathway exports, **obtain and validate those existing
source releases**, preserve taxon/compartment and compare any proposed
Kitzerow causal edge as a separate typed claim.

## Ownership and present scope

**Creator proposal:** Kimberly Kitzerow, *Autism & the Comorbidities Along the BH4 Pathway* (January 2024), DOI 10.13140/RG.2.2.23124.37761/1; *The BH4 Pathway as an Allostatic Mechanism in the Pathology of Autism and Systemic Comorbidities* (August 2024), ResearchGate publication 383021907; *Neurodivergent Biochemistry and the Autism and the Comorbidities Theory* (July 2025), DOI 10.13140/RG.2.2.30248.89606.

**Background chemistry:** UniProtKB (https://www.uniprot.org), Rhea (https://www.rhea-db.org/help/links), ChEBI (https://www.ebi.ac.uk/chebi) and older primary biology own the underlying knowledge. Credit Kitzerow for her documented selection, proposed ordering and proposed causal BH4/allostatic synthesis, not already-known NOS, AAAH, AGMO, redox, mTOR or E/I component facts.

**DASHI work:** finite extraction, xPollenation, candidate-causal reconstruction, evidence/payment rules and algorithmic interop belong to their independently attributed repository implementations. A candidate transcription cannot become a verified original quotation. Priority/contact/citation/derivation/misconduct remain five independent genealogy coordinates.

The current 16-UniProt/24-protein–Rhea-link panel yields 12 finite Rhea reactions, 29 indexed Rhea/ChEBI source species, three non-finite MTOR residuals and a 56-coordinate open-state manifest (15 state/context + 12 reaction flux + 29 exchange). This is not Kitzerow's entire proposed pathway, not a compartment-resolved model and not disease-causation evidence. The flux solver remains underdetermined.

## Structural identifiability limit (exact non-promoting theorem)

The existing open-system owner gives S*v+e=0, separating internal
reactions from environmental exchange. The new source-written Agda
module `BH4ExchangeIdentifiabilityExact` proves a general additive
cancellation theorem: for any prescribed internal signed total s=S*v,
an **unrestricted** external e=-s exists and balances it exactly.
The concrete helper `bh4_exchange_identifiability.py` checks this
identity with exact integer matrices/vectors, not approximate kinetics,
and the regression exhibits caller-assumed exchange intervals that can
exclude that particular candidate.

**This identifies the test's discriminating max-cut**: an apparent
steady-state feasible point with arbitrary freely chosen exchanges
does not support Kitzerow's simultaneous-demand mechanism.
Pay specific transport/source/sink bounds for each relevant species
with coherent compartment, tissue, state, and time; then use the
existing HiGHS feasibility solver and a separate reviewed hypothesis
test. There are no manufactured observational exchange values.

The new abstract theorem and exact-integer fixture are source-written
and **not** current-head Agda-kernel/pytest verified.

    python3 scripts/check_bh4_exchange_identifiability.py
    scripts/run_agda29_parallel_check.sh DASHI/Biology/BH4ExchangeIdentifiabilityExact.agda

## Original chart -> curated biochemical resource (implemented acquisition path)

An explicit, optional source-first mode now **reuses the existing Rhea
REST/SPARQL acquisition and signed stoichiometric matrix builder**:

    python3 scripts/acquire_rhea_chebi_bh4_reactions.py \
      --from-source-chart docs/biology/KitzerowPublishedRheaChartObservedIndex.v1.json \
      -o artifacts/biology/kitzerow-creator-chart-rhea-reactions.json

    python3 scripts/build_bh4_stoichiometric_matrix.py \
      artifacts/biology/kitzerow-creator-chart-rhea-reactions.json \
      --output-prefix artifacts/biology/kitzerow-creator-chart-stoichiometric-matrix

    python3 scripts/build_bh4_pathway_ontology.py \
      --matrix artifacts/biology/kitzerow-creator-chart-stoichiometric-matrix.json \
      --rhea artifacts/biology/kitzerow-creator-chart-rhea-reactions.json \
      -o artifacts/biology/kitzerow-creator-chart-ontology.json \
      --jsonld-output artifacts/biology/kitzerow-creator-chart-ontology.jsonld

Alternatively opt in through the canonical Phase-4 runner:

    python3 scripts/run_bh4_phase4_maxcut.py \
      --acquire-creator-chart-reactions

The outputs are distinct from the 16-protein-selected DASHI 29×12 matrix.
No net transport equations, kinetic assignments, same-state pool merges or
author-causal predictions are produced by the source-chart matrix.
The acquisition stores explicit errors and source REST/SPARQL SHA receipts,
and **does not claim a verified Rhea release number** when using live
endpoints without a release-manifest receipt. Source identity, actor,
creator-chart source index digest, acquisition date and missing original
PDF verification are retained.

The corresponding native source consumer in SensibLaw #512 can now
take an optional creator-selected Rhea acquisition receipt and present
the independently curated ChEBI participant candidates within the
existing provider-neutral external graph view. Its mappings are
review-required; a same-compartment or in-vivo relation is still unproved.
None of these source-written changes has been locally executed or
referee-checked on the current PR heads.

## Canonical reuse — no parallel biological ontology

- KitzerowBH4SourceRegistry, KitzerowPriorityGenealogyExact, KitzerowBH4EvidenceAtlasExact: author/source chronology, attribution, bounded research.
- KitzerowBH4SystemNongNangMaxCutExact: proposed mechanisms and per-edge payment.
- UniProtBH4PanelCertificateExact, BH4PanelStoichiometricMatrixExact: protein identity, reaction participants and signed coefficients.
- BH4SystemStateExact, BH4OpenMetabolicNetworkAdapterExact, BH4JointFluxFeasibilityExact: shared pool and open-system law d(x)/dt = S*v + e.
- BH4JointPaymentAcquisitionExact: source and same-context rate/exchange admission.
- DASHI.Core.XPollenationExact + #1227 and ITIR #22: typed external identities, transport-only artifact receipts.
- BH4PathwayOntologyInteropExact and build_bh4_pathway_ontology.py: structural projection, not a new physiology solver.
- BH4PathwayReviewInteropExact and build_bh4_pathway_review.py: readonly source-reopenable obligations, reusing existing PNF/Wikidata repair and ReadingTrail owners; not SLR native persistence.
- BH4CreatorChartSourceBridgeExact and compare_kitzerow_primary_chart.py: creator-first source index and finite-panel exact-ID crosswalk. Native SensibLaw external graph bridge PR #512 consumes the same source observations through its existing generic world model and linkage adapters.
- Canonical imports: DASHI/Biology/Everything.agda and DASHI/Everything.agda now import KitzerowBH4EvidenceEverything; the symmetry-only TOE root is intentionally untouched.

## Executable first tranche in this stacked PR

1. Validate Rhea, ChEBI, the existing finite matrix and optional xPollenation. Reject contradictory reaction participants, a zero reaction or false promotion.
2. Preserve signed substrate/product coefficients, source revision and acquisition receipt. Rhea master-reaction orientation is not in-vivo physiological direction.
3. Export one deterministic JSON pathway manifest and one RDF-importable JSON-LD discovery graph using identifiers.org for exact Rhea, ChEBI and UniProt coordinates. When present in the newly acquired Rhea REST row, retain GO and Reactome cross-references as separately sourced, non-promoting edges. Unresolved Rhea compounds and all other namespaces remain literal source identifiers until their resolvers are independently acquired. No owl:sameAs is manufactured.
4. Keep author-level *hypothesis* edges in the independent KitzerowBH4ClaimLedgerCandidate.v1.json. Two initially transcribed edges are repo reconstructions of existing BH4 owner claims; original paper page/figure pins remain unverified.
5. Keep 12 reaction-flux and 29 external-exchange coordinates null/unresolved. No SBML, BioPAX or GO-CAM conformance, simulator kinetics or clinical finding is claimed.
6. Acquire Rhea GO and Reactome crosslinks (with source REST hashes); recognize well-formed curated KEGG/MetaCyc reaction IDs as typed *review-only* crosslinks, while retaining malformed or ambiguous field values as unparsed review material. GO and Reactome crosslinks remain non-promoting; no same-context event is presumed.
7. Project author-source gaps, ontology-mapping semantics, compartment/kinetic/rate and nonfinite chemistry into a deterministic read-only worklist. Never infer missing evidence is false. Source-envelope visibility blocks exporting restricted locators.

Command using already-produced receipts:

    python3 scripts/build_bh4_pathway_ontology.py \
      --matrix artifacts/biology/bh4-stoichiometric-matrix.json \
      --rhea artifacts/biology/rhea-kitzerow-bh4-reactions.json \
      --xpollenation artifacts/biology/bh4-xpollenation.json \
      --claims docs/biology/KitzerowBH4ClaimLedgerCandidate.v1.json \
      -o artifacts/biology/bh4-pathway-ontology.json \
      --jsonld-output artifacts/biology/bh4-pathway-ontology.jsonld

The Phase-4 runner invokes the exporter from receipts produced in that run, with Rhea/matrix-only fallback when no new xPollenation receipt is emitted.

## User-story review worklist

    python3 scripts/build_bh4_pathway_review.py \
      --pathway artifacts/biology/bh4-pathway-ontology.json \
      -o artifacts/biology/bh4-pathway-review-worklist.json

When an authorized, typed external source packet is already present, pass
--source-receipts PACKET. The packet must contain explicit visibility and
source/revision/locator/digest coordinates; strings are not an independent
source-authentication certificate. Public locators can be presented for
source opening, while internal/restricted locators remain opaque.

See [BH4ITIRSensibLawWikiRepairCrosswalk.md](BH4ITIRSensibLawWikiRepairCrosswalk.md)
for the exact ITIR-US-17 / WIKI-US-01..04 / SLR S29 / Dioxus user-story
handoff, which reuses current Agda Wikidata repair/reopening types and
avoids legacy SensibLaw Python and ITIR Svelte as production owners.

## Exact outstanding max-cut obligations

| ID | Required proof, evidence or implementation | Source/owner and firewall |
|---|---|---|
| KPO-01 | **Source-first correction:** original Kitzerow Jan-2024 Rhea-coded BH4/folate chart found, eight identifiers indexed with web-text coordinates; acquire the original PDF bytes, source revision and all source-observed reactions and pin exact source passages, figures/pages and proposal edges. Transcribe without republishing protected diagram. Original proprietary network coverage remains unknown. | Kitzerow primary works. No backdating from later texts. |
| KPO-02 | Creator chart Rhea-ID subset is indexed and a separate source-selected REST/SPARQL-to-matrix/ontology pipeline has been implemented. Execute and verify it; complete original diagram transcription and adjudicate structural reaction family/compartment alignment with the independent 16-protein panel, reporting unknown coverage and prior-art subtraction. | Distinct source/claim and chemistry ownership. |
| KPO-03 | Rhea REST requests GO, Reactome, KEGG and MetaCyc columns; well-formed KEGG/MetaCyc IDs become source-attributed review candidates, malformed values remain unparsed residuals. Reactome crosslinks are automatically ChEBI-derived, unlike curated KEGG/MetaCyc links. **Still required:** version-pinned acquisition, GO evidence/taxon/context adjudication, EC and other pathway families, and independent typed relation review. | Rhea/UniProt/GO/Reactome/KEGG/MetaCyc, with no same-biological-event or flux promotion. |
| KPO-04 | Adjudicate GO/ECO evidence codes, GO-CAM causal assertions, GO cellular components, Cell Ontology/UBERON tissue and sample/taxon scope. | Source-specific GO evidence, not generic ontology matching. |
| KPO-05 | Acquire explicit transport/uptake/export/oxidation reactions and appropriate source/sink boundaries for the 29 exchange *coordinates*. | A coordinate is not proof a transport reaction occurs. |
| KPO-06 | Pin NOS1/NOS2/NOS3 isoform, exact tissue, sample, time, compartment, BH4/BH2/redox, substrate, volume and protein abundance. | Cross-tissue abundance does not create one physical state. |
| KPO-07 | Derive justified assay-specific magnitude and unit bridges (Vmax, kcat*[E], mass/volume) for all 12 reaction-flux intervals, including PCBD1/NOS literature gaps. | Km/Kd/Ki alone do not set flux; protein intensity != enzyme molarity. |
| KPO-08 | Acquire transport/turnover/time evidence for required exchanges; supply matched AAAH/NOS/AGMO demands, then rerun source-paid S*v+e=0 and dynamics. | Unknown != zero. Feasibility != unique causal allocator. |
| KPO-09 | Prefer existing Reactome BioPAX Level 3 exports and curator-provided GO-CAM/GO evidence where available; acquire versioned artifacts and validate their sources, taxon, revision and mapping relation before attaching a creator proposal. | RDF/JSON-LD discovery graph alone is not native BioPAX/GO-CAM. |
| KPO-10 | Prefer existing Reactome SBML Level 3 release exports and round-trip/validate against the source-owned reaction subset; only synthesize missing compartment-specific creator extensions after source payment. Preserve rate-of-extent units amount/time. | Never fabricate a shared cytosol or a kinetic law. |
| KPO-11 | Compare identified alternative redox, NO, immune and non-BH4 mechanisms with matched observables, identifiability and negative controls. | Local mechanism support != whole Kitzerow hypothesis. |
| KPO-12 | Reconcile #1159 -> #1226 -> ontology PR with current master; independently reconcile #1227 and ITIR #22. Pin first-implementation commits and exact-head Agda/Python receipts. | Mergeability != type-check or scientific validity. |
| KPO-13 | Admit genuine primary source bytes/revisions/spans, with source scope and no caller-hash authentication shortcut. | SLR INGEST-1; ITIR-US-17; Kitzerow attribution. |
| KPO-14 | Bind existing candidate worklist through *native* SLR S29/PG source/review in a consumer-scoped transaction and demonstrate reopenability. | SLR #76 family; not a new parallel review database. |
| KPO-15 | Implement an opt-in selected BH4 object Dioxus inspector: Orient -> Project -> Why? -> Source -> Meaning -> Follow -> Next unresolved. | Dioxus M10; Svelte is historic only; preserve restricted sources. |
| KPO-16 | Consume PNF/SSSOM/OCTF/Wikidata repair only with typed inference language, source and context; never auto-edit or conflate GO/Reactome/Rhea/QID. | DASHI #1143, #1447; original JMD/Peter/Ege/Rosario attribution. |
| KPO-17 | Obtain real 12 reaction and 29 exchange source-paid intervals, same-object tissue/time/volume and BH4 demands; rerun existing solver. | Primary kinetics and transporter studies; unknown != 0. |
| KPO-18 | Verify/reconcile stacked #1159/#1226/#1454, peers #1227/ITIR #22/#70/SLR #76 and formal roots with exact-head runs and first-implementation receipts. | Git state + independent referee, not assertion of mergeability. |

KPO-03 through KPO-06 make it easier to find transport candidates and matching physiological states. They can expose assumptions and guide experiments. They cannot independently pay the numerical measurements demanded by KPO-07/08.

## External primary standard/reference roots

- Rhea REST and linked resources: https://www.rhea-db.org/help/rest-api and https://www.rhea-db.org/help/links
- Reactome Content Service: https://reactome.org/dev/content-service
- Gene Ontology / GO-CAM and evidence codes: https://geneontology.org/docs/go-annotations/ and https://geneontology.org/docs/guide-go-evidence-codes/
- BioPAX Level 3: https://www.biopax.org/
- SBML Level 3: https://sbml.org/specifications/sbml-level-3/
- Systems Biology Ontology: https://www.ebi.ac.uk/sbo/
- Cell Ontology: https://cellontology.org/
- UBERON: http://uberon.github.io/

Version/assay/source release still must be pinned in acquired receipts. No standards DOI has been invented.

## Validation (not yet observed on this new head)

    python3 scripts/check_bh4_pathway_ontology.py
    python3 scripts/check_bh4_pathway_review.py
    python3 scripts/check_kitzerow_primary_chart.py
    python3 scripts/check_kitzerow_chart_source_text.py
    python3 scripts/check_kitzerow_source_chart_acquisition.py
    python3 scripts/check_bh4_numeric_flux_guard.py
    python3 scripts/check_bh4_exchange_identifiability.py
    scripts/run_agda29_parallel_check.sh DASHI/Biology/BH4CreatorChartSourceBridgeExact.agda
    python3 scripts/check_kitzerow_bh4_priority_all.py
    scripts/run_agda29_parallel_check.sh DASHI/Biology/BH4PathwayOntologyInteropExact.agda
    scripts/run_agda29_parallel_check.sh DASHI/Biology/KitzerowBH4EvidenceEverything.agda
    scripts/run_agda29_parallel_check.sh DASHI/Biology/Everything.agda
    scripts/run_agda29_parallel_check.sh DASHI/Everything.agda

No exact-head Agda type-check, remote ontology verification or SBML parser receipt is asserted by this PR.


## 2026-11-09 — current spatial biology completion ledger (cross-PR)

The earlier KPO-01–KPO-18 ontology and source obligations **remain**; the current mathematical priority is the shared physical-state slice, not another parallel ontology. Detailed synchronized table: `docs/biology/BH4PhysicalTissueFutureObservationMaxCut.md` on this branch and `Docs/support/reference/BH4PhysicalTissueFutureObservationMaxCut.md` on developmental PR #1471.

**New confirmed source owner:** `scripts/check_bh4_original_panel_spatial_events.py` consumes the existing acquired original 16-protein Rhea/ChEBI 29-species/12-finite-reaction certificate; it does *not* write a substitute 29×12 matrix. Three nonfinite source residuals are retained. The strict certificate-backed run is gated on the original artifact; a five-species QDPR fixture is a separate finite self-test. Permissible geometric events do not justify physiological transport or kinetics.

**Exact proposed unpaid declarations, in dependency order:** `original369LocalSignedContinuityExact`, `original29x12SpatialReactionBalance`, `sameSourcePhysicalReactionTransportStep`, `physicalBH4StepCommutes`, `physicalPNPStepCommutesOriginal`, `physicalTissueOneStepRefinement`, `physicalKernelLumpsUnderInterventions`, `physicalFutureQuotientIsMinimal`, `sourceCalibratedParametersAdmissible`, `heldoutFuturePredictionsDiscriminate`.

**Release gates D0–D6:** exact Agda receipts and branch reconciliation; genuine original reaction/exchange source payment; admissible chemical/PNP update; physical-to-tissue commuting proof; minimal intervention-safe stochastic quotient; independent longitudinal calibration/discrimination; attributed ITIR/PNF review. Do not promote biochemical source attribution into Kitzerow clinical causal validation.


### 2026-11-09 same-inventory original-panel chronology update

Source-consuming `check_bh4_original_panel_spatial_events.py` now checks a reaction→original native-bond transfer→return history for every source-acquired finite reaction column. The full strict test requires `artifacts/biology/rhea-kitzerow-bh4-reactions.json`; absent artifacts must remain OPEN. This makes no synthetic claim of 29 measured environmental exchange fluxes. QDPR selected one-column self-test is a separate chemistry fixture.

Companion #1471 now has pointwise Agda local-debit/credit and original exterior-face-injection owner lemmas, but all-voxel original signed-current continuity and exact-head kernel receipts are unpaid. **Full remaining theorem sequence** remains `original369LocalSignedContinuityExact` → `original29x12SpatialReactionBalance` → `sameSourcePhysicalReactionTransportStep` → same-source BH4/PNP/tissue step commutation → intervention-safe future quotient/minimality → source-calibrated held-out predictions. Preserve all KPO-01–18 original source obligations, attribution and no-auto-promotion ITIR boundaries.


### 2026-11-09 P0 geometry/flux and evidence status

Companion developmental branch #1471 now has actual native-bond off-endpoint local invariance, certified exterior-face event off-site locality and stricter voxelwise signed-current regression guards. The local current law `original369LocalSignedContinuityExact` **is still open** for Agda histories, as is the source-certificated `original29x12SpatialReactionBalance` (not a zero-filled synthetic replacement). The physical reaction/transport step, BH4–PNP–tissue commutation, intervention-safe minimality and held-out measurements remain downstream open gates. Preserve KPO-01–18 and all Kitzerow-original-chemistry attribution boundaries.


### 2026-11-09 strict Rhea source artifact and native-history audit

The connected GitHub PR #1454 branch did not contain the tracked path `artifacts/biology/rhea-kitzerow-bh4-reactions.json` (404). This is a **tracked-branch reproducibility gate**, not a claim that the earlier acquired material never existed. The existing `BH4ExecutedPanelReactionReceiptExact` records 12 finite IDs, three nonfinite residuals and 29 species, but this typed receipt alone does not execute the original matrix or supply measured fluxes. Keep the strict 29×12 validator fail-closed on absent source bytes.

Companion #1471 now source-writes true forward/reverse native-bond action histories, global conservation for those histories, and off-endpoint spectator invariance. Signed local current/face history induction remains unproved; original chemical rates, source-specific exchanges, clinical hypotheses and independent longitudinal predictions remain open. Retain KPO-01–18 and original-source attribution.


### 2026-11-09 physical P0 transport-current dependency update

Original geometric/cubical companion PR #1471 has now source-written exact executed source/target transfer quantum lemmas, geometric non-loop proofs, per-role native voxel incidence conservation, one-step **integer signed** cation/anion continuity, and original face discharge local balance. No Agda typecheck or branch integration is claimed. This strengthens the local-current mathematical dependencies but leaves arbitrary mixed-current history induction unpaid. Rhea 29×12 original source bytes, 29 exchange flux measurements, physiological model calibration, same-source BH4/PNP/tissue refinement, original stochastic quotient, held-out validation and stacked Golden reconciliation remain OPEN. Existing KPO-01–KPO-18 source/attribution obligations are unchanged.


## 2026-11-09 source-written signed mixed-history 369 theorem owner

Companion biology PR #1471 now has a source-written original 27-voxel/54-bond/6-face ionic history theorem candidate `original369LocalSignedContinuityExact` in new `Biological369MixedNativeFaceSignedContinuityExact.agda`, imported into its Round-23 Golden and acceptance script. It consumes original geometric incident edges and actual face-selected exchange currents, derives signed charge from separate cation/anion ledgers and proves chronological balance by natural-number induction in source. No exact-head Agda checker has run: mark as **kernel pending**.

The high-value P0 source obligation is still to recover/execute the original byte-pinned 29×12 Rhea certificate, carry its 3 nonfinite residuals and all 29 separately measured exchange rates into a physical 3D model; then construct `sameSourcePhysicalReactionTransportStep`. P1–P3 phenotype, stochastic quotient, empirical evidence and the stacked root remain OPEN. Do not confuse source-written transport conservation with measured permeability or a proved clinical Kitzerow allocation mechanism.


## 2026-11-21 atomic geometry / KK / proteomics extension (MG01–MG09)

User-directed explanatory order: native atomic geometry, quantum state and proper-frame symmetry first; molecular observables second. Reuse merged #901 same-sequence 4AKE/1AKE separating pair, #1159 original BH4 panel (16 proteins, 38 PDB structures, 526 SIFTS mappings, 932 kinetic parameter objects), #1471 native spatial transport, and #1241/#1460 conditional KK/observer donors. These are donor references, not verified cross-branch imports. Preserve KPO and D0–D6 gates.

- MG01 OPEN: recover original atomic carrier and its precise geometric-to-electronic observable map; separate representation from physical derivation.
- MG02 OPEN: byte-pinned nonpathogenic 4AKE/1AKE coordinate replay with explicit units, missing atoms and frame provenance.
- MG03 OPEN: proper-frame invariant distances, signed tetrahedral chirality and orientation; reflection negative control; no identification of a spatial coordinate with the KK fibre.
- MG04 OPEN: same-inventory/different-conformation separating pair and observer-specific geometric residual; certify reconstruction cost against unreduced coordinates.
- MG05 OPEN: distinguish chemical bond, interaction and functional observation graphs; demonstrate nonfactorability using original adenylate kinase pair.
- MG06 OPEN: conditional KK metric/connection reduction to the same physical quantum Hamiltonian, then independently justified electronic-to-molecular energy surface. Retain #1241/#1460 physical metric, coupling, radion and same-H gates; no atomic spectra inferred merely from 369 counts.
- MG07 OPEN: proteomics observation operators for peptide identity/abundance, intact proteoforms, and structural observations; peptide-to-protein ambiguity and missingness negative controls. Reuse BH4 SIFTS identity and assay-context gates; no claim of existing LC-MS acceptance.
- MG08 OPEN: same-object BH4 abundance/compartment/time context to existing original reaction and PNP carriers; no invented fluxes.
- MG09 OPEN: held-out nonpathogenic structure/measurement comparison, compression and reconstruction bounds and exact-head safe Agda local acceptance.

The November 2026 adaptive-impermeability report motivates the abstract distinction of structural versus functional observations; antibiotic mechanisms are literature examples, not a pathogen-specific predictive or optimization workstream. First implementation tranche: general proper-frame/chirality and observation nonfactorability fixtures on nonpathogenic or synthetic geometry. No resistance engineering, atomistic pathogen simulation, physical KK closure, or clinical promotion. All MG gates remain OPEN until source and local execution receipts are recorded.


### 2026-11-21 MG01/MG03/MG06 finite geometry continuation

Recovered actual master source AtomicPeriodicTable369GenerativeExact (also verified present on this branch, blob 5817bc6965f80013d6e4b1e54271e8ce55a14e74). It owns nine-sheet reconstruction and the abstract AtomicGenerator stages realize, oneParticle, antisymmetrize, interactingEnergy, selectGround, shellOf, valenceOf, observeChemistry. The physical realization and interacting Hamiltonian remain abstract. Original HydrogenReducedMassExact records 13.598287264283275 eV versus NIST 13.598434599702 eV; original MadelungPhysicalSourceSnowballExact explicitly retains model dependence and exceptions. These are existing receipts, not reruns.

Read actual KK sibling #1241 head 219f7962b36f30342bb27935cfeaa2ecd82dd97d: TOEKKCircleSpectrumConsumerBIDIExact already owns cardinality/operator and finite Fourier/continuum mass non-descent; KKCircleQEDChiralityConsumerExact owns QED charge/mass versus weak chirality non-descent. The former file is absent on the BH4 branch (404); no typed sibling import claimed.

Committed scripts/check_atomic369_geometry_kk_reference.py at 99ec8aa5eda1aa06a4a82b2cf1cca6465984bcb7. Identical source executed locally with SymPy: 27-site native path cube has 54 edges and exact Laplacian trace 108; C27 has 27 edges and trace 54; both annihilate constants. All 48 signed permutation frames preserve Gram and transform oriented volume by determinant; 729 exact rational sampled-phase alias cases for k=-13..13 and j=0..26 pass, with differing continuum squared modes. Finite reference only, not Agda acceptance nor physical atomic/KK realization. MG01 source recovery paid, physical realization OPEN; MG03 finite fixture paid, empirical and kernel gates OPEN; MG06 finite negative controls paid, selected same-action/same-H bridge OPEN. Next: recover original atomic hydrogen/helium producers and selected KK same-action electron source; establish provenance-pinned operator comparison, with mass, charge, spin, units, boundary conditions, domain and independent spectral residuals. Keep all original MG02/MG04/MG05/MG07–09 and KPO/D gates unchanged.


### 2026-11-21 MG06 same-operator finite reference (continuation)

**New committed reference**: `scripts/check_atomic369_kk_operator_weld.py`, commit `7286b8ef97fa17b907337e898a90c7d89cdb5ff8`. Independent equivalent local SymPy execution: 512/512 Z2 subset of U(1) lattice gauge frame transformations (unitary-conjugacy identity), one +1/-1 Wilson holonomy spectral separation on the same 9-site cycle, 4/4 exact 8-point radial kinetic + centrifugal + Coulomb decompositions for Z=1,2 and ell=0,1, reduced-mass-versus-unit-mass separating witness, and original reduced-mass hydrogen constant regression. The source file was committed via GitHub; **do not claim exact checked-out commit script execution or Agda kernel acceptance** without a new receipt.

**Primary donor audit**: `scripts/atomic_hydrogen_reduced_mass_nist.py` (master blob 67b1df8e...) is an analytic nonrelativistic Coulomb/reduced-mass model with CODATA conversion and NIST comparator; `scripts/atomic_helium_hartree_scf.py` (master blob 289eae45...) uses the spherical radial finite-difference Hamiltonian, self-consistent one-electron Hartree potential, and E_He=2 epsilon-J. They are distinct operators and the latter includes a mean-field approximation, not a physical KK derivation. `AtomicPeriodicTable369GenerativeExact` (branch blob 5817bc69...) keeps `AtomicGenerator` physical realization and interacting-energy fields abstract. `KKQEDQCDHyperchargeBIDIExact` (KK #1241 blob 1c635128...) checks Q=T3+Y normalization and explicitly does **not** derive 5D SM fields.

**Next actual source-payment cut**: selected 5D action with fixed radius/field normalization -> horizontal connection and charge identification, kinetic operator including units and continuum limit -> same source electron mass/spin/fermion statistics -> Coulomb field and boundary -> hydrogen reduced mass and externally calibrated spectral residual -> independently sourced two-electron Hartree interaction and correlation budget. Explicitly compare same action, same Hilbert space/domain, state/clock, nuclear source, units, and selected Hamiltonian. A Z2 signed-link subcase is not full U(1), and graph gauge conjugacy does not establish physical 5D KK-to-electron or continuum Coulomb identification. MG06 finite mathematical subgate PARTIAL; physical same-H and GOLDEN remain OPEN. Do not promote these results to medicine, pathogen mechanism, or experimental proteomics.


### 2026-11-21 MG06 U(1)-subgroup / Dirichlet operator cut

**Committed** `scripts/check_atomic369_kk_u1_dirichlet_weld.py` in commit `489b09d6804c95cadc83178271b2f52c4b094c6f`. The equivalent local SymPy implementation executed with exact rational/Gaussian-integer arithmetic and passed 512/512 gauge-frame transformations for the fourth-root complex phase subgroup {1,i,-1,-i} across two four-site cycle connections and 8/8 incidence+centrifugal+Coulomb radial matrix equalities (Z=1,2; ell=0,1; mu=1 and illustrative 1836/1837). Negative controls: changing Wilson-loop holonomy changes characteristic polynomial and determinant; dropping one Dirichlet boundary edge changes the matrix; Coulomb term cannot be discarded; an independently supplied Hartree field changes helium's operator; nonzero phase changes matrix representation although gauge equivalent on a contractible interval. The local executed source and committed script encode the same experiment; **the committed GitHub checkout script itself was not executed** and no Agda receipt exists.

The exact radial identity is H = B^dagger B/(2 mu dr^2) + diag(ell(ell+1)/(2 mu r_i^2) - Z/r_i), with *both* hard-Dirichlet boundary edges included, matching the source `atomic_helium_hartree_scf.py` finite difference at mu=1 before its separately provided self-consistent potential. The exterior Coulomb source, empirical mu, spin, many-electron antisymmetry, 369 carrier map, 5D KK action and continuum limit remain unpaid. Do NOT identify a finite fourth-root U(1) subgroup with full compact U(1), a gauge-equivalent representation with an experimentally validated model, or the algebraic operator identity with a physical KK derivation. MG06 mathematical finite-operator subgate PARTIAL, MG06 same-selected physical-H OPEN, MG07 proteomics OPEN, original KPO/D and Golden pending. Next exact cut: derive or source-select the connection's coupling, dimensionful coordinate/R/units and electron one-particle Hilbert/domain from a physically fixed KK reduction, then produce explicit same-source operator commuting square against original radial hydrogen/helium with phase/gauge controls and independent spectral error budget.


### 2026-11-21 MG06 conditional selected-mode commuting square

Added `scripts/check_atomic369_kk_selected_mode_commuting.py` (commit `1ddf40b659b1d51101eeb738f7f1f67014afab2b`). Local equivalent script passed 16/16 exact SymPy product-operator instances on a 4-point radial Dirichlet matrix tensor the 3-site compact circle. Parameters: Z=1,2; ell=0,1; mu=1 or illustrative 1836/1837; radius=1,2. `H_product = H_rad ⊗ I + I ⊗ L_C3/R^2`; isometric `W=I⊗(1,1,1)/sqrt(3)` satisfies H_product W = W H_rad, W†W=I, W†H_product W=H_rad. A nonconstant circle eigenvector (eigenvalue 3) retains the `3/R²` spectral residual, proving that zero-mode projection loses nonzero fibre excitation data. Negative controls: wrong Coulomb Z, wrong reduced mass, omitted Dirichlet boundary diagonal, incorrect assumption that higher KK modes have the zero-mode Hamiltonian, holonomy change versus pure-gauge phase transform. The actual committed script was written using the source of the locally executed equivalent test; no exact-checkout CI or Agda kernel receipt has been claimed.

**Critical non-promotion:** the tensor product `H_product` explicitly CONTAINS the original Coulomb atomic `H_rad` as an input. Its exact commuting square proves mathematically consistent restriction, not deduction of electron mass/charge/spin, Coulomb potential or the selected 5D Einstein–matter action. No physical KK-to-atom derivation, no 369 physical realization, and no helium interacting operator from first principles yet. MG06 finite same-operator *conditional model* PARTIAL; MG06 physical independent derivation and selected same-H still OPEN. Next: identify actual selected 5D action/physical source and build a non-circular reduction yielding independently prescribed electromagnetic field, coupling, electron representation and atomic operator before comparing to source H_rad; retain provenance and spectral error budget.


### 2026-11-21 MG06 non-circular selected KK electron-source audit

Source read directly from sibling PR #1241: `scripts/check_kk_light_qed_dirac_same_action.py` blob `948768cf9dfb3ca2fc2c83b713da8c24d68e11f4`; `Docs/physics/KKLightElectronBIDIChiralityRadionMaxCut20261024.md` blob `38098c42b0f313bdfbb58bb77e84182dd65076ae`. This specific smooth S1 model has independent 5D Maxwell `B_A` distinct from metric graviphoton, and a periodic 5D Dirac zero mode. Its `m_e=0.00051099895 GeV` and `e5=e4 sqrt(2 pi R)` are empirically selected INPUTS; this source neither predicts mass/charge nor constructs a proton/nuclear source, electroweak chirality, bound-state Coulomb Hamiltonian, or derived 369 atomic realization. Its radion/Casimir result is contingent on a separately selected matter spectrum and counterterm, not a universal physical KK solution.

New reference `scripts/check_atomic369_kk_maxwell_coulomb_source_gate.py` committed, corrected head `28860e0fd7182eb16b9a26b7e22928920a24ea7f`. A separate local exact symbolic check verified the zero-mode normalisation `L (1/sqrt(L))²=1`, the effective coupling `e4=e5/sqrt(L)`, zero-mode mass retention `sqrt(m5²)=m5`, the nonzero excited-mode mass difference, and the external-source conditional potential `V=-Z e4²/(4 pi r)` (reducing to `-Z/r` only in units fixing e4²=4pi). Missing nuclear source `Z=0` gives V=0; electric coupling requires independently supplied field normalisation. The *committed* exact script has not been rerun from a checked-out GitHub tree; no kernel acceptance is claimed.

**Priority and no-circularity constraint:** the cited model's physical photon is the independent Maxwell zero mode, **not derived from the gravitational KK graviphoton**. The independent Maxwell action can yield an ordinary Coulomb field only upon supplying a charged nucleus, electrostatic boundary conditions and a controlled nonrelativistic limit; this is conditional field theory, not an origin-of-charge theorem. Establish a single selected physical source with 5D action, coupling and matter state; prove dimensional reduction, electron charge/mass/representation, external nuclear source and Coulomb potential, physical 369 embedding, matching domains/Hilbert spaces, then compare original atomic Hamiltonian spectra without inserting target H in the producer. At present MG06 conditional source/normalisation PARTIAL; physical same-H, pure metric graviphoton identification, electroweak/SM and Golden OPEN.


### 2026-11-21 MG06 observer- and dimension-indexed geometric error audit

User correction: the correct question is not simply 'which parameters remain input?' but **relative to which dimension, observer, consumer and physical realization does an input appear missing?** Original owner `DASHI/Core/ConsumerDescentMinimalObserverExact.agda` (master blob `d0961074290dd887af3c96add0957a0fa14140be`) formalizes consumer-specific fibre constancy / descent, and original KK `TOEKKCircleSpectrumConsumerBIDIExact.agda` (#1241 blob `193f3e2a260968db83ca98837679629bc472d847`) proves finite mode and graph-cardinality non-descent. Reuse these authorities; do not relabel them as newly derived.

**Executed finite source fixture**: `scripts/check_mg06_observer_dimension_geometry.py` (commit `d310466f6c53583b5c29a65c44719b2df96f74e3`). Exact local SymPy calculation: 189/189 sampled 27-phase alias/reconstruction cases with explicit integer quotient/residue; C27 trace 54 vs native P3^3 trace 108; d=2,3,4 Gauss radial conservation `d/dr(r^(d-1) E_d)=0`; resulting potential dependence log(r), -1/r, -1/(2r²) up to sign and source convention. An arbitrary source amplitude remains a separate coordinate. The executed local source is equivalent to the committed script; exact GitHub checkout execution and Agda kernel remain unverified.

**Failure taxonomy, each independently adjudicated:**
1. Wrong spatial dimension, spatial/fibre conflation, topology or operator -> geometric mismatch.
2. Observer discarded relevant spectral mode, winding, chirality, source or boundary data -> insufficient observation; retain a consumer-minimal residual, rather than assert intrinsic indeterminacy.
3. Bad frame, gauge, units, orientation or normalisation -> representational mismatch, correct under appropriate covariance/isometry.
4. Missing source dynamics, action, electron representation, nuclear charge or calibration -> physical-model/source gate, not automatically reducible to geometry by assertion.
5. Numerical discretisation, regularisation, approximation or measurement noise -> independent numerical/empirical error budget.

Test the research hypothesis 'apparent errors predominantly come from wrong geometry' by a preregistered residual decomposition across independent consumers and held-out measurements. **Do not assume all physical error vanishes under geometric refinement**; residuals can reflect omitted physics, approximations or genuine data limitations. For selected #1241 KK electron, the independent Maxwell field, chosen coupling, supplied bare mass and absent physical nuclear source remain explicit; proving an observer lift or changing dimension does not by itself derive them.

**Next highest-alpha physical work**: construct observer-indexed commuting square with `O_(d,c)`, physically selected state `X`, projected operator `H_(d,c)` and reconstruction residual `R_(d,c)`, prove precise sufficient-consumer conditions and concrete separating pairs using the original owners; then test same-selected 5D action to 4D electron/nuclear source without inserting the target Coulomb operator. MG06 dimensional/observer finite checks PASS, same-source physical realization OPEN, MG07 proteomics and Golden OPEN.


### 2026-11-21 MG06 observer-indexed Schur/Feshbach exact reduction

New source `scripts/check_mg06_observer_schur_residual.py` committed at `ac5f6789763cb74db6e79b362c5c92a6bebe22c5`. The same source was run locally with SymPy after correcting a test-only resolvent sampling point that landed on a hidden-sector pole. **48/48 exact rational model cases PASS**, plus explicit decoupled case, same visible A and D with different interaction B (distinct full characteristic polynomials), nonconstant energy self-energy, and hidden-orthogonal-frame invariance. The independently executed source is the one committed; GitHub remote execution/Agda kernel are not claimed.

Let H=[[A,B],[B†,D]] and let P select the visible block. Away from poles, `P(zI-H)^{-1}P† = (zI-A-B(zI-D)^{-1}B†)^{-1}`. The exact consumer-specific residual is the Schur/Feshbach self-energy `Sigma(z)=B(zI-D)^{-1}B†`. It is unnecessary for a fully decoupled sector B=0; for B≠0, simply keeping PHP=A generally fails. This is a mathematically meaningful geometry/observer distinction, not a newly discovered effect or a proof that any actual electron interaction is hidden KK geometry.

**New highest-alpha gates**:
- MG06.O1 FINITE PASS: identify visible observer and correct projected-resolvent consumer.
- MG06.O2 FINITE PASS: preserve hidden-mode self-energy as exact residual where coupled; test two states with same visible observation but different B.
- MG06.O3 FINITE PASS: verify hidden-frame invariance and decoupled negative control.
- MG06.O4 OPEN: replace synthetic A/B/D with independently selected native 369/KK source operators and actual observer maps, preserving Hilbert-domain and unitarity.
- MG06.O5 OPEN: compare recovered physical atom/protein observables and held-out data, not just finite algebra.
- MG06.GOLDEN OPEN: original canonical Agda observer/claim-transport theorem reuse and exact-head kernel acceptance.

**Scientific firewall**: A Schur complement transforms a *given* microscopic operator. The current construction does NOT derive a selected physical Hamiltonian, electron coupling/mass/spin, Maxwell/nuclear source, molecular forces or proteomic assay predictions; neither must every empirical error vanish after geometric refinement. No substitution of the original Coulomb Hamiltonian into a supposedly independent KK source is allowed. Continue from same-source KK + 369 physical operator before invoking this observer reduction.


### 2026-11-21 MG06 original 27-site/54-bond observer Hamiltonian Schur test

Native original owner inspected directly: `DASHI/Biology/Physical/BiologicalFullCubeIncidenceExact.agda` (master blob `49209b1c12e1433afef9ede6b911192c27bac3fe`) defines `PositiveBond` x/y/z over trits {-1,0,1}, proves 54 positive bonds, 36 elementary squares and actual nearest-neighbor incidence. New Python regression `scripts/check_mg06_native369_cube_observer_schur.py` committed `58a94356073c2e5527422aa7e06d1770ca18c71e`; executable local source originally failed on an invalid SymPy `Matrix.diag_join` method and was corrected to `sympy.diag(A,D)` before successful execution. **Four of four exact rational 27×27 Schur/resolvent comparisons passed** against graph Laplacian L=B^T B, trace 108; observers select one nine-site x, y or z slice and eliminate 18 hidden sites. Outer sheets have 9 crossing bonds, middle sheets 18; exact observer projected resolvent equals `(zI-A-B(zI-D)^-1 B^T)^-1` for (x,-1,z=-1), (x,0,z=-2), (y,1,z=-1), (z,0,z=-2). All four naive A-only projections fail; all four decoupled controls succeed. Actual result includes nonzero rational self-energy traces. No synthetic block operator was inserted; the inputs are the original combinatorial cube geometry. This is mathematically stronger than the earlier arbitrary 1+2 block fixture.

**Scope/non-promotion:** This graph Laplacian is a source-faithful finite incidence operator and not an independently supplied 5D KK Einstein/Dirac/Maxwell Hamiltonian. The nine-site sheet observer is a physically *unselected* geometric observer; hidden sheets are not the verified compact fifth dimension; no Coulomb coupling, electron mass/spin, physical source or hydrogen spectral match was derived. No Agda compiler receipt or exact GitHub checkout execution claimed. MG06.O4 advanced to **native 369 combinatorial operator instantiated and locally executed**; original physical KK same-H and observer/clock remain OPEN. Continue by selecting actual 5D physics action and embedding its operator/connection into this incidence representation with physically determined units, domain, boundary and observer map before making atomic claims.


### 2026-11-21 MG06 native P3^3 Cartesian spectral and observer-invariance cut

Reopened original `DASHI/Biology/Physical/BiologicalFullCubeIncidenceExact.agda` (master blob `49209b1c12e1433afef9ede6b911192c27bac3fe`), whose 27 sites / 54 oriented bonds / 36 squares use **nonperiodic** trit coordinate steps. Earlier native Schur script on this branch is `scripts/check_mg06_native369_cube_observer_schur.py` (blob `31c5fef78c2e7d5d1884a4e26769e3e200fdb912`). New directly sourced regression `scripts/check_mg06_native369_cartesian_observer.py`, commit `47457adffe0fd59fcbbd9ab7797938b2e7c41c57`, was locally executed with exact SymPy. Two incorrect test expectations (10 rather than **9** distinct cube eigenvalues, and 36 rather than **24** reduced 9-site trace) were discovered and corrected *before* committing. The locally executed equivalent source passed all post-correction assertions.

Native B^T B equals `L(P3)⊗I⊗I + I⊗L(P3)⊗I + I⊗I⊗L(P3)` exactly. Since `spec(L(P3))={0,1,3}`, the cube has 27 modes across **9 distinct eigenvalues**, agreeing with direct eigenvalue multiplicity; trace=108. Its 9D uniform-coordinate observer `W=I9⊗(1,1,1)/√3` has `W†W=I9`, `L27 W=W L9`, `W†L27W=L9`, and zero leaked coupling `(I-WW†)L27W=0`. By contrast, raw outer, middle, outer sheet observers have nonzero leakage norms squared **9,18,9**, respectively. This strictly separates an invariant-mode *observer* from a coordinate-slice *observer*, even though both output nine coordinates.

**Essential topology negative control**: replacing native path P3 by periodic C3 adds a wrap-around edge per transverse site, changes the trace from **108 to 126**, and changes the full spectrum. A trit axis must **never** silently be identified with a compact KK S1 fibre. Physical 5D topology, time/observer geometry, connection, units, electron state and source still require independent physical-source selection. This refinement changes mathematical MG06 observer operator status to **native exact finite spectral pass**; no physical KK-to-atom proof, measured protein mechanism, exact committed-checkout execution, or Agda Golden kernel receipt is claimed. Next highest-alpha: explicit topology-preserving map/obstruction between source-selected KK fibre and native 369 graph, with finite discretisation and spectral convergence rather than cardinality-based identification.


### 2026-11-21 MG06 native-to-periodic explicit seam and observer spectral gate

The canonical source `DASHI/Biology/Physical/BiologicalFullCubeIncidenceExact.agda` defines an original nonperiodic P3^3 grid, 27 vertices and 54 bonds; one must not reidentify a trit coordinate as compact S1 without modifying topology. New locally executed source `scripts/check_mg06_native369_explicit_seam_observer.py` committed as `e682c0fe9f72bf6285a9651e335e479e8bc7e4b9` implements nine **explicit additional** wrap-around seam bonds in the last coordinate, taking P3^3 (54 edges, Laplacian trace 108) to P3^2 x C3 (63 edges, trace 126). The exact operator increment is `Delta=S^T S`, rank 9, trace 18, nonnegative; full spectra are different. Native incidence and original 369 adjacency are preserved as the unmodified baseline.

The uniform last-coordinate observer `W=I9⊗(1,1,1)/√3` is isometric and is invariant under both Laplacians, since `Delta W=0`; both produce the *same* 9-site operator L(P3^2) for this limited consumer. The middle/outer **coordinate sheet** observers are not equivalent: seam correction traces at outer, middle, outer are 9,0,9, respectively. Six exact rational fibre Green-function comparisons (one for each distinct transverse eigenvalue of P3^2, at z=-1) verify that uniform observers cannot distinguish the two geometries, while an outer-sheet observer can; all six also satisfy the exact resolvent-update identity. This explicitly tests observational insufficiency rather than fitting a physical constant. The local equivalent source was executed; do not claim the exact GitHub checkout or Agda kernel was executed.

**Important scope:** `C3` is a three-site periodic toy graph, not by itself a physical KK S1; `P3` is a path graph, not a dimensional compactification. This establishes a topology-aware negative control and consumer-specific equivalence, not 5D Einstein/Dirac/Maxwell physics, electric charge, hydrogen or proteomics. The physically selected fifth dimension, holonomy, metric normalization, source and continuum approximation remain OPEN. **New MG06 seam subgate PASS (finite geometry), physical KK-to-369 identification OPEN**. Next accepted source step: define source-preserving maps with controlled lattice spacing a, circle radius R, Wilson link and kinetic normalisation, compare dispersion / spectral convergence of C_N to smooth S1 without silently altering the original P3^3 geometry; keep separate source-action and observed-atom gates.


### 2026-11-21 MG06 Wilson-twisted C_N to smooth S1 spectral convergence

The immediately preceding native graph/topology result is source-owned `BiologicalFullCubeIncidenceExact.agda` (original 27 vertices/54 positive edges/36 faces) and `scripts/check_mg06_native369_explicit_seam_observer.py` (explicit nine-edge P3^3 -> P3^2 x C3 topology change). The earlier KK #1241 `TOEKKCircleSpectrumConsumerBIDIExact.agda` distinguishes finite sampled Fourier aliases 0 versus 27; it is a sibling donor, not an imported same-branch Agda proof. **No native P3 trit coordinate has been relabelled as a physical fifth dimension.**

New independently defined compact-circle regression `scripts/check_mg06_circle_continuum_holonomy.py` committed at `3c06dbeea36acdec7a14a3c062872a53d7a1672f`. Equivalent code was executed **locally**, with NumPy complex eigenvector residual tests plus SymPy **exact** integer native-incidence checks: 120/120 mode-eigenvalue and error-bound cases over `N∈{9,15,27,54}`, `R∈{1,2}`, `theta∈{0,pi/2,pi}`, `k∈{-2,-1,0,1,2}`; 3 sampled Fourier character alias witnesses; 6 coarse-to-fine convergence checks (N=9 vs 54); native 27-site graph retains 54 bonds and trace 108. The output reports the maximum observed ratio to the analytic upper bound. The **floating-mode checks are numerical** (tolerance 2e-10), rather than exact SymPy roots-of-unity proofs. The error bound is an analytic sine inequality, whose sampled values are independently tested.

Mathematical dispersion for `a=2*pi*R/N`, phase link `exp(i*theta/N)` and fixed mode `nu=k+theta/(2*pi)`: `lambda_N=4*sin(pi*nu/N)^2/a^2` converges to `nu^2/R^2`, with `0<=lambda_cont-lambda_N<=pi^2*nu^4/(3*R^2*N^2)`; valid in the fixed low-mode regime, tested with `2*abs(nu)<N`. This model has explicit Wilson-phase input and radius input, not a derived 5D gravitational/Maxwell matter configuration. Sampled character alias `k~k+N` does **not** preserve the unbounded continuum energy; the residual integer alias/mode lift is required for that consumer. The bare normalized graph Laplacian without spacing and boundary conventions is not a continuum KK spectrum.

**Status:** observer/finite-resolution spectral compatibility CONDITIONAL PASS; original P3^3 graph invariance PASS; physical compactification field equations, embedding from native 369 geometry, clock/observer, electron spin/mass/charge, nuclear source, original H/He same-H and Agda Golden OPEN. Next cut: introduce an explicitly sourced metric/gauge/Wilson fibre and dimensionful coupling into the operator, test holonomy-aware parallel transport and physical observer reconstruction using original native 369 geometry separately. Do not conflate small Fourier residuals with a physical force derivation, nor a numerical matrix test with proof of full spectral convergence.


### 2026-11-21 MG06 source-selected KK metric / observer-coupling cut

**Source was reopened, not inferred from a filename:** sibling #1241 `Docs/physics/KKSingleActionRadionPhysicalSteelman20261024.md`, blob `f075962d4e5e4b81e5ee82b19bd41a82932933f5`, fixes the Jordan metric ansatz `ds5²=gJ+b²(dy+κA)²`, y dimensionless and 2π-periodic, with `M4²=2π b0 M5³` and a conditional matter frame. The sibling `scripts/check_kk_light_qed_dirac_same_action.py`, blob `948768cf9dfb3ca2fc2c83b713da8c24d68e11f4`, uses a **different independent 5D Maxwell field** as physical QED photon with calibrated `e5=e4 sqrt(2πb0)`; its bare Dirac electron mass is an observed input. The KK metric graviphoton and Maxwell QED photon are different source-owned fields. The winding model's nonzero winding gives the graviphoton a Stückelberg mass, a distinct physical negative control.

New local exact test `scripts/check_mg06_metric_connection_dimensional_source.py` committed at `0a75f09732755d93512e0f85a291899596202e44`. The exact same file was executed locally with SymPy after correcting a purely syntactic Matrix-equality check to simplify each entry. It passes metric block inverse, determinant `detG5=b²detgJ`, principal-symbol horizontal momentum `G^-1(p,p_y)=gJ^-1(p-κ p_y A,p-κ p_y A)+p_y²/b²`, local section-covariance with both the momentum and connection transformed, zero compact momentum decoupling, and unequal circle momentum energies on sampled-alias sectors. A minimal one-time, one-space plus fibre block is used; no new physical action is invented.

**Dimensional and observer-specific interpretation:** a finite 369 P3^3 graph Laplacian is still a distinct spatial incidence operator. The five-dimensional metric ansatz is independently selected. The physical observer's choice of p_y determines whether graviphoton coupling survives. Only with a *physically justified identification* of the metric connection to electromagnetic fields (not supplied in this source) may κ p_y be treated as physical electron charge. The 5D metric identity does not identify the geometric coupling with the independent Maxwell QED coupling, does not produce a nuclear source or Coulomb potential, and is at the principal-symbol/free-kinematic level rather than a full 5D Dirac reduction.

**Acceptance:** MG06.M1 source provenance recovered PASS; MG06.M2 inverse/determinant/horizontal geometric coupling symbolic PASS; MG06.M3 neutral and nonneutral observer sectors separated PASS; MG06.M4 independent Maxwell versus graviphoton firewall PASS; MG06.M5 full physical 5D action + matter-source solution OPEN; MG06.M6 native 369 incidence/KK fibre physical morphism OPEN; MG06.M7 atomic/helium same-H OPEN; AGDA Golden OPEN. Further work must derive an action-consistent finite covariant operator and compare its consumer-selected spectrum with independent hydrogen/helium producers, preserving coupling constants, units, local section change, boundary, and observer-specific residuals. An unproved claim that every physical model discrepancy is only a geometric error is not accepted.


### 2026-11-21 MG06 GR-QFT/QED/QCD unification source reconciliation and unique photon gate

**Important original-source correction**: the earlier #1241 light-QED free periodic S1 model's independent 5D Maxwell field B is a *candidate-specific source choice*, not a no-go against all geometric/gauge unified photon routes. Primary sources directly reopened on default branch:
- `Docs/physics/KKCasimirMinkowskiPhotonSourceMaxCut20261024.md` blob `145c132fcee147ce2e119a0d97da86d1e21a24c4`, which contains the stronger free periodic pure-geometric photon obstruction: `m_n²=m5²+n²/b²`, `q_n=sqrt(2)n/(M_Pl b)`, hence `m_n/|q_n|>=M_Pl/sqrt(2)` for n!=0 and nonnegative bare m5². It also distinguishes independent massless Maxwell B from metric graviphoton A.
- `Docs/physics/KKE6TwoVEVTorqueParityCSPhysicalMaxCut20261024.md` blob `fdc63b8290bbd0e12987617999de2b9d51c6c3e6`: original E6/first-Tits 27-trinification two-VEV stabiliser SU2_L x U1_Y, independent SU3c, and exact *additional photon* issue when the old independent B is also included. Source notes the old Casimir/Wilson spectrum cannot be transported to the E6 electroweak photon.
- `Docs/physics/KKE6OrbifoldChiralSourceMaxCut20261024.md` blob `db936cdbdeccd9a82aa1a20a8f858b5e6ff0f6df`: explicit P2 unique observed U1_EM photon remains OPEN, orbifold/two-VEV and potential Higgs do not yet pay full CS/WZ/eta anomaly, 5D vacuum or physical photon coupling.
- `DASHI/Physics/Foundations/TSFVKKSameArrowQuadraticMetricWeldExact.agda` blob `539e24285c74f88b571a0518513d918a7f074bb4`: measured observer/KK axis agreement conditional upon inhabited same physical metric. `docs/kk-braid-monster-qcd-quantum-gravity-maxcut-roadmap.md` blob `fbf8029e87163fd90b03497b0ee858976cd066e2` requires same physical QCD gauge field and quantum-gravity positivity/anomaly checks.

**Executed and committed finite negative controls**: `scripts/check_mg06_unification_photon_rank.py` commit `f9fbfc7eec5dbf738994c312804e13afde09afab` (locally executed exact SymPy, PASS). Neutral gauge Gram `v²q q^T` with basis (B,W3,Y) and `q=(0,-g2/2,gY/2)` has rank 1 and nullity 2. Including separately massless graviphoton gives nullity 3. EW alone (W3,Y) has nullity 1. Even adding a separate positive B mass while keeping graviphoton massless leaves nullity 2. Positive bare-mass periodic KK ratio satisfies the above exact lower bound. This finite Gram calculation counts zero directions under the *given source assumptions*: it is NOT a general quantum anomaly proof or exclusion of mixing/source completion. No exact-head Agda kernel verification performed.

**Resolution for MG06 programme**: do not proclaim that an independent Maxwell is fundamentally mandatory, nor identify gravitational KK coupling `kappa p_y` with electron charge by fiat. Choose a *single* source-consistent branch: (A) explicit Maxwell physical photon with calibrated matter couplings, and account for all extra massless U1s; (B) selected E6 EW photon `Q=T3+Y` with sourced Higgs/broken symmetry, removing or source-identifying old B and handling graviphoton; or (C) a new geometric photon theory that survives the original periodic free-mass/charge no-go. For any branch require one low-energy electromagnetism with correct charge/neutral current, QCD colour, anomaly/global quotient, consistent radion stress/Casimir, and same observer/metric/OS Hilbert construction. Preserve native P3^3 incidence and observer-residual cut. **MG06.U1 original sources recovered PASS; U2 finite mass-gram negative control PASS; U3 physical unique photon + common 5D action OPEN; U4 GR/QFT same state and source OPEN; U5 KK-to-atomic same-H OPEN.**
