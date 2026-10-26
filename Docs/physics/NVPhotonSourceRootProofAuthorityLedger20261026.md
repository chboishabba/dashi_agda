# NV quantum readout max-cut: source-root and verification ledger (2026-10-26)

This audit implements `Docs/SourceAttributionPolicy.md` by keeping original source roots, the mathematical prior art, repository implementation chronology and proof authority distinct.

| Claim / carrier | Original source or owning repository source | DASHI extension in PR #1269 | Authority state |
| --- | --- | --- | --- |
| NV− spin-1 ground-state axial energy `E±=D±γB,E0=0` | Existing Diamond MCG PR #1238, `DASHI/Physics/QuantumSensors/NVSpinOneAxialExact.agda`. Standard NV physics; physical constants require primary instrument source | Same-object C3 ↔ qutrit chart; field-reversal and energy-only decoder no-go | Source-written, not a measured three-level spectrum |
| NV optical photon response | Diamond MCG PR #1238, `NVPhotonBinaryLikelihoodExact.agda`, normalized likelihood with separate nonnegativity obligations | Conditional state-labelled observer, equal-response collision and additional-response separation | Algebraic conditional theorem, photon parameters not calibrated |
| Diamond MCG human observations | Muhib Omar et al., *Human cardiac measurements with diamond magnetometers*, *Science Advances* 12(38), eaeg5281 (2026), DOI **10.1126/sciadv.aeg5281**; source specifics recorded in `Docs/physics/DiamondComplexC3MCGMeasuredCalibrationMaxCut20261024.md` on PR #1238 | None of the quoted measured sensitivities is an NV quantum gate/readout-fidelity receipt | Published system measurement; no reconstructed raw individual data or quantum-processor performance |
| Three-level quantum representation | Existing `FiniteQutrit.agda`; existing `Core/FiniteC3OrbitStabilizerExact.agda` | Reversible conventional label chart, not a physical spatial (C_3) action | Finite source-written label equivalence |
| Finite SUSY-QM factorization | Classical supercharge anticommutator formalism; independent NV companion PR #1262 | Ideal `Sz²` factorization and Zeeman obstruction are owned by #1262, not copied here | Ideal mathematical system, NOT spacetime SUSY or observed superpartners |
| Symmetry classification | Crystal PR #1261 is tetragonal D4h, not diamond bulk `O_h` or ideal NV local `C3v` | Only group-action *method* is a donor | No NV-site representation asserted from D4h |
| Conditional Bernoulli independent repetitions and Bayes risk | Classical probability/statistical decision theory; repo-native likelihood type #1238 and statistics evidence core | Explicit products, count-class sufficient statistic, O(n) Bayes exact-rational executable and conditional upper-bound calculations | Mathematical conditional model, independence unmeasured |
| Pascal/binomial multiplicity | Classical combinatorics, `Data.Nat.Combinatorics._C_` already used in `DASHI/Foundations/BishopExponentialBinomialCoefficientExact.agda` | `NVPhotonPascalCountClassesExact.agda` finite recurrence and trivial base identities | The bridge to filtered history cardinalities is **not yet proved** |
| TSFV/coherent optical paths | Diamond MCG #1238 + TSFV source programme Agda #621 | Optical path interference is separate from spin energy/permutation C3 | No physical action-phase calibration or computation advantage inferred |
| Experiment/promotion receipts | `dashiQ` PRs #2/#3 | Proposed future consumer only; do not claim runtime receipt integration | No observed same-device state preparation or held-out readout trial |

## Implementation versus validation chronology

- Historical roots are owned by the primary cited sources and earliest implementing PRs. A present commit does **not** reassign those definitions' authorship or priority.
- Our additive PR #1269 stems from the MCG #1238 branch and must preserve its historical ancestry. The newly revised attribution comment on the Pascal carrier was implemented in commit `845c73ba956dd54df9ca968cc8d3c90bf39df646` on 2026-10-26.
- Previous distinct #1269 source commits include reversible chart `80e5fac`, observer collision `a6f295c`, photon refinement `9f4289c`, one-shot risk `9b25c61`, two-shot kernel `76b335c`, history likelihood `9854fed`, tree normalization `1497370`, explicit-sum normalization `d981773`, count class sufficiency `0e47562`, and Pascal recurrence `b5921b6`. Prefixes are for navigation, not assertions about first historical implementation elsewhere.
- Source-written Agda files have not been certified by an Agda kernel execution in this session. Executed exact Python parameter-grid regressions are separate from general Agda proofs and from laboratory measurement.
- Existing `scripts/check_nv_photon_count_class_bounds_exact.py` reports exact rational tests of a source-described ideal i.i.d. model. It does not import original experiment waveforms or validate manufacturer hardware.
- CI deliberately not pursued on user instruction.

## Highest-value outstanding proof and experimental obligations

1. Prove the literal filtered length-`n` history class count equals the existing stdlib binomial coefficient, without replacing or duplicating its canonical owner.
2. Bring the analytic error bound into Agda's existing rational-order library as a theorem; don't mistake finite parameter-grid tests for quantification over all rational probabilities.
3. Obtain state-conditioned **same-device** optical data, trial/preparation dependence, detector background, and held-out validation. Nothing in the mathematical model proves the purported 16×8 multicore quantum processor was calibrated, entangled, or outperformed classical alternatives.
4. Only then connect a provenance-identified `dashiQ` experiment receipt and consider promotion.

## Attribution discipline

Repeated reports of a paper, reprints, media clips and downstream repository comments are not independent source roots. Existence of a paper, the claims it attributes, corroboration by raw data, and a kernel-verified theorem are different statuses. Every donor retains the original scope and credit; extensions are labelled as DASHI reconstructions or new consumer-specific propositions, not retroactively attributed to the originating authors.
