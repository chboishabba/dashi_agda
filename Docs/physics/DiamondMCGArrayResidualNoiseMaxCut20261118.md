# Diamond MCG: array residual-noise maximum cut (2026-11-18)

## Scope and prior-art owners

This cut extends the **existing** [diamond MCG PR #1238](https://github.com/chboishabba/dashi_agda/pull/1238) rather than reinventing Maxwell, NV spectroscopy or calibrated sensor readout.

- `DASHI/Physics/QuantumSensors/DiamondMCGFiniteBridgeExact.agda`: finite Fourier magnetic-current-to-axial-sensor map; NOT a physiological torso forward solution.
- `DASHI/Physics/Closure/NSTriadKNMaxwellFluidBiotSavartBridgeExact.agda`: exact rational-mode current/field donor, not a free-space tissue Green function.
- `DASHI/Physics/QuantumSensors/NVSIMetrologyReadoutAdapterExact.agda`: SI/readout-calibration boundary.
- `scripts/psychotronics_field_loom_covariance.py`: independently authored correlated GLS and explicit common-calibration covariance; reuse as prior art, not a newly measured noise spectrum.
- `DASHI/Physics/Measurement/BioEMErrorBudgetExact.agda`: conditional error propagation.
- `DASHI/Physics/Closure/NSTriadKNExactFiniteComplexCauchySchwarzRound65.agda`: finite Cauchy–Schwarz owner; the weighted matched-filter optimality proof should reuse this algebra where compatible.

Original experimental credit: Muhib Omar and coauthors, *Human cardiac measurements with diamond magnetometers*, *Science Advances* 12 (2026), eaeg5281, DOI 10.1126/sciadv.aeg5281. Their measured sensitivity is not a certified all-frequency white-noise floor, nor a measured 1,000-element array.

## New checked algebra

Execute `python3 scripts/check_diamond_mcg_array_detection_exact.py` (requires SymPy).

For `N` identical sensor couplings `a`, independent-channel variance `sigma²` and equicorrelated covariance
`C = sigma²[(1-c)I + c 11ᵀ]` with `0 <= c < 1` (for `N>1`), exact inversion yields

`a² 1ᵀ C⁻¹ 1 = (a²/sigma²) N/[1+(N-1)c]`.

The symbolic checker verifies the inverse and information formula at N=1,2,3,5,10, plus the 2-channel nonuniform-response covariance formula. The closed form itself is valid for all positive integers N, conditional on the stated covariance assumptions; finite symbolic instances are **not an Agda all-N kernel proof**.

Projection against the uniform interference mode gives `P = I - 11ᵀ/2`. For two channels it retains target power `(x-y)²/2`, and erases a perfectly uniform target. Hence gradiometry must never be claimed to reject interference without an accompanying target-transfer budget.

For `A(r)=A₀(r₀/r)³`, coherent ideal matched-filter observation time scales as `r⁶`; fixed-duration independent noncoherent power-block integration yields an illustrative `r¹²` scaling. Constants, phase tracking, bandwidth, threshold search, stationarity, other source multipoles, and non-Gaussian tails are NOT paid by these symbolic identities.

## Actual residual-noise research contract

1. **Forward source:** anatomically constrained finite-size heart with bounded current and tissue return currents, sensor positions/axes, an appropriate Maxwell quasistatic operator, measured coordinates and orientation; include finite-source multipole error bounds, not only a point-dipole law.
2. **Sensor:** measured transfer functions with units, optical/microwave resources, useful photon counts, channel cross-talk and intrinsic noise vs frequency. Distinguish 1,000 sensor heads from 1,000 NV defects or 1,000 subelements sharing one readout.
3. **Noise:** estimate `C_n(f)` from off-target and held-out recordings with uncertainty; model sensor and environmental contributions jointly. Positive definiteness and covariance stationarity are measured/validated obligations, not assumptions silently promoted to empirical fact.
4. **Detector:** for a *specified* signal, weighted linear matched-filter information `∫s† C_n⁻¹ s df`; then a source-family search with unknown heart rate, phase, position, motion, orientation and frequency multiple-testing corrections. Optimize retained cardiac signal against **residual** noise, not noise reduction alone.
5. **Attribution:** compare target-consistent 3D spatial templates with other humans, animal heartbeats, engine/rotor and electric-line harmonics; require held-out false-alarm and detection probabilities and localization criteria.
6. **Envelope:** compare one sensor, compact array and distributed array under *equal aggregate resources*. Report constructive verified achievable ranges separately from model-class no-go upper bounds. Unbounded time is not free: sensor drift and source evolution require independently tested coherence/reset models.

### Acceptance gates

| Gate | This cut | Remaining obligation |
| --- | --- | --- |
| A1: existing finite magnetic forward owner | Located | Physical finite-heart/tissue geometry weld |
| A2: exact equicorrelation information | Symbolic checks PASS | All-N Agda kernel proof |
| A3: spatial-filter signal-loss control | 2-channel exact negative control PASS | General projector and anatomical template |
| A4: general coloured/correlated array noise | 2-channel SPD rational identity PASS | Frequency-resolved empirical cross-spectra and uncertainty |
| A5: integration exponent | Conditional algebra PASS | Physiological phase tracking, noise tails, threshold trials |
| A6: kilometre-scale heartbeat detection | NOT established | Same-device measured residual noise and attributable target signal |

This is an exact mathematical negative/positive-control cut, NOT a demonstration of kilometre-scale sensing. No live array data were accessed. Neither external authors' scientific results nor preexisting owner proofs are claimed as new.


## 18 November continuation: P1/W1 finite-array detector weld

New source: `DASHI/Physics/QuantumSensors/DiamondMCGArrayInformationWeldExact.agda`.

1. `allNWhitenedInformationUpperBound` imports the **existing** `NSTriadKNExactFiniteComplexCauchySchwarzRound65` owner and transfers its finite complex inequality to a noise-whitened sensor/filter response indexed by any finite support. The premise `ExactFiniteComplexCauchySchwarz` remains explicit: repo owner itself declares the concrete ordered-real instantiation open. This is not falsely marked a unconditional Agda theorem over physical reals.
2. `addedSensorsCannotReduceAttainableInformation` is a new generic score-monotonicity proof: if an old score-optimal detector is representable on the expanded array with exactly preserved score, then the attained expanded optimum is no smaller. It does **not** assume independent noise or claim that purchasing another diamond element yields any gain. Requires an exact preservation witness for the physical resource model.
3. `SignalPreservationReceipt` records both target response and filtered noise before promotion of any claimed SNR benefit. It is a receipt interface, not a proved inequality for a physical projector.

**Verification receipt:** `python3 /mnt/data/check_diamond_mcg_array_detection_exact.py` (local copy of committed `scripts/check_diamond_mcg_array_detection_exact.py`) completed successfully, concluding `All exact symbolic identities passed`. Agda executable unavailable in the current runtime; **no Agda kernel acceptance claimed**.

**Gate change:** P1/W1 moves from symbolic two-channel analysis to source-authored general finite-support theorem interfaces and a genuine abstract monotonicity proof, with exact-head kernel validation, inverse-covariance whitening construction, and instance-specific optimality still OPEN. P2–P6 remain OPEN.

**Highest-value next cut:** construct an actual positive-definite complex/real covariance-to-whitening owner (not an unexplained isometry), then instantiate all-N norm/score identities; prove covariance block extension via Schur complement, and quantify signal loss for spatial nulling using a projection theorem. Only then promote P1 to kernel-checked optimal linear detection.


## P1/W1 continuation: Schur-complement marginal information, 18 November 2026

**New evidence-bearing exact regression:** `scripts/check_diamond_mcg_schur_increment_exact.py`. Run with `python3 scripts/check_diamond_mcg_schur_increment_exact.py`; SymPy local check PASS for exactly rational positive-definite covariances built from `LLᵀ` with 1, 2, 3, 4, 6 and 10 existing channels; also checks symbolic arbitrary 2-channel covariance and the common-mode-null target-loss case.

For old covariance `C`, old signal `s`, new-channel cross covariance `c`, scalar new noise variance `d`, and new-channel cardiac response `t`, define:
```
v = d - cᵀ C⁻¹ c
u = t - cᵀ C⁻¹ s
I_old = sᵀ C⁻¹ s
I_new - I_old = u² / v
```
For jointly positive-definite covariance, `v>0`; hence information cannot decrease. A sensor gives **zero new information exactly when its conditional cardiac innovation is zero**. This corrects the naive idea that an individually sensitive added channel necessarily improves cardiac detection. All of these expressions are conditional on the same noise model and jointly calibrated physical response.

The regression also verifies the block inverse and a **negative control** in which `t=cᵀ C⁻¹ s` (the extra channel contributes exactly zero information), rather than just testing positive examples. Rational regressions do not constitute an all-N Agda proof.

**New Agda source:** `DASHI/Physics/QuantumSensors/DiamondMCGSchurInformationIncrementExact.agda`. This is an explicitly conditional information-identity and positivity *certificate consumer*, not a derivation of the Schur block inverse from matrix algebra. It supplies `schurAdditionDoesNotDecreaseInformation` and `redundantSensorAddsNoInformation` from the named premises. Source committed, **Agda executable unavailable, kernel verification not claimed**.

**P1 exact open proof obligations:** (i) instantiate a concrete SPD matrix over the repo ordered-real/complex finite carrier, (ii) build the block inverse and Schur-variance positivity in Agda, (iii) derive the gain equality rather than pass it as a field, (iv) prove target-preservation versus covariance reduction for spatially filtered arrays, (v) establish calibrated frequency-dependent covariance from raw measured channels. Prior-art complex finite CS owner itself explicitly leaves its concrete ordered-real instance open.

**Phase status:** P0 prior art inventoried, P1 symbolic Schur identity and conditional Agda receipts implemented but **P1 NOT CLOSED**; P2–P6 remain OPEN. No claim of kilometre-scale heartbeat detection, new instrument capability or sourced target attribution is promoted by this cut.


## 18 November P1/W1 prior-art correction: do not reinvent Schur

A broader repository and PR audit confirms pre-existing concrete/proof-bearing Schur mathematics:

| Existing owner | What it actually supplies | Applicability boundary |
| --- | --- | --- |
| `DASHI/Physics/YangMills/BalabanConstructiveRationalMatrixInverseExact.agda` | Finite rational coordinates, matrix action/product, proved product-action identity and further rational matrix inverse construction | Does not by itself certify an empirical magnetic cross-spectrum or SPD property |
| `DASHI/Physics/YangMills/BalabanP33FiniteKKTBlockInverseExact.agda` | Specific constrained KKT inverse after coercivity/uniqueness; real matrix work, not merely a label | Geometry and operator not automatically equal to cardiac sensor covariance |
| `DASHI/Physics/YangMills/BalabanSU2ConditionalCovarianceFormula.agda` | Conditional covariance operator, exact coarse constraint annihilation, and lifted-mode annihilation under explicit compatibility | **Direct reusable** projector logic; maps to actual interference only after physical identification |
| `DASHI/Physics/YangMills/BalabanFiniteConstraintCovariance.agda` | All-depth inductive `Q C Q*` covariance transport | Physical noise covariance measurements not contained in theorem |
| `DASHI/Analysis/BlockSchurStructure.agda` | Abstract Schur block definition and determinant socket | Not a constructed inverse or positivity certificate |
| `DASHI/Physics/YangMills/BalabanSU2ConditionalCovarianceConcrete.agda` | Inverse identities supplied through finite covariance certificate | Does not imply white-noise assumption or measured transfer |
| `DASHI/Physics/Closure/NSTriadKNRationalCauchySchurComplementRound443Exact.agda` | Rational Cauchy–Schur donor | Check proof signature before transfer to actual covariance |
| PRs #125, #371, #393 | Generic extraction and finite Schur/KKT/Combes–Thomas development | Not automatically a measured diamond array |

**New thin reuse module:** `DASHI/Physics/QuantumSensors/DiamondMCGExistingSchurCovarianceReuseExact.agda` imports `BalabanSU2ConditionalCovarianceFormula` and directly exports its already-established zero-coarse-response and zero-lifted-mode theorems. A second alias demonstrates the negative control: **a cardiac mode in the rejected lifted sector is erased as well**. These are structural consequences, not a calibration claim. This means the former roadmap statement that DASHI lacked general Schur definitions/operators was too broad.

**Changed max-cut:** avoid proving Schur itself again. Remaining high-value work is (a) the concrete *same-carrier* mapping from sensor cross-spectral covariance to existing finite rational/complex matrix structures, with units; (b) transfer of the actual Schur block inverse/positivity and heart-response vector, without changing its interpretation; (c) information increment proof using those operators; (d) measured `C_n(f)` and held-out source discrimination. Do not use unconditional squared-SNR claims where the physical covariance or target response is uncalibrated.

**Verification:** Existing local exact symbolic scripts rerun with PASS; new Agda module source-authored and uploaded to PR #1530. No Agda executable is available in the current container; **no kernel-checked result for the new module is claimed**. The existing owner's proof is imported rather than paraphrased as a newly proved theorem. P1 remains OPEN pending actual same-object covariance-to-magnetometer identification and new-module Agda checking.


## 18 November continuation: same-carrier inverse-covariance response and measured-data input

**New mathematical weld** `DASHI/Physics/QuantumSensors/DiamondMCGFiniteCovarianceCarrierWeldExact.agda`:
- Imports the **existing** `BalabanConstructiveRationalMatrixInverseExact` finite rational matrix carrier and both its proved inverse-action theorems.
- Uses the **existing** `DiamondMCGFiniteBridgeExact.modelMCG` as the per-sensor cardiac response from the same finite current mode, with a geometry-dependent sensor axis for every finite index.
- Constructs `inverseCovarianceResponse` by applying the inverse-covariance operator to that response; `covarianceRecoversCardiacResponse` proves the computed response solves the covariance normal equation pointwise, **not** via a Schur identity postulate. `inverseRecoversCovarianceAppliedVector` proves the opposite inverse direction.
- Separately requires `physicalCovarianceIdentification` as an evidence-specific witness: converting SI-valued cross-spectral magnetic covariance (T²/Hz) and sensor magnetic response (T) to dimensionless rational coordinates is NOT automatic. `physicalFrequency` and `physicalFieldScale` carry already-defined SI dimensions; these labels alone do not prove the conversion or sensor calibration.
- Does **not** assert that arbitrary measured covariance is symmetric, SPD, or invertible. The existing matrix owner requires its exact two-sided inverse certificate. No calibration observations have been supplied.

**New measured-data gate** `scripts/diamond_mcg_cross_spectrum_acceptance.py`:
- Accepts only explicitly source-labelled instrument/dataset/calibration records with frequency-specific complex response and complex cross-spectral covariance in T²/Hz.
- Checks finite numerical data, frequency and bin width, Hermitian covariance, and strict positive numerical eigenvalue lower bound before using a whitened solve. Reports known-response conditional weighted information. An ill-conditioned or singular matrix fails closed.
- Synthetic self-test covers independent noise, correlated noise degradation, non-Hermitian and indefinite negative controls. This is a **numerical replay gate**, not physical calibration, statistical false-alarm control or Agda kernel acceptance; measured files are not bundled or invented.
- Numerical formula uses a one-sided Fourier convention and 4× frequency-bin bandwidth; a future measured source must identify its spectral conventions, transfer normalization, calibration uncertainties, and appropriate discrimination/phase-tracking model.

**Exact executed local checks:** existing SymPy scripts `check_diamond_mcg_array_detection_exact.py` and `check_diamond_mcg_schur_increment_exact.py` both PASS. A locally executed matching cross-spectrum acceptance prototype passed synthetic SPD/correlation negative controls. GitHub version was committed but not independently executed from a checked-out exact Git blob in this runtime. The Agda executable is unavailable here, so the new Agda source remains **source-authored, not kernel-verified**.

**P1 status:** now has a concrete finite rational matrix inverse -> diamond source-response reuse weld, plus a fail-closed path for future real cross-spectral measurements. Remains **OPEN** pending (i) Agda exact-head check, (ii) a calibrated SI-to-rational/complex cross-spectrum interpretation with uncertainties and spectral normalization, (iii) SPD/inverse construction on measured covariance, and (iv) proof that the physical frequency-domain matched-filter objective agrees with the finite model. P2–P6 remain OPEN. The next prioritised action is testing this actual bridge in the pinned Agda toolchain, followed by P2 anatomical source response and independent empirical cross-spectra acquisition.
