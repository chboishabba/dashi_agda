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


## 18 November P2 exact finite-extent source / array geometry cut (SymPy, no CI)

**Committed producer:** `scripts/check_diamond_mcg_finite_source_geometry_exact.py`.

**Independent local SymPy execution:** PASS for exact finite-pair field, point-dipole error, dimensionless expansion, derivative/monotonicity, far-field limit, two-sensor gradient and target-signal projection loss; exact-rational geometry fixtures at 1 m, 10 m and 1000 m PASS. The local checker reproduces the committed formulas and cases; it is not an independently fetched source-blob replay.

The first constrained finite-extent source **test fixture** is two equal, aligned magnetic dipoles centred at axial offsets `+a` and `-a`, measured at `r>a`. Absorb the common angular factor and total moment into `K`. Then:

```
B_pair/K = (1/2)[(r-a)^(-3)+(r+a)^(-3)]
         = r(r²+3a²)/(r²-a²)³
B_point/K = r^(-3)
B_pair/B_point = (1+3x²)/(1-x²)³,  x=a/r
(B_pair/B_point)-1 = x²(x⁴-3x²+6)/(1-x²)³
d/dx (B_pair/B_point) = 12x(1+x²)/(1-x²)^4 > 0, 0<x<1
lim_(x→0) (B_pair/B_point-1)/x² = 6
```

The exact relative error is nonnegative over `0<x<1`, and monotonic; hence for `a/r<=1/10` it is bounded by `59701/970299 ≈ 0.06153`. For `a/r<=1/2` a looser exact bound is `85/27`. These are specific symmetric axial test-source bounds **not** universal human-heart finite-size bounds, anatomical calibration or a continuum Biot–Savart volume-conductor theorem.

Two sensors at `r-h`, `r+h` observe point-dipole responses whose exact difference is

```
G = (r-h)^(-3) - (r+h)^(-3)
  = 2h(3r²+h²)/(r²-h²)³,
lim_(h→0) G/h = 6r^(-4).
```

With the two-sensor uniform-mode projector `P=I-11ᵀ/2`, the **cardiac signal** power retained is `G²/2`. At a fixed physical baseline `h` and increasing range, differential cardiac amplitude decays as `r^-4`, not `r^-3`. If residual differential-noise amplitude spectral density remains range-independent and coherent integration is admissible, this implies a conditional `T ∝ r^8` time scaling, versus `T ∝ r^6` for a retained direct dipole mode. A gradiometer must be selected by actual post-filter signal-to-noise, not noise rejection alone.

This is a **P2 mathematical partial closure** of one finite-source axial test case and spatial negative control. It does not establish general source orientation, tissue return currents, Maxwell boundary conditions, finite-heart current bounds, finite source support across all cardiac morphologies, or a measured array. The existing `DiamondMCGFiniteBridgeExact` Fourier finite-mode owner is preserved, but free-space point/finite-dipole fields are not falsely identified with its periodic Fourier model.

**Next P2 highest-alpha cut:** finite vector-dipole source family, explicit sensor 3D position/orientation, per-sensor axial projection and actual anatomical multipole remainder bound over a bounded source/current family; then link the resulting array response to the already-implemented covariance GLS acceptance. P3 resource-matched 100/1000-element array tests only after this source geometry is represented. P1 Agda kernel acceptance and measured covariance remain open.


### P2 3D orientation / directional readout continuation

Added `scripts/check_diamond_mcg_3d_source_response_exact.py`, independently executed locally with SymPy: **PASS**. It checks the *classical free-space magnetic dipole* geometric field `B=(mu0/4pi)[3(m·R)R-|R|²m]/|R|^5`; symmetric trace-free dipole tensor, proper rotation covariance, axial and equatorial field values, a zero-response NV axis when orthogonal to the field, recovery on a transverse measurement axis, and consistent reduction to the symmetric finite axial pair already tested.

**Important domain repair discovered during checking:** an observer at `r-a` must satisfy `r>a>0`; naive simplification of `(r-a)^2` to `(r-a)` under a square root without this premise is invalid. The checker establishes the positive-separation identity before substituting the domain-constrained coordinate. No unqualified absolute-value elimination is permitted.

This demonstrates that simply increasing channel count is insufficient if every NV axis is blind to the physically possible source orientation. P3 must optimize angular sensing response *jointly* with noise/cost and spatial positions. Both P2 scripts use **magnetostatic test fixtures**, not experimental or anatomical heart-current distributions, not actual human cardiac moments, and not a proven equivalence to the existing periodic Fourier Biot–Savart representation.

Executed SymPy controls now include finite-extent axial source field, exact finite-size error and asymptotics, two-sensor gradiometry `r^-4` field decay, 3D rotation covariance, and directional detection nulls. **P2 is partially advanced but NOT closed.** Anatomical 3D source geometry, tissue conductivity, return-current closure and uniform multipole bounds across the source family remain open. No CI or Agda kernel acceptance is claimed per this round's SymPy-only instruction.


## P3 — Array geometry and resource comparison (18 November 2026)

**New code:** `scripts/check_diamond_mcg_array_resource_p3.py`; locally executed matching SymPy/NumPy experiment **PASS**. It compares `N∈{1,100,1000}`, two planar disk diameters (2 cm, 50 cm), single-z vs interleaved x/y/z axes, two budget regimes, and detection ranges 2, 10, 100, 1000 m. Results are **synthetic mathematical fixtures, not human MCG measurements**.

**Model:** each sensor measures its sensing-axis projection of the free-space vector dipole tensor `(3rrᵀ/|r|²-I)/|r|³`. Target information for three unknown dipole moment coordinates is the finite GLS Gram `F = Sᵀ C⁻¹ S`, evaluated without a dense 1000×1000 inverse using the **Woodbury identity** on `C = D+UUᵀ`. `U` contains three common 3-vector magnetic field modes and six planar gradient modes; `D` has independent channel noise. `lambda_min(F)` is the worst-orientation detection information; `trace(F)` sums information across all orientations but **does not guarantee target orientation coverage**. All quantities below are normalized information units, not T²/Hz or calibrated probabilities.

**Resource fairness:** `fixed-total` assumes allocating a fixed photon/readout resource to N independent channels raises each channel's variance as `N`; `per-channel` holds individual noise variance fixed and therefore increases aggregate sensing resources with N. The first is a deliberately constrained comparison, not a universal NV physics law. Common field and gradient nuisance amplitudes are also synthetic fixed inputs (0.5, 0.15 in dimensionless units).

### Reproducible result at 10 m, fixed aggregate independent-channel resource

| N | Disk diameter | Sensor axes | trace(F) | min eigenvalue(F) |
|---:|---:|---|---:|---:|
| 100 | 2 cm | z only | 3.19999490e-6 | 2.21645483e-12 |
| 1000 | 2 cm | z only | 3.19999490e-6 | 2.24665981e-12 |
| 100 | 2 cm | x/y/z | 1.83761091e-6 | 3.04849735e-7 |
| 1000 | 2 cm | x/y/z | 1.84529904e-6 | 3.07408090e-7 |
| 100 | 50 cm | z only | 3.19681420e-6 | 1.38195081e-9 |
| 1000 | 50 cm | z only | 3.19681432e-6 | 1.40075705e-9 |
| 100 | 50 cm | x/y/z | 1.83601174e-6 | 3.04756019e-7 |
| 1000 | 50 cm | x/y/z | 1.84371716e-6 | 3.07300558e-7 |

At 2 cm disk diameter, the 1000-channel x/y/z array improves **worst-orientation information only about 0.84%** over 100 channels under this fixed resource model. With per-channel resources held constant, the 1000-channel x/y/z model instead has worst-orientation information `3.95326107e-6` versus `3.56763146e-6` for 100 channels, reflecting both new sensor resources and correlated nuisance limitations. These are **not** detector SNR or range multipliers.

**Two important negative controls:** all 100 co-located z-axis sensors have zero information for orthogonal source moments (rank-one information), regardless of perfect magnetic sensitivity; and co-located identical sensors with fixed total photon budget and no ambient interference satisfy the exact identity `N/(N sigma²)=1/sigma²`, so splitting a fixed resource cannot magically produce `sqrt(N)` SNR growth. The exact 2x2 low-rank Woodbury identity was independently SymPy-checked.

**Source-validation boundaries:** no optical photon statistics, diamond material resource model, spectral transfer, tissue-return currents, NV-axis constraints/selection rules, sensor crosstalk, measured `C_n(f)`, cardio-dynamic source, or multiple-hypothesis false-alarm model was available. A 50 cm disk is a mathematical layout, not an installed apparatus. The 1 km row is only an extrapolation of the point-dipole model, not detection evidence.

**P3 status: mathematical architecture benchmark implemented, physical design optimisation remains OPEN.** The highest-alpha next cut is (i) a measured frequency-resolved covariance and readout resource law; (ii) joint axis/baseline/range optimisation with unknown-source orientation and location, not just these hand-picked designs; (iii) P4 variable-heartbeat detection/attribution and time/false-alarm acceptance. Reuse the existing covariance and Biot-Savart owners; no extra Schur algebra required.


## P3/P5 — Source-FOV optimal axis allocation and steelman (18 November 2026)

**Committed checker:** `scripts/check_diamond_mcg_fov_steelman_p3.py`. Exact SymPy axial split and locally evaluated numerical angular-cone grid; numerical grid results rounded and subject to discretisation tolerance. Source committed through GitHub; exact-blob local replay was not available in this session. No Agda kernel or experimental claim.

For a fixed look direction along `z`, the normalized far-field dipole map is `D=diag(-1,-1,2)`. For independent-noise, co-located axis measurements with normalized total resource `p_x+p_y+p_z=1`, information is `Dᵀ diag(p_x,p_y,p_z) D`. An E-optimal (maximum minimum eigenvalue) allocation sets `p_x=p_y=4/9`, `p_z=1/9`; `lambda_min=4/9`, compared to `1/3` for equal-axis allocation. This is an **exact on-axis mathematical optimum**, not an installed NV allocation or a spatial baseline optimum.

For a look-direction cone `0<=theta<=theta_max`, every azimuth is reduced by rotational symmetry; numerically maximize `min_{look,moment} mᵀ D(n)ᵀ W D(n)m / ||m||²` over axis allocation `W=diag((1-p_z)/2,(1-p_z)/2,p_z)`. Grid result:

| Cone half-angle | Approx optimal p_z | Worst-case normalized information | Gain over equal axes |
|---:|---:|---:|---:|
| 0 deg | 1/9 exact | 4/9 exact | 33.3% exact |
| 10 deg | 0.176 | 0.3861 | 15.8% |
| 20 deg | 0.239 | 0.3516 | 5.5% |
| 30 deg | 0.300 | 0.3355 | 0.6% |
| >=45 deg | 1/3 | 1/3 | 0% |

These **conditional** values assume point dipole, fixed distance and budget, co-located sensors, no correlated nuisance, exact axes, and no spatial position uncertainty or finite-source cancellation. They should not be misrepresented as a result for finite-heart current families. A fixed global axis allocation for an off-axis look direction need not remain optimal if full environmental covariance breaks axial rotational symmetry.

**Optimistic distance steelman with transparently assumed empirical reference:** `A_0=50 pT at r_0=0.1 m`, `S_B=7 pT/sqrt(Hz)`, all N channels independent at this sensitivity, coherent known-phase/known-source integration, target threshold 5, dipole amplitude decay `r^-3`. Conditional `T=(5S_B/(A_0 sqrt(N)))²(r/r_0)^6`, subject to spectral/phase normalization conventions and no look-elsewhere/false-alarm adjustment.

| Assumptions | 10 m required time | 100 m required time | 1000 m required time |
| --- | ---: | ---: | ---: |
| N=1000, 7 pT/sqrt(Hz) per channel | 15.53 yr | 15.53 million yr | 15.53 trillion yr |
| N=1000, 1 pT/sqrt(Hz) per channel | 0.317 yr (~116 days) | 316,881 yr | 316.9 billion yr |

This is not a lower bound against every possible future sensor technology, nor proof of impossible remote biomagnetometry. It is a steelman calculation **conditional** on this benchmark signal, fixed per-sensor sensitivity and coherent idealizations. It is also **not the fixed-total-resource P3 comparison**; achieving the same per-element sensitivity for N=1000 incurs more resources. The calibration reference at 10 cm should not be promoted to a validated 10m–1km human cardiac dipole law: source orientation, multipoles, body-current closure and spatial environmental attenuation are unverified.

**True worst-case issue:** A source family with no lower bound on measured magnetic cardiac moment admits arbitrarily weak or cancelling observable signals, so minimax source information can be **zero regardless of array geometry**. Worst-orientation eigenvalue for a fixed *nonzero dipole moment* does not solve worst-case anatomical source, unknown location, interference, human identification or sensor stability. An honest certified positive range needs a bounded and nonvanishing target source class (or a probability distribution with specified detection quantile) and measured cross-spectral covariance.

**New spatial-optimisation gate:** jointly optimize true 3D sensor positions, 3D axes, source location within the requested angular cone and range interval, resource costs, common nuisance modes, robust cardiac source family and finite-aperture constraints. Test a single-source matched filter and held-out source-versus-nuisance discriminator with multiplicity-corrected false-alarm/detection rates. The current result is *axis allocation for an ideal FOV*, not an optimal physical sensor spread.


## 18 November correction: prioritize BEST-CASE steelman, not E-optimal worst orientation

**Correction:** Prior P3 FOV axis allocation maximized the *smallest* eigenvalue of the Fisher matrix. That is a defensible ROBUSTNESS result, **not** a best-case steelman. It must not be promoted as the primary best-case array optimization. For a known look direction, ideal co-located free-space dipole response `D = diag(-1,-1,2)/r³` and fixed independent-noise resource, maximum source-direction information is `4/r⁶` by choosing the line-of-sight moment and matching the sensor-axis orientation. The earlier `4:4:1` allocation optimizes the *minimum*, not the maximum, eigenvalue; its `4/9` minimum is not a best-case result.

**New implementation:** `scripts/check_diamond_mcg_bestcase_steelman_p3.py` replaces the optimization target with the **largest eigenvalue** of the source Fisher Gram `Sᵀ C⁻¹ S`, optimizing source moment analytically and two independently weighted sensor macro-group positions/axes numerically. It optionally maximizes over source bearing in a viewing cone (not the minimum across that cone). The model uses the exact point-dipole tensor and a simple correlated uniform two-component ambient field. A fixed aggregate independent sensing resource makes group coadded variance independent of splitting each of the two macro-groups into 50 or 500 identical channels: the same best-case objective applies at 100 or 1000 channels under **this particular assumed resource law**, not universally.

For source distance `r`, sensors in the planar disk and a fixed total independent-noise budget, the spectral norm of the free-space dipole tensor gives a rigorous model upper bound:
```
I_best <= 4/(sigma² * d_min^6)
```
where `d_min` is the nearest geometrically allowed sensor-to-source separation; here `sigma²=1` is the dimensionless total resource noise variance. This bound remains valid with added positive semidefinite ambient covariance. In no-ambient cases, co-located aligned sensor groups attain it exactly for an on-axis source (in the ideal point-sensor limit). This gives a **provable model optimum**, not merely an arbitrary local numerical search result. With correlated ambient noise the differential-evolution result is only a feasible lower witness, possibly suboptimal: the bound-to-witness gap is reported and global optimality is **not claimed**.

**Local exact SymPy checks and numerical witnesses, 50-cm aperture** (all normalized, not physical SNR; `tau` is the common-field standard deviation relative to normalized independent-noise scale):

| Source distance | tau | viewing-cone half-angle | feasible best-case information | rigorous loose upper bound | fraction of upper |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 2 m | 0 | 0 deg | 0.062500 | 0.062500 | approximately 1 |
| 2 m | 10 | 0 deg | 0.0025971 | 0.062500 | 4.16% |
| 10 m | 0 | 0 deg | 4.0000e-6 | 4.0000e-6 | approximately 1 |
| 10 m | 10 | 0 deg | 4.5063e-8 | 4.0000e-6 | 1.13% |
| 10 m | 10 | 20 deg | 4.5063e-8 | 4.0000e-6 | 1.13% |
| 100 m | 10 | 0 deg | 3.9659e-14 | 4.0000e-12 | 0.991% |

Under correlated-noise cases the optimizer convergence flag is false at its iteration limit: **these are feasible designs only, not certified maxima**. This is an explicit optimization residual, not a hidden success flag. No output here is an empirical NV or human-heart sensitivity/range claim. The prior 7 pT/√Hz / 1000-sensor range table remains an illustrative independent-*per-channel*-resource reference and is not the fixed-total-budget output here.

**Next gates in strict steelman order:** (1) replace model-only `C` by measured frequency-dependent residual cross-spectral covariance and include NV transfer/readout costs; (2) extend from two planar macro-groups to full finite array positions/axis distributions with physically allowed NV crystal orientations; (3) optimize over the strongest source geometry/current waveform consistent with primary cardiac evidence, including sensor-to-source geometry and anatomy; (4) optimize spectral template and finite coherent/partially coherent integration under validated phase stability; (5) only then report range and statistical detection/attribution. Worst-case eigenvalue and minimax FOV coverage remain separate *secondary* robustness gates.

**Verification scope:** exact theoretical identities and comparable numerical cases were executed locally with SymPy/NumPy/SciPy before commit; this is **not** an exact Git-blob replay or an Agda kernel check. No CI requested.


## 18 November: CRYOGENIC RECEIVER / ABSOLUTE-ZERO PRIOR ART (steelmanned)

**Why this is a separate high-alpha branch, not more banal array geometry:** Omar et al., *Science Advances* 2026 (DOI 10.1126/sciadv.aeg5281) demonstrated room-temperature NV-diamond cardiac magnetic recording, reported sensitivity 6–26 pT/sqrt(Hz). Cooler sensors may be a different hardware class (e.g. superconducting quantum interference devices), not simply NV diamond with a lower scalar noise knob. The physical upper-limit steelman must compare receiver architectures and their measured cardiac-band noise rather than repeatedly discussing covariance/spacing.

**Existing Agda owner:** PR #701, `DASHI/Physics/QuantumVacuum/ZeroPointModeHyperfabricExact.agda`, `HarmonicOscillatorDoubledEnergyExact.agda`, `ZeroPointExtractionFirewallExact.agda`. The oscillator law `E_n=(n+1/2)hf` distinguishes ground energy from thermal excitations and forbids interpreting nonzero vacuum energy as extractable work. This is the relevant formal spine; it does *not* imply a universal magnetic instrument PSD or a 0-Kelvin noise-free detector.

**New exact SymPy/model checker:** `scripts/check_diamond_mcg_cryo_zero_point_steelman.py`. Tests ground/excitation split, symmetrized equilibrium harmonic-mode `coth(hf/2kT)` identity, extra sensor standoff scaling, and conditional coherent threshold time. In local SymPy, `coth` must be rewritten as exponentials before simplification to zero; fixed in commit 158ee49b. Exact committed blob not independently run in this runtime. No Agda kernel acceptance, measured cryogenic PSD or SQUID-array demonstration is claimed.

For `f=1 Hz`, the crossover `hf/k_B ≈ 4.799×10^-11 K`. Thus a 4-K magnetic receiver has *enormous* thermal occupancy of **an ideal equilibrium 1-Hz oscillator**. This does not equate all cardiac-band external magnetic interference to blackbody noise: electrical/magnetic receiver noise physics must be separated by mechanism (spin projection, photon readout, Johnson currents, superconductor flux fluctuations, mechanical vibration, drift, environmental and room-temperature human/body fluctuations). Cryogenic NV spin `T2` improvements with dynamic decoupling cannot simply be carried to quasi-DC heartbeat sensing because the pulse filter may suppress the heart frequency too.

**Receiver sensitivity scenario, not a physical prediction:** retain the illustrative 50 pT amplitude at 0.1 m, ideal dipole `r^-3`, 1000 statistically independent identical channels, coherent SNR threshold 5, and unrealistically unlimited phase stability. For single-channel ASD 7 pT/sqrt(Hz), 1 fT/sqrt(Hz), or 0.01 fT/sqrt(Hz), conditional integration time scales with noise ASD squared. Reference results:

| Per-channel ASD | 10 m time | 100 m time | 1 km time |
| --- | ---: | ---: | ---: |
| 7 pT/sqrt(Hz) | 15.53 years | 15.53 million years | 15.53 trillion years |
| 1 fT/sqrt(Hz) (SQUID-like receiver scenario) | ~10 seconds | ~116 days | ~316,881 years |
| 0.01 fT/sqrt(Hz) (extreme hypothesis) | ~1 ms | ~17 minutes | ~31.7 years |

The 1000 independent per-channel sensitivities assume **1000× hardware**, not fixed total resources; 0.01 fT/sqrt(Hz) is an extreme mathematical input, not an empirically established diamond or SQUID MCG sensor. These numbers do not account for 1/f noise, coherence loss, source variability, environmental fields, or look-elsewhere search thresholds. A stronger source/hardware model can shift these; present as conditional envelope only, not impossibility theorem.

Cooling incurs cryostat vacuum windows, optical/microwave power and cooling-budget penalties. For a dipole at sensor distance `r`, additional cold-stage standoff `d` reduces amplitude by `(r/(r+d))^3` and increases same-ASD ideal integration time by `(1+d/r)^6`; a marginally stronger receiver might lose the gain at close range. The *human source remains near physiological temperature*, not near 0 K. Body thermal current and dynamic biological signals are independent environmental source terms.

**Revised steelman priority:** P3/P5 compare **room NV, cryogenic NV, SQUID, alternative atomic receivers** against actual sensitivity PSD across ~0.5–40 Hz and measured environmental covariance, including stand-off, total readout/cooling resources, quantum readout floor and signal coherence. Only after a receiver architecture survives these comparisons is detailed spatial/FOV layout optimisation worth doing. P4 needs realistic noncoherent/semicoherent heartbeat integration; no 1-km detection promoted.

**Primary references used in analysis:** Omar et al. 2026 DOI 10.1126/sciadv.aeg5281; *Spin Readout Techniques of the Nitrogen-Vacancy Center in Diamond* (2018); *Diamond surface engineering for molecular sensing with nitrogen—vacancy centers* (2022); NIST cryogenic SQUID sources. Source search and publications do not supply a measured best receiver-plus-human-heart 1-km error budget.


## 18 November 2026 — SOURCE-CLASSIFIED SQUID / CRYOGENIC SUPERCONDUCTOR STEELMAN

Previous 1 fT and 0.01 fT rows were **arbitrary receiver substitutions**, not an SOTA scientific benchmark. This source-backed cut corrects that: neither an isolated sub-fT white-noise component nor a SQUID under magnetic shielding implies that the same noise spectrum is available to each of 1000 independent sensors outside a lab at a cardiac frequency.

New checker: `scripts/check_diamond_mcg_squid_sota_source_steelman.py`, with exact SymPy rational `T ∝ S_B²r⁶/N` controls. Local equivalent checker executed PASS (range^6, ASD^2, N^-1, 0.1fT-vs-1fT=1/100 time). GitHub script committed, not independently replayed by exact Git blob. No CI or Agda kernel check.

| Receiver / publication | Reported source sensitivity | Critical domain limitation |
| --- | --- | --- |
| *Human cardiac measurements with diamond magnetometers* (Omar et al., Science Advances 2026; https://pmc.ncbi.nlm.nih.gov/articles/PMC13580569/) | 7 pT/sqrtHz is one tested configuration; 6-26 pT/sqrtHz across systems | Measured near-body NV cardiac detection, not far-field or 1000 channels |
| *SQUID Magnetometers for Natural EM Signals* (Kawai et al., 2024; https://www.jstage.jst.go.jp/article/jcsj/59/1/59_19/_article/-char/en) | ~25 fT/sqrtHz over 0.5-100Hz | **Actual cardiac-band-relevant system** but geomagnetic/ELF setting, not clinical cardiac source attribution |
| *Low-frequency noise characterization of high-swing multi-loop SQUIDs* (2026; https://www.sciencedirect.com/science/article/pii/S0921453426001036) | 4.15 fT/sqrtHz white; **1/f corner ~10Hz** and reported extra 0.1-10 Hz spectral terms | The white result must NOT be copied into 1 Hz and treated as measured low-frequency noise |
| *Superconducting Quantum Magnetometers for Brain Investigations* (2025; https://pmc.ncbi.nlm.nih.gov/articles/PMC12349212/) | Nominal 1.5 and 3 fT/sqrtHz flux transformer instruments | Pickup coil, mutual inductance and ambient system conditions are part of sensitivity |
| *SQUIDs in biomagnetism: a roadmap towards improved healthcare* (2016; https://doi.org/10.1088/0953-2048/29/11/113001) | Historical ~0.5 fT/sqrtHz lowest system noise; ~2 fT/sqrtHz common low-Tc MEG system | Shielded system benchmark; measured 1 Hz per-channel performance and 1000 arrays not established by number |
| *Neuromuscular Magnetic Field Measurement Based on Superconducting Bio-Sensors* (2023; https://pmc.ncbi.nlm.nih.gov/articles/PMC10535156/) | Literature table notes ~0.1 fT/sqrtHz **white noise** for IPHT magnetometer component | Component white-noise metric, NOT cardiac-band installed system |

**Two separate superconducting routes:**

1. **Low-Tc SQUID with a superconducting pickup/flux transformer**, in which a large-area field pickup, superconducting inductance/mutual coupling, SQUID flux sensitivity and room-temperature electronics set field sensitivity. White flux noise and effective area alone do not establish low-frequency magnetic sensitivity, or unlimited scaling of area (nonuniform cardiac field and ambient pickup).
2. **Cryogenic superconducting pickup arrays / multiloop geometries** where coupling area, standoff and channel placement are a genuine device-level optimisation, including superconducting Johnson/shield noise, 1/f critical-current/flux noise, shielding, vibration, cryostat costs and correlated ambient fluctuations. Modern direct-coupled/multiloop designs may avoid transformer parasitics but do not universally beat transformer-coupled SQUIDs. These are physically distinct hardware designs, not necessarily independent sensors with equal figures of merit.

**Same-source ideal range sensitivity substitution, intentionally optimistic:**
- Assumed heart: 50 pT at 0.1m, ideal r^-3 fixed-moment amplitude.
- 1000 *independent* per-channel sensors at reported ASD, infinite coherence, zero nuisance, perfect source axis, SNR threshold 5, T = [5S_B/(A(r)sqrt(1000))]^2.
- Values below are **not** experimentally demonstrated range or optimal system performance:

| Receiver ASD | 10m ideal T | 100m ideal T | 1000m ideal T |
| --- | ---: | ---: | ---: |
| 25 fT/sqrtHz (ELF measured system) | ~1.74 h | ~198 years | ~198 million years |
| 4.15 fT/sqrtHz (white multiloop only) | ~172 s | ~5.46 years | ~5.46 million years |
| 1.5 fT/sqrtHz (nominal transformer) | ~22.5 s | ~0.713 years | ~713,000 years |
| 0.5 fT/sqrtHz (historical system) | ~2.50 s | ~28.9 days | ~79,200 years |
| 0.1 fT/sqrtHz (ultra-low component white floor) | ~0.100 s | ~1.16 days | ~3,169 years |
| 0.01 fT/sqrtHz (unsupported extreme hypothesis) | ~0.001 s | ~16.7 minutes | ~31.7 years |

**Important calibration vulnerability:** benchmark source amplitude was *assumed*, not traced to an anatomically validated upper bound on cardiac magnetic moment. These are conditional detector-time calculations, not a universal no-go theorem. In fact, a stronger source moment, source-motion/gradient processing, longer baseline or different modality can alter the model. Conversely actual magnetic shielding at remote observation points, 1/f drifts, line noise and heartbeat-phase decoherence can make detection dramatically less favourable.

**Quantum/absolute-zero rule:** existing PR #701 oscillator and ground-state theorems are reused as conceptual ownership. A zero-temperature oscillator has nonzero ground energy, but its symmetrized noise is not a universal magnetic SQUID/NV noise floor, nor an assertion that 0.1 fT sensors run at 0K. Neither temperature lowering nor vacuum fluctuation suppression proves a physically usable kilometric cardiac receiver.

**P4/P5 next hard physical discriminator:** obtain source paper noise spectral curves at 0.5,1,3,10,30 Hz for each *full receiver system*, plus measured cardiac moment/source spectrum, pickup standoff, SQUID flux-transfer and noise budgets, 1/f/drift, and inter-channel covariance. Then integrate frequency-bin matched-filter information with realistic phase decorrelation and periodicity searches. Explicitly mark reported white noise vs measured 1Hz vs projected hardware. No more generic spatial-array statements should be presented as novel physics.
