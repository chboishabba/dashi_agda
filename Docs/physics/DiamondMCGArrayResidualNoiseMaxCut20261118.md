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


## 18 November: eleven-reported-scientists source audit vs undisclosed MCG receiver capability

**Repo prior art actually inspected**, not guessed:
- `Docs/roadmaps/AmyEskridgeVideoAggregationMaxCut20261117.md`, PR #1528: the source-attributed media **11** comes from the 17 April 2026 Fox list, whereas the 20 April House committee letter discusses **at least ten** cases and describes reports as **unconfirmed**. Amy's 2022 death is separate from the House letter's 2023-onward sequence. The edited video has **86 attributed claims**, not 86 independent source receipts.
- `DASHI/Culture/MissingDeceasedCommonObjectProgrammeInvestigationExact.agda`, PR #915: the retained cross-person owner has `literalCrossPersonReceiptCount = 0`, with 6 institutional/thematic adjacency receipts and multiple candidate capability hypotheses. This is an **evidence-search ledger**, not a proof that no programme exists.
- `docs/research/psychotronics-missing-scientists-physics-crosswalk-20261024.md`, PR #1242: engineering and original-science crosswalk; it specifically distinguishes Li/Torr superconducting-gravity theory, Podkletnov/Nieminen reported shielding, NASA/Quantum Machines POAMS, and standard electromagnetic/cryogenic metrology. Distinct speculative mechanisms must not be silently promoted to a demonstrated SQUID, cardiac sensing system, gravitational source enhancement or intelligence capability.

The eleven-person reporting cannot independently supply a quantitative instrument performance claim; the absence of a public technical receipt **does not** impose an upper bound on an undisclosed receiver. A maximally favourable capability hypothesis is valid as a *conditional inverse design problem*: what cardiac moment, receiver ASD, array gain and coherent integration would make a claimed range possible? No need to infer motive, secrecy or involvement of any person.

**New exact inverse-envelope checker:** `scripts/check_diamond_mcg_undisclosed_capability_inverse_steelman.py` uses exact SymPy solution of `rho = A0 (r0/r)^3 g sqrt(N T)/S`. The effective transfer factor `g` cannot be identified with independent-sensor count a second time. The 50 pT @ 0.1m amplitude, 1000 independent sensors, r^-3 static dipole, coherent SNR 5 benchmark is deliberately retained here to expose required *additional* performance—not because 50 pT is the universal strongest human cardiac moment.

Under these assumptions at `r=1000m`, the **required PER-CHANNEL equivalent ASD** is

| Fully coherent observation time | Required ASD (fT/sqrtHz), upper threshold |
| --- | ---: |
| 1 second | 3.1623e-7 |
| 1 minute | 2.4495e-6 |
| 1 hour | 1.8974e-5 |
| 1 day | 9.2952e-5 |
| 1 year (365.25 days) | ~1.776e-3 |

These are requirements, **not achieved or physical lower bounds**. Inverse source-moment constraints can be computed with `needed_A0 = rho S (r/r0)^3/[g sqrt(NT)]`. Stronger source moment, better flux coupling, different propagation or longer coherent integration change this quantitative requirement; any such claim must independently source its gain mechanism and noise floor.

### Updated high-alpha decision sequence

1. **Primary source strength:** seek maximum *measured* remote cardiac magnetic moments/spectra and geometry, with separation from source movement, metal/implant artifacts or technical fields. A powerful source mechanism changes the premise; no arbitrary upper bound is granted.
2. **Best receiver transfer:** construct SQUID/superconducting pickup flux-to-field conversion `S_B = S_Phi/|A_eff|` including mutual inductance, standoff, impedance, amplifier backaction and measured 0.5-40Hz spectra. Large loops average the source spatially and capture correlated ambient fields.
3. **Temporal information:** test whether long-term cardiac phase is usable. False-alarm-corrected periodicity detection can integrate power without a stable waveform but with a different time law; do NOT treat year-long coherence as a free receiver gain.
4. **Hypothesis discrimination:** compare a conventional public SOTA system, an engineering-extrapolated system, and an **explicit hypothetical undisclosed** capability envelope without conflating these categories.
5. **Attribution separate from detection:** a magnetically correlated periodic signal is not yet proof of a human heartbeat or identity. Hold-out spatial/spectral/human/technical negatives remain mandatory.

**Current milestone:** zero hidden-technology inference was needed to compute the inverse requirements. No empirically calibrated 1-km system or universal impossibility theorem is established. The repo source genealogy informs the evidence and owner search, not the numerical field sensitivity. P4/P5 and physical validation remain OPEN; synthetic inverse algebra alone does not close them.


## 18 November 2026 — Missing-scientists superconductivity/gravity mechanism crosswalk

The 11-person media source ledger (PR #1528) and wider original-science atlas (PR #1242) are **inspiration and source discovery**, not a quantitative receiver measurement or evidence for one secret programme. Inspected the actual current owner files:
- `DASHI/Physics/ExoticGravity/LiTorrCoupledPotentialModelExact.agda`: Li/Torr 1991/1992 theoretical coupled-potential claim `A+(m/q)Ag`, separate EM and gravito-EM response, and proposed attenuation of combined field; not proved continuum dynamics or measured transfer.
- `DASHI/Physics/ExoticGravity/SuperconductingSourceConstitutiveEvidenceBidiExact.agda`: explicit source-normalisation and phase/constitutive split, whose present evidence gate starts with source characterisation.
- `DASHI/Physics/ExoticGravity/SuperconductingGravityExperimentalConstraintRegistryExact.agda`: Podkletnov reported 0.05–0.3% weight response; NASA/Noever follow-on artefact, Hathaway 2003 null replication, Tajmar transition mismatch and large-theory constraints. Preserve individual experimental configurations; null one configuration is not a universal prohibition.
- `DASHI/Physics/ExoticGravity/LiTorrExperimentalDiscriminatorBidiExact.agda`: requires same-apparatus normal/superconducting comparisons and separate inertial/clock probes for gravity claims, rather than misidentifying EM pickup with gravity.
- `DASHI/Physics/ExoticGravity/SuperconductingGravityExperimentDesignProofSearchCrossPollinationExact.agda`: explicit hypothesis-world and observational-collision separation reusing repo-native experiment design.

**Practical magnetic-receiver steelman:** The established superconducting route is improved **electromagnetic** flux collection, low-loss transport, coupling to SQUID flux readout and source/ambient discrimination. This is independent of proving any exotic-gravity effect. We should calculate a source-to-pickup flux integral `Phi = integral_A B_heart · n dA`, then transfer `Phi_SQUID = M/(L_p+L_i) Phi` for an idealized one-loop transformer circuit, and `S_B^1/2 = S_Phi^1/2 / |dPhi_SQUID/dB|`, with actual circuit losses/noise and field nonuniformity; any factor from larger pickup area cannot simultaneously be counted as independent-channel gain. These are circuit hypotheses requiring accurate geometry, not a replacement for the empirical heart field.

**Optional independent conjectural branch:** Li/Torr `A+(m/q)Ag` and any material-dependent anomalous constitutive response would require a quantitatively identified source-to-sensor *magnetic* transfer law at the cardiac frequency, phase-on/off comparison, same-source calibration, and electromagnetic/thermal/mechanical background accounting. A purported gravitomagnetic receiver might measure a channel that ordinary MCG does not; it does not therefore amplify ordinary cardiac EM `B` or permit cancellation of the dipole range penalty for free. Do not sum EM and gravito-EM gains without a measured or model-proved common transfer coefficient and noise covariance.

**Cross-lane specific high-alpha cut:** for the same input current/field geometry, test (1) low-Tc SQUID without transformer, (2) superconducting pickup + SQUID transformer, (3) phase-cycled device (normal vs superconducting) under identical external applied calibrated fields, and (4) optional genuinely distinct external inertial/clock probe if claiming gravito-EM conversion. Require receiver `dPhi_out/dB_in`, `S_Phi(f)`, effective field ASD `S_B(f)`, `T_c`, standoff and environment at 0.5–40Hz. A phase jump alone is not an exotic-force observation because ordinary superconductivity changes flux screening and circuit transfer.

**Original sources:** Li and Torr, Phys Rev D 43 (1991), https://doi.org/10.1103/PhysRevD.43.457; Li and Torr, Phys Rev B 46 (1992), https://doi.org/10.1103/PhysRevB.46.5489; Hathaway/Cleveland/Bao, Physica C 385 (2003) 488–500; Graham et al., Physica C 468 (2008) 383–387; NASA NTRS 19990019627. Technical theories are not experimentally established superconducting gravity. The wider cohort's disappearances/deaths do not substitute for a measured physical transfer function.


## 18 November — Filsinger nonlinear countermodel against historical superconducting-gravity null regimes

**Original sources:** Hathaway, Cleveland, Bao, *Gravity modification experiment using a rotating superconducting disk and radio frequency fields*, Physica C 385 (2003) 488–500, https://www.sciencedirect.com/science/article/abs/pii/S0921453402022840; Graham et al., *Experiment to detect frame dragging in a lead superconductor*, Physica C 468 (2008), https://www.sciencedirect.com/science/article/pii/S0921453407013937; Tajmar et al., *Search for Frame-Dragging-Like Signals Close to Spinning Superconductors*, https://arxiv.org/abs/0707.3806. The Hathaway study did attempt RF excitation, so **do not misdescribe it as an unpumped control**. Its tested pump frequency/geometry, phase, material response and measured weight channel must be compared precisely against any proposed alternative. Graham's rotating lead and ring-laser frame-dragging test has a different probe and hypothesis. The Tajmar reported onset not coinciding with material superconducting `Tc` is a constraint against a simple `Tc`-locked response.

**Prior-art weld:** `Docs/research/SmithFilsingerLorentzADEMaxwellGreenMaxCut20261117.md` supplies passive Lorentz-ADE/Maxwell `E,H,P,V` model, positive material storage, pump/source/receiver separation and exactly accounted dissipation. `SmithFilsingerMidpointPhaseWorkExact.agda` supplies signed two-port source/driver/output energy accounting. Existing Li–Torr source/constitutive owners are reused without declaring an observed gravity enhancement.

**New executed SymPy checker:** `scripts/check_sc_nonlinear_gravity_receiver_steelman.py`. Local exact execution PASS; 1-km one-day reverse calculation gives amplitude improvement ~1075.83 and information improvement ~1.1574 million relative to the already optimistic 0.1 fT/sqrtHz per-channel reference, 1000 independent sensors and 50 pT @0.1m dipole. This is NOT an estimate of a material's achievable enhancement. Exact Git blob replay/Agda kernel check not claimed.

**Established nonlinear receiver lane:** Below-threshold degenerate parametric model `x''+2gamma x'+omega0²[1+h cos(2omega0 t)]x=F_signal`, with ideal rotating-wave amplified quadrature `G=gamma/(gamma-h omega0/4)` and stability `h omega0/4<gamma`. Source: SQUID pumpistor / Josephson parametric amplifier established literature, https://link.springer.com/article/10.1140/epjqt6; https://doi.org/10.1103/physrevb.89.214517. This is a model for **electromagnetic circuit amplification** (often microwave), not evidence of gravitational amplification or cardiac-frequency sensor advantage. Pump power is an external source and must be paid; no free work from zero-point energy.

**Noise-gain accounting:** `y=G(s+n_input)+n_readout` implies `I(G)=G²s²/(G²N_input+N_readout)` and `lim_(G→∞) I(G)=s²/N_input`. Therefore a pumped gain cannot improve input-limited SNR; it can at most suppress downstream readout-noise penalty. Any physically distinct source conversion or noise-squeezing improvement must be documented separately and include added/backaction/idler/pump-correlated noise. Filsinger exact work accounting remains required.

**Exploratory gravity-specific *conditional* alternative:** To discriminate a nonlinear response from a tested null, introduce *unfitted* dimensionless `eta=1+alpha*coherence*[d²/(1+d²)]*[linewidth²/(linewidth²+detuning²)]*cos(phase)`. It reduces to ordinary response for zero drive, zero coherent phase fraction or phase quadrature, and can have nonzero residual only with separately proven nonzero `alpha`, matched pump, source, temperature and calibrated external gravitational probe. This formula is only an algebraic counterexample to overbroad extrapolation of experiment scope—not a derivation from Li–Torr, not evidence the historical runs lacked relevant RF, and not a reproduction of measured values. Strong positive coefficients/energy-to-gravity coupling are not established.

**Reproduction status:** Original Hathaway/Graham/Tajmar raw histories (pump timing, absolute geometry transfer, temperature, run-matched controls, uncertainties and per-sample measurements) have NOT been acquired, so their published null statistics cannot be independently recomputed. It is possible to reproduce the *logical scope* and construct exact limiting countermodels, but NOT to state that their actual observed nulls have been numerically reproduced or explained. This gate stays open.

**Meaningful next cut:** same-geometry normal/superconducting phase sweeps; pump frequency/amplitude/relative phase controls; source-normalised EM and separately inertial channels; subthreshold bandwidth/gain/nonlinearity/noise-plus-idler plus parametric near-instability calibration; true cardiac-band receiver `S_B(f)` measurements and adaptive pump noise. Determine whether any observed excess is simply readout gain, changed magnetic field source, constitutive response, or gravity-channel residual. Optimize the strongest physically viable receiver rather than maximizing arbitrary `alpha`.


## Original-regime replication and nonlinear receiver steelman — 18 November

**Priority change:** the material's nonlinear/phase-dependent susceptibility and an advanced *frequency-converting* receiver are two different research hypotheses. A powered nonlinear frontend may shift the cardiac signal away from downstream low-frequency 1/f readout noise, but does not improve the information available above the **input-referred noise** floor merely by boosting gain. Gravity-channel coupling remains a separate, speculative, experimentally unpaid proposal.

### Original-source observation/geometry audit

1. **Hathaway, Cleveland & Bao, Physica C 385 (2003) 488–500**, original full text at https://www.naturalphilosophy.org/pdf/abstracts/abstracts_paperlink_7351.pdf (journal DOI/PII https://www.sciencedirect.com/science/article/pii/S0921453402022840). Reported weight repeatability **0.001%**, 50-fold beneath 1992 0.05% minimum claim. They actually used three-phase RF (mostly **4–5 MHz**, 100 kHz levitation coils), YBCO/Pr123 disks and clockwise mechanical rotation typically ~400 rpm with maximum ~550 rpm. The phase order of RF drive was occasionally reversed, but **disk rotation never reversed**. They failed to obtain the specified free AC levitation at 100 kHz, used mechanically supported spin and suffered mechanical vibration/drag at high RF power. Their paper directly identifies **1000–2000 rpm**, both mechanical rotation senses, stronger levitation, flux trapped on cooldown, and the effect of RF phase/direction relative to spin as unresolved. This is a *measured-domain gap*, **not** evidence of positive weight loss there. The published Figure 11 includes n=10 group means/std deviations, but its separated configurations/time intervals do not license fake matched-pair significance.
2. **Graham, Hurst, Thirkettle, Rowe & Butler, Physica C 468 (2008)**, original Canterbury preprint https://www2.phys.canterbury.ac.nz/~physrin/papers/SuperFrameDragging2007.pdf and journal https://www.sciencedirect.com/science/article/pii/S0921453407013937. UG-2 ring laser area **833.7m²**; spinning lead at ~4.22 K; rotor CW 15 rps and CCW 12 rps; ~17.5 m separation from the closest ring-laser corner. They evaluated a **London-like gravitomagnetic field proportional to angular velocity**, `B_g* = 2 omega rho*/rho`, whose predicted field and Sagnac transfer yield `Delta f = 4.65e-5 omega Hz`. Expected shifts **4.38mHz CW** and **3.51mHz CCW**; observed source-fit slope **(2.3±1.4)e-6 cycles/rad** vs predicted **4.8e-5 cycles/rad**. Predicted/best-fit ratio **20.87**, not a 95% upper limit: with a naive Gaussian two-sided 95% upper on source SE, the ratio is **9.52**. The published journal abstract describes ≥95% detection probability for the original theory. Source-linked falsification pertains to velocity-proportional distant frame dragging, *not* every acceleration-triggered effect, although novel mechanisms require independent derivation and data. The authors report geophysical microseismic noise and a 33.3mHz low-pass filter; raw traces have not been replayed.
3. **Tajmar et al**, arXiv:0707.3806, https://arxiv.org/abs/0707.3806. The authors report a cold-temperature onset **not equal to the tested material's superconducting Tc** and a much stronger gyro response for clockwise direction. Their accelerometer (angular-acceleration-sensitive response) and gyro (angular-velocity-sensitive response) must be kept distinct; a pure superconducting phase-transition model is insufficient if its signal appears in non-transition regimes. `onset!=Tc` is an observed paper-level condition, **not** a measured temperature numerical replay here. Alternative smooth cold-fluid, mechanical or material-temperature effects are equally candidate explanatory worlds until matched controls discriminate. Do not claim they established gravity.

### New checked mathematical controls

- `scripts/check_superconducting_gravity_historical_regimes_exact.py`: **exact SymPy equivalent executed locally PASS** for Hathaway 50-fold published-sensitivity comparison and untested CW/CCW 1000–2000 rpm regime; Graham source-published predicted/fit slope and Gaussian interval arithmetic; and logically separate acceleration/rate/temperature gates. The synthetic CCW-only high-speed threshold is *only a counterexample to the universal extrapolation of a tested null*, **not an inferred physical law**. Exact committed Git blob has not been replayed independently.
- `scripts/check_sc_upconversion_input_noise_steelman.py`: **exact SymPy equivalent executed locally PASS**, source algebra for linear pump gain and early frequency conversion. If `y=G(s+n_in)+n_read`, information saturates to `s²/n_in`. For ideal transfer `eta` to a high-frequency sideband before downstream LF readout noise, information is `eta² s²/[eta² n_in + n_side+n_pump]`. This can materially beat a low-frequency frontend dominated by downstream `1/f`; it does NOT alter true input magnetic source/environmental noise. Source models must include nonreciprocal isolation, idler and pump-added noise and energy, and the Filsinger signed port ledger.
- An extra **1076× amplitude sensitivity** relative to the already assumed 0.1fT/sqrtHz/1000-channel/one-day/50pT@0.1m 1km hypothetical benchmark requires **1,157,776× information**. If the baseline input-referred irreducible noise contributes >`1/1,157,776` of *baseline total* noise power, that same source + passive transfer + readout-gain-only construction cannot reach the goal even with infinite noiseless downstream gain. The inverse statement makes clear a **large improvement is not mathematically impossible**, but it must attack the dominant noise stage or source/transfer, rather than count pump voltage gain as new source information.
- Constructive gain-budget candidate branches (NOT instrument facts): (A) superconducting pickup response/effective source coupling `g_s`, (B) input-referred field noise suppression `g_n`, (C) actual independent source-mode/receiver coverage `g_N`, (D) demonstrably valid coherent/semicoherent time gain `g_T`. Required product `g_s g_n sqrt(g_N) sqrt(g_T) >=1076` for the specific baseline. Require *causal single-sensor source/field equality* and Filsinger pump/output work to prevent double-counting gain.
- Experimental follow-up to Hathaway without pretending bench access: preregister `{rpm=400,550,1000,1500,2000} × {CW,CCW} × {phase RF CW,CCW,OFF} × {normal,YBCO} × {cooldown trapped flux low,high}`, collect independently calibrated weight, external gyro, magnetic field, RPM, torque/vibration, RF current/phase, temperature and full waveform. Treat unsafe 2000rpm cryogenic rotor mechanical containment and high RF voltages as specialist lab engineering, not an instruction to build an uncontained rig. Expected absence or presence under a new nonlinear model is contingent on actual parameter identification.
- Graham/Tajmar discriminators: same rotor/geometry compare velocity-proportional plateau to acceleration-edge transient, normal/superconducting phase state, both directions, gyro and isolated test-mass channels and phase-referenced / deliberately detuned pump; unfiltered time histories and held-out baselines needed. Avoid conflating rotation-direction effects with biological MCG sensor sensitivity.

**Important boundary:** the user goal is a maximally capable physically honest steelman. Hypothetical undisclosed receiver capabilities are not bounded by public specification sheets; equally, an unobserved nonlinear gravity effect or a historically reported personal disappearance does not instantiate an unknown instrument. The current work tests **source-defined null domains and mechanisms**, not a mechanism for enhancing all cardiac magnetism.

Next high-alpha construction: frequency-domain Maxwell + nonlinear superconducting susceptibility with a **measured 0.5-40Hz input magnetic source** and pump-sideband frequency conversion, including photon/flux added noise, idler correlations, bandwidth and noise-equivalent field. This is distinguishable from routine gradiometry and solves a specifically identified capability bottleneck.


### Gain-bandwidth negative control (same round)
The ideal below-threshold, one-quadrature, single-pole parametric model `G=gamma/(gamma-k)` has amplified-quadrature linewidth `b=gamma-k`, hence exact `G*b=gamma`. An amplitude *voltage* gain of 1076 in this isolated model narrows the linewidth to **1/1076** of the unpumped linewidth. This is not a general theorem limiting all nonlinear sensing schemes: a physically separate broadband upconverter, cascaded engineering, multimode receiver or genuine source enhancement requires its own noise/bandwidth/power audit. At cardiac frequencies, a high-gain single-pole point solution cannot be promoted to broadband/variable-heartbeat detectability without checking the sidebands and tracking. Exact symbolic identity checked locally; committed checker extended.


## Physical-SI, nonlinear high-speed regime, Tajmar split and narrowband RQU — 18 Nov 2026

**This supersedes the previous *arbitrary* RPM switch toy**. Do not promote a hard-coded `>550rpm` anomalous switch as a physically justified mechanism.

**Checked original papers:** Hathaway et al., Physica C 385 (2003) 488–500, https://www.sciencedirect.com/science/article/pii/S0921453402022840 (full copy https://www.naturalphilosophy.org/pdf/abstracts/abstracts_paperlink_7351.pdf); Graham et al., Physica C 468 (2008), https://www.sciencedirect.com/science/article/pii/S0921453407013937; Tajmar et al., arXiv:0707.3806 https://arxiv.org/pdf/0707.3806; 2025 `RF Quantum Upconverter` Phys Rev Research 7, 013281 DOI https://doi.org/10.1103/PhysRevResearch.7.013281.

**Repo-native typed experiment:** `DASHI/Physics/QuantumSensors/SuperconductingRotorSIExperimentRegimeExact.agda` imports the existing `DASHI.Physics.Units.SI` and constructs angular velocity (frequency), angular acceleration (time^-2), moment of inertia (kg m²), plus synchronized **measured** rotor angular velocity/acceleration, temperature, Tc, RF power/frequency, trapped flux, geometry, external force and magnetic field, and source/calibration strings. It separates weight, gyro, accelerometer and magnetic outputs as distinct constructors; matched-world experimental receipts require geometry/calibration/source-work/nuisance witnesses. Agda **not kernel checked**. These records make dimensions and measurement needs explicit; they do not prove gravity dynamics.

**Exact SymPy physical-mechanics lane**, `scripts/check_sc_rotor_filsinger_physical.py` local mathematical match PASS: `omega = 2*pi*rpm/60` s^-1; characteristic rotating-ring stress `sigma~rho*R²*omega²` Pa; `E_kin=I*omega²/2` J and `dE/dt=I omega alpha` W; damped Lorentz-ADE `|chi(w)|²=kappa²/[(w0²-w²)²+4gamma²w²]`. Signed odd `omega` and even `omega²` response channels distinguish mechanical rotation direction. Superconducting material gate is an illustrative *smooth* `1-(T/Tc)²` factor only for T<Tc, gated by measured trapped flux; it is **not a measured YBCO response law** or empirical explanation of gyro onset.

**Nontrivial high-RPM feasibility inequality (conditional):** If a matched original experimental configuration is constrained by a hard effect envelope of **≤0.001% at 550rpm**, then a fixed `omega²` model can grow only by `(2000/550)² = 1600/121 ≈ 13.22`, giving **≤0.0132%** at 2000rpm. This is below original Podkletnov/Nieminen 0.05%. A second-order nonlinear response to the same rotation-stress coordinate yields `omega^4`, with `(2000/550)^4 = 2560000/14641 ≈174.85`, so a constant coefficient can yield **0.05% at 2000rpm while remaining below 0.001% at 550rpm**. The source power, flux, temperature, RF phase and geometry must be matched. This is a genuine algebraic *compatibility construction* consistent with classical stress units, NOT a demonstrated external gravity coupling. Ordinary mechanical/EM rectification can have the same exponent.

**Graham distinct response channels:** `scripts/check_sc_graham_angular_acceleration_dynamics.py` locally checked exact 2-pole transfer `H(s)=1/[(1+s*tau_x)(1+s*tau_f)]`; acceleration-edge response is the difference of decaying exponentials, and asymptotes to zero on a constant-speed plateau. `tau_f≈4.78s` corresponds to a **hypothetical single-pole** filter with the paper's 33.3mHz cutoff, NOT the paper's actual filter replay. The already-failed Graham prediction was a **velocity-proportional persistent** Sagnac slope. A separate acceleration transient can be consistent with its fitted plateau/null in principle, but its actual response under their spin-up/spin-down cycles is NOT established without the raw time histories and exact filter. Source kappa remains constrained; speculative transient gain lambda needs independent identification.

**Tajmar nuance correction:** `scripts/check_tajmar_phase_onset_observable_split_exact.py` locally sourced/matched symbolic control distinguishes Fig 4 **niobium accelerometer contrast** across 4.5–6.5K vs 10–14K, published magnitude ratios 2.26e-8 and 1.24e-9 (~18.23×), from the **laser gyro onset** of about 16K for Nb/Al and about 32K for YBCO, which are *not their superconducting Tcs*. The primary authors also discuss aluminum sample-holder contributions, vibration subtraction, and the possibility that their signals are systematics. **It is wrong to erase the published Nb superconducting-versus-normal contrast simply because the gyro onset is not at Tc**; it is equally wrong to claim the contrast proves gravity. Both observations stand as author-reported experimental data requiring source-probe calibration.

**Heartbeat bandwidth correction:** `scripts/check_sc_heartbeat_narrowband_tracker_exact.py` PASS, mathematical model `G*BW=BW0`: with peak gain 1076, initial 100Hz bandwidth gives **0.093Hz** signal band; initial 10kHz gives **9.29Hz**. A tracked heartbeat fundamental occupies a narrow band, unlike ECG morphology; the relevant condition is **bandwidth/tracking/source frequency drift per coherent segment**, not a generic requirement to preserve 0.5–40Hz waveform. For `f(t)=f0+fdot*t`, mismatch phase `pi*fdot*T²`; one-radian drift for T=86400s needs `|fdot|<4.26e-11Hz/s`, a strict demand for *untracked* day coherence, not a limit on tracking/semicoherent detection. A power/phase/timebase budget is required to track and combine beats; a 1Hz carrier itself does not guarantee arbitrarily long phase coherence.

**Real nonlinear superconducting metrology donor:** Kuenstner, van Assendelft, Chaudhuri, et al. *Quantum metrology of low-frequency electromagnetic modes with frequency upconverters*, Phys Rev Research 7 013281 (2025), https://doi.org/10.1103/PhysRevResearch.7.013281. Authors demonstrate superconducting Josephson-loop upconversion of dc–VHF electromagnetic signal to approximately 5GHz microwave mode, and phase-sensitive extinction **46.9 dB**. This is a *measured frequency-conversion experimental result*, **not** 46.9dB of equivalent cardiac magnetic amplitude-sensitivity gain. It discusses quantum-limited/op-amp and backaction-evading approaches, with actual metrological noise performance requiring separate device-specific receipts.

**Actual source-to-flux receiver owner**, `scripts/check_sc_pumped_flux_transfer_exact.py` local SymPy PASS, uses SI signatures `T kg/(A s²)`, `Wb=T*m²`, `H=Wb/A`, measured circuit symbols `Phi_in=B*A_p`, `I_p=Phi_in/(L_p+L_i)`, `Phi_SQUID=M*I_p`, `chi_B=M*A_p/(L_p+L_i)`. With superconducting upconverter transfer `eta` and amplifier voltage gain `G`, input field PSD `S_B,in`, intrinsic flux PSD `S_Phi`, downstream readout and pump PSDs, the **derived exact input-referred noise PSD** is:
```
S_B,eq = S_B,in + S_Phi/chi_B²
        + (S_read+S_pump)/(G² eta² chi_B²).
```
Unlike gain-only arguments, this makes exact improvements falsifiable and shows the irreducible magnetic/flux noise floors. The symbolic `A_p → ∞` limit ignores `L_p(A_p)`, spatial averaging, cryostat, ambient flux and environmental correlated noise and is specifically NOT a physical pickup gain claim. Full Filsinger source/pump and dissipation payment remains required.

**Scope receipts:** local matching exact SymPy tests PASS for rotor/omega⁴, Graham ideal transfer, Tajmar separate observable statements, cardiac chirp/linewidth, and SI-source-to-flux input-equivalent PSD. GitHub source files committed; no full exact-blob-replay, Agda kernel or CI acceptance claimed; no physical rotor experiment run, no fabricated measurement. Source parameter comparisons are not a new gravitational-force observation.

**Next highest-alpha:** constrain stress-to-response coefficient and nonlinear susceptibility from *actual superconducting rotor and flux-loop measurements*; test bidirectional high-speed rotor regimes in a professional contained cryogenic lab, matched RF relative phase and initial trapped flux, normal/SC controls; fit source-normalized external EM vs independent inertial/clock probes; compare two-port pump power with any readout improvement. Then perform measured 0.5–10Hz RQU input-referred PSD tests with a cardiac-like calibrated magnetic source and validated tracking. These gates are physical/empirical, not missing algebra.


## 18 November — Filsinger HF capacitors + low-frequency cardiac input + nonlinear superconducting readout

**Question clarified:** Previous `omega^4` (Hathaway) involved a *mechanically spinning YBCO disk*, with stress `rho R² omega²`; a heart is **not a mechanically rotating superconducting disk**. A heart has traveling activation/current dipoles and can be approximated in a deliberately limited fixture by a *time-rotating equivalent magnetic dipole*. Its magnetic field rotates as a vector while remaining dipole-decaying as `1/r³`. These are different angular-velocity coordinates with separate measurements and source laws.

**Existing exact owner first, no new capacitor ontology:** `Docs/research/SmithFilsingerDispersiveSourceResponseMaxCut20261115.md` and `Docs/physics/PVAtomic369RFDrivenMaxCut20261116.md` already derive `q(V)=C0 V+alpha V³`, `U(V)=C0 V²/2+3alpha V⁴/4`, and exact modulator/source work. `Docs/research/FilsingerZVSShuntAcousticMicrovariationMaxCut20261110.md` documents the candidate 1 Mohm shunts and ~3.3uF capacitors, acoustic ~7.8kHz (NOT measured electrical pump). `Docs/research/SmithFilsingerNonlinearRetardedSourcePortMaxCut20261117.md` and `SmithFilsingerLorentzADEMaxwellGreenMaxCut20261117.md` give causal finite Debye/Lorentz response, external pump work, dissipated work and source restoration. None establishes Josephson, SQUID or cardiac physics for the original Filsinger device. The **mathematical nonlinear mixer idea is portable**, not the original claimed apparatus as a real superconducting receiver.

**New verified symbolics:** `scripts/check_mcg_filsinger_hf_cap_mixer.py` (source-equivalent SymPy locally executed PASS; committed exact Git-blob replay not run). Write `V(t)=Vb+Vp cos(Omega t)+vs cos(omega_c t)`, with small `vs`. Linearize the *charge* signal in `vs`:
```
dq/dV at pump =
   [C0 + 3alpha Vb² + (3/2)alpha Vp²]
 + [6alpha Vb Vp] cos(Omega t)
 + [(3/2)alpha Vp²] cos(2Omega t).
```
Therefore `q_signal ≈ (dq/dV)_pump vs cos(omega_c t)`, and mixed charge sidebands `Omega±omega_c` each have amplitude `3alpha Vb Vp vs`; `2Omega±omega_c` each have amplitude `(3/4)alpha Vp² vs`, including zero bias. It is the derivative `i=dq/dt` that supplies the sideband **current**, with pump frequency dependence and circuit matching needed to measure it. The energy ledger `v dq = d(0.5 C(t)v²)+0.5 v² dC(t)` for a modulated linear capacitance and the original cubic `U` identity keeps modulation work **separate from the cardiac source**. Filsinger charge nonlinearity alone does NOT supply a calibrated magnetic transduction `vs/B`; the SQUID flux transformer and Josephson pump must supply actual transfer.

**Rotating equivalent cardiac source** `scripts/check_mcg_rotating_heart_polarization.py` locally exact SymPy PASS: choose `m(t)=m0(cos omega_c t, sin omega_c t,0)`; for look vector `z`, `B(t)=-mu0*m(t)/(4pi r³)`. A phase-tracked co-rotating transverse analyzer produces constant demodulated amplitude `-mu0*m0/(4pi r³)`, while a counter-rotating analyzer yields a `2omega_c` residual. This is a *point-dipole polarization fixture*, not an anatomically sourced heart model, a new mechanism for increasing the original field or a gravitational interaction. The vector orientation may vary over the cardiac cycle, but physiological source trajectory cannot be inferred from a synthetic circular trajectory.

**Input noise retains rigorous ceiling:** use existing pickup `chi_B=M A_p/(L_p+L_i)` and IF/readout responsivity `R` with a pump: `S_out=R²(chi_B² S_B,input+S_Phi+S_pump)+S_down`; exact `S_B,eq=S_B,input+(S_Phi+S_pump)/chi_B²+S_down/(R² chi_B²)`. Field-equivalent input and flux noise remain; readout power gain does **not** create source SNR. Improvement can be real if the original device is downstream-noise-limited and the HF conversion shifts the output to a quieter band. A nonlinear capacitor sideband does not prove gain or beat measured 1Hz SQUID floor.

**Quantum/atomic donors:** `DASHI/Physics/QuantumVacuum/ZeroPointModeHyperfabricExact.agda` distinguishes ground and excitation, `DASHI/Physics/QuantumVacuum/ZeroPointExtractionFirewallExact.agda` prohibits assuming free ground-state work, `DASHI/Physics/QuantumSensors/NVSIMetrologyReadoutAdapterExact.agda` owns SI metrology; neither is the real Josephson-junction Hamiltonian. Cryogenic hardware comparisons must use actual equilibrium occupation, Josephson/flux susceptibility, measured flux noise and quantum readout added noise rather than subtracting a fictitious zero-point PSD constant.

**External primary physics donors:** S. E. Kuenstner et al., *Quantum metrology of low-frequency electromagnetic modes with frequency upconverters*, *Physical Review Research* 7 013281 (2025), https://doi.org/10.1103/PhysRevResearch.7.013281 ; `Dispersive magnetometry with a quantum limited SQUID parametric amplifier`, *Phys Rev B* 83, 134501 (2011), https://doi.org/10.1103/PhysRevB.83.134501 (tradeoff 0.29 microPhi0/sqrtHz at 20MHz bandwidth vs 0.14 microPhi0/sqrtHz at 0.6MHz); the 2026 APS RQU bias-controlled noise suppression talk https://meetings-archive.aps.org/smt/2026/mar-g18/7/ is a conference abstract, not a cardiac sensitivity demonstration. Review of HTS SQUIDs, *Rev Mod Phys* 71, 631, https://doi.org/10.1103/RevModPhys.71.631, reports 10fT/sqrtHz white becoming ~30fT/sqrtHz at 1Hz; frequencies and subsystem conditions matter.

**High-alpha next measured weld:** quantify `B_heart -> Phi_pickup -> nonlinear flux/charge mixing -> high-frequency sideband current/voltage -> noise PSD at carrier±heartbeat`, under fixed total pump/readout power, transfer and temperature, and measured source coherence. Obtain source harmonics and actual quantum circuit Josephson parameters to distinguish phase-sensitive improvement, spin/flux quantum readout and pump added noise. Avoid claiming the source physically rotates at one constant frequency or that Filsinger capacitors are SQUIDs. Both original-world and secret-hardware capability assertions remain unsupported without further evidence.


## 18 Nov: Why original YBCO rpm was low; entangled multi-MCG receiver steelman

**Attribution:** G. Hathaway, B. Cleveland and Y. Bao, *Physica C* 385 (2003) 488–500, original full text https://www.naturalphilosophy.org/pdf/abstracts/abstracts_paperlink_7351.pdf, are responsible for the rotor design, negative weight observations and mechanical limits. The 1997 high-RPM regime is an **authored experimental claim by E. Podkletnov**, not a demonstrated replicated effect. The user-origin hypothetical nonlinear/entangled MCG steelman is distinct from those publications and the new SymPy/QFI algebra below is a separately attributed conditional derivation.

### Actual low-speed selection and regime mismatch

Hathaway original paper §§2.1, 2.2, 3–4: large-grain sintered YBCO disks shattered in some spin tests at about **1300 rpm**; reported hoop stress approximately **0.5 MPa**, indicative of weak granular disks. Their later 160mm bilayer disks had cryogenic bearings/gears that vibrated, typical test around **400rpm** and hard maximum **~550rpm**. One description reports 400–800rpm mechanical drive, but the *actual experimental-results* section says ~550rpm maximum. Three-phase 4–5 MHz RF power produced **drag**, reducing/stalling disk rotation around 200W/phase. Sufficient 100kHz AC Meissner levitation was not achieved, hence external mechanical drive and no rotation reversal. Authors recommend **1000–2000rpm** and both mechanical directions; an alternative 1997 Podkletnov manuscript claims ~5000rpm. This was **not a theoretically optimal speed choice**: it was apparatus material strength, drag, levitation and drive limitations.

**New verified source-bounded quantitative fixture** `scripts/check_ybco_rpm_entangled_mcg.py` executes SymPy PASS locally, with exact `sigma(rpm)=0.5MPa*(rpm/1300)^2` **only if material, radius and stress geometry remain identical**. Conditional stress estimates at 550/1300/2000/5000rpm: 0.0895/0.5/1.1834/7.3964MPa. These are *extrapolated stresses*, not actual high-speed disk measurements or demonstrations of safe containment. Different grain structures, reinforcement and motors change the physical apparatus and may change any speculative constituent response. The larger alleged 1997 weight effect and its apparatus cannot be silently merged with the 1992 0.05–0.3% report. The original 2003 weight null remains a meaningful constraint on its actual tested regime, not a global suppression proof.

### Multiple entangled cardiac magnetic sensors: real research donors

**Original sources and claims belong to original experimenters**:
- 2026 *Nature Communications*, *Distributed multi-parameter quantum metrology with a superconducting quantum network* https://www.nature.com/articles/s41467-026-68535-9 : distributed **four-qubit GHZ** state across superconducting sensor modules enables spatial gradient-vector estimation. Demonstration of quantum distributed metrology, **NOT an entangled 4-channel MCG recorder or human cardiac detection**.
- 2025 *Physical Review Letters*, *Experimental Distributed Quantum Sensing in a Noisy Environment* https://pubmed.ncbi.nlm.nih.gov/41385659/ : entangled sensing can separate a field signal from some nuisance spatial profiles over micron-scale demonstrated sensor separation; statements about arbitrary distances concern potential generalisation, not human-heart metrology already demonstrated.
- 2022 *Nature*, *Distributed quantum sensing with mode-entangled spin-squeezed atomic states* https://www.nature.com/articles/s41586-022-05363-z : experimentally reports up to 4.5dB better precision than no distributed entanglement and 11.6dB vs quantum projection limit. Distinct source, sensor technology and denominators.
- 2025 *Nature Physics*, *Concurrent spin squeezing and field tracking with machine learning* https://www.nature.com/articles/s41567-025-02855-3 : continuous quantum enhancement and tracking time-varying magnetic fields, not measured SQUID MCG.
- 2026 *Physical Review Letters*, *Correlated Noise Estimation with Quantum Sensor Networks* https://journals.aps.org/prl/abstract/10.1103/sl32-jn82 : theory of entanglement advantage for collective stochastic parameters, not direct proof of an MCG amplitude advantage.
- 2025 *Nature*, *Multi-qubit nanoscale sensing with entanglement as a resource* https://www.nature.com/articles/s41586-025-09760-y : quantum-enhanced NV sensing, not a demonstrated heart-scale entangled cryogenic network.

**Core resource-matched quantum Fisher information steelman** (normalized generator `H=(b/2) sum sigma_z`, exact ideal probes, equal coupling, no dead-time): independent sensors `F_Q=N t² exp(-2gamma t)`; GHZ `F_Q=N² t² exp[-2(N gamma+N² gamma_common)t]`. In the noise-free fixed-`t` limit, GHZ/independent **information** ratio `N`, hence ideal **amplitude** sensitivity gain `sqrt(N)` relative to product states; for N=1000 `sqrt(1000)=31.62`, not 1076. GHZ `N` enhanced phase accumulation should **not** be presented as `N` sensitivity gain over a same-resource ensemble (the reference ensemble already gains sqrt N).

**Important steelman/negative result**: with independent Markovian phase noise `gamma>0`, optimize interrogation time for equal **total laboratory observation time**, using QFI rate `F_Q/t`. Product optimum `t_p=1/(2gamma)`; GHZ optimum `t_g=1/(2N gamma)`; **optimized QFI rates are identical**. With additional common noise `gamma_common>0`, optimal GHZ rate/product rate = `gamma/(gamma+N gamma_common)` in this particular model; entangling all channels can actually do *worse*. Exact SymPy identities PASS. This is a **model-specific limit**, not a universal theorem against entangled MCG, error correction, decoherence-free subspaces, non-Markovian sensing or quantum-enhanced continuous tracking.

**Spatial signal profiles/attribution:** uniform GHZ coupling responds to `sum_i g_i`; for opposite-sign magnetic contributions it can be identically blind. A sign-configured GHZ gradient protocol responds to `sum_i s_i g_i` with distinct nuisance rejection. It is only useful when the actual cardiac field spatial mode is retained and dominant correlated ambient field modes are rejected; no demonstration that a coherent 1000-sensor GHZ state survives cryogenic wiring, distance, 1Hz measurement and common noise. Quantum enhancement applies when quantum probes are entangled **before measurement**. Classically cross-correlating outputs from independent SQUIDs is useful but not quantum entanglement, and digitally combining already-measured channels cannot recover lost quantum coherence.

**Interpretation for original 1km steelman:** Even the ideal noise-free *same-interrogation-time* 1000-channel GHZ advantage over product-state sensing is only 31.6× in amplitude, leaving a further ~34× amplitude factor of the previously estimated 1076× additional gain, before decoherence/cost and without claiming that reference 0.1fT/√Hz SQUID noise was quantum projection-limited. If reference SQUID channels are technically or environmentally limited, entanglement advantage may be negligible. Conversely purpose-built differential GHZ/squeezed-state and protected subspaces can change the appropriate error model and should be tested as distinct, sourced hypotheses.

**Next high-alpha:** derive measured/proposed Hamiltonians, flux-noise and quantum Fisher information for a superconducting SQUID/Josephson network and compare *same* area, photon/cooling/pump budget, sensing time and magnetic field spatial kernel. Optimize entangled partitions/sign patterns rather than automatically create a 1000-site GHZ; include loss/dephasing, spatially correlated noise, realistic cardiac drift and local false alarms. Absent concrete qubit coherence or interface values, do not infer system performance from published small-network results. Source-to-SQUID flux and Filsinger driven-mixer work remain prior owners.


## 18 November — Physics-first high-RPM levitated REBCO/YBCO source steelman: original paper's SIX RPM data and new dynamical split

**Original attribution and original measurements, NOT our discoveries:**
- E. E. Podkletnov, *Weak gravitation shielding properties of composite bulk YBa2Cu3O7-x superconductor below 70 K under e.m. field*, arXiv:cond-mat/9701074v3 (1997), https://arxiv.org/pdf/cond-mat/9701074 , §6, pp 8–10. The author *reported* a 0.05–0.07% stationary effect, at **2 MHz constant RF** the exact six RPM/weight-loss (%) pairs `4000/.17,4200/.19,4400/.20,4600/.21,4800/.22,5000/.23`; at 4300 RPM another *distinct* RF-frequency table `3.1/.22,3.2/.23,3.3/.24,3.4/.26,3.5/.29,3.6/.32`; and up to 1.9–2.1% only **during RF-driven braking from ~5000 toward ~3500 RPM over 25–30s**, with reported optimum RF ~3.2–3.8 MHz and levitation height 30–35mm. Do NOT combine these as measurements of one constant source condition. Reported observations are not independently demonstrated gravitational effects.
- G. Hathaway, B. Cleveland, Y. Bao, *Physica C* 385 (2003) 488–500, https://www.sciencedirect.com/science/article/pii/S0921453402022840 and https://www.naturalphilosophy.org/pdf/abstracts/abstracts_paperlink_7351.pdf. Their observed ~550RPM mechanical maximum, disk fractures near 1300RPM (~0.5MPa estimated stress) and failed free-AC levitation explain limits, not a theoretically optimal RPM.
- D. Noever, R. Koczor, R. Robertson, AIAA-98-3139, NASA NTRS https://ntrs.nasa.gov/citations/19990019627 : **already present in repo** `DASHI/Physics/ExoticGravity/NingLiYBCORotatingFieldConstraintExact.agda`. Rotating **magnetic field** rates to 12,000 RPM reported and no effect, but **rotating drive field != actual mechanically rotating disk**. This is a valuable configuration-specific negative control, not a duplicate rotor proof.

**New exactly checked source-table reconstruction:** `scripts/check_podkletnov_rpm_physics_steelman.py` uses exact `Fraction` six-row regression and SymPy. At fixed **2 MHz** alone:
```
Reported percent weight change y = rpm / 17500 - 113/2100
R² = 48/49 ≈ 0.97959
```
This *descriptive line*, not a validated physical law, extrapolates to **6191.7 RPM for 0.3%**, **35941.7 RPM for 2%**, which is **not** a causal prediction: the 2% transient was at different RF, changed levitation/drive/braking and perhaps different material state. The 2% data cannot be forced to obey the same steady `y(rpm)` law. Identifiability of `y=f(omega, domega/dt, B, fRF, T, h, Jc, pinning, geometry, time)` is **OPEN**; one curve is not a global optimization landscape.

The 1500-rpm decrease over 25–30s corresponds, conditional on the reported endpoints being the same interval, to average magnitude angular deceleration `5pi/3` to `2pi` rad/s². Subtracting the 0.23% *different-regime* steady response from the 2% transient generates a purely **phenomenological** 1.77 percentage-point residual; a linear acceleration coefficient of ~0.282–0.338 percentage points/(rad/s²) could fit it **by assumption**. No signed acceleration history or source-state calibration was supplied, so this must not be presented as a verified constitutive parameter, gravity mechanism, or prediction.

**Conventional gravity scale first:** A deliberately generous thin-ring illustration with disk `m=0.8 kg`, `R=0.1375m`, `omega=5000rpm`, `z=0.1m` has `Erot ≈ 2073 J`, effective mass `Erot/c² ≈ 2.3e-14kg`, and Newtonian source-to-test-mass acceleration fraction `G(Erot/c²)/(z² g_earth) ≈ 1.57e-23`. This is only a **kinetic-energy gravity order of magnitude**, not the full GR stress-energy tensor solution, not a universal upper bound, and not a statement about unknown constitutive effects. It does demonstrate that percent-level weight changes do **not** follow from ordinary rotational energy gravitation alone. One must derive or independently measure a different physical coupling/source rather than posit arbitrary RPM amplification.

**Physical drive and Filsinger source ledger:** `scripts/check_sc_rotating_flux_drive_energy.py` gives an exact finite RL rotating-flux model `Phi(theta,t)=Phi0 cos(p theta - omega_RF t)`; `L dI/dt + R I = -dPhi/dt`, with signed mechanical and pump powers `P_mech = -I partial_theta Phi * omega_mech`, `P_pump = -I partial_t Phi`. Exact balance:
```
 d(L I²/2)/dt + R I² = P_mech + P_RF_pump.
```
At 5000rpm physical spin is ~83.3Hz and reported preferred RF ~3.5MHz, **42,000× faster**. An inferred rotor/RF resonance is unjustified without a nontrivial harmonic, vortex or envelope-mediated conversion law. This is a finite circuit surrogate, not a flux-flow/GL/TDGL solution or gravitation equation. Filsinger signed source-work formalism is reused; pump work is not an unexplained gain.

**Levitate? YES for removing bearings, NO for removing hoop stress.** The strongest design now separates a *levitated load-bearing rotor* from *bulk REBCO as levitation bearing*, and distinguishes a strengthened composite rotating YBCO sample from a superconducting bearing with a normal structural rotor. Modern concrete technology donors:
- Li et al., *Optimizing superconducting magnetic bearings ... 3D H-phi formulation*, *Cryogenics* (2024), DOI https://doi.org/10.1016/j.cryogenics.2024.103849 : source-reported optimized thrust bearing **4.0× force and 2.3× stiffness** versus their reference and journal bearing 5.5×, **not** higher measured rotation speed.
- Savaskan et al., *Enhancement of YBCO superconductor magnetic bearing capability by using multiple bulks*, *Cryogenics* (2025), https://doi.org/10.1016/j.cryogenics.2025.104233 : actual 77K multi-bulk levitation/force and 2D H-formulation validation.
- *Design and experimental evaluation of a superconducting flywheel energy storage system with contactless power transmission*, *Renewable Energy* (2026), https://www.sciencedirect.com/science/article/pii/S0960148126003319 : published HTS bearing plus non-contact torque, **rated max 3000rpm**, not 5000rpm qualification.
- Review *Perspectives in power applications of low and mainly high temperature superconductors*, https://doi.org/10.1007/s40766-025-00071-6, discusses separate **composite flywheel rotors and HTS levitation bearings** near 10,000–14,500rpm; those rotation rates are not demonstrated for a 275mm *bulk YBCO test rotor* and cannot be transplanted as material tensile strengths.

**Repo prior physics and materials (actual owner audit):**
- `DASHI/Physics/Chemistry/AtomicPeriodicTable369ManyBodyHamiltonianTerminalMaxCutExact.agda` explicitly says its exact C3-projected hydrogenic p² Coulomb `Vee=(21/128) I3` does not close **full periodic-material Hamiltonian, spin-orbit, empirical spectra or actual YBCO material identity**. Do not substitute for YBCO structural strength, London penetration, coherence length or pinning current.
- `DASHI/Physics/ExoticGravity/SuperconductingSourceVsConstitutiveEnhancementBidiExact.agda` owns source change vs constitutive change; `NingLiYBCORotatingFieldConstraintExact.agda` owns original NASA rotating-field negative control.
- `DASHI/Physics/QuantumVacuum/ZeroPointModeHyperfabricExact.agda` and zero-point extraction firewall own T->0 oscillator theory, not a physical free-work or gravity coefficient.
- **Real materials/physics equations needed, NOT an extra schematic record:** derive rotation-dependent `J_s(r,t)` from a physically selected anisotropic multi-band GL/London/TDGL plus vortex pinning and RF boundary forcing, compute `J×B` torques and `T_mu_nu`; evaluate standard GR external field and ordinary EM/thermal/mechanical balance response. Only then define an explicitly distinct anomalous constitutive alternative and fit/contrast it to reported regimes. Real material values (`J_c(T,B)`, anisotropic elastic strengths, fracture toughness, weak-link networks, flux flow losses) must be sourced independently.

**Question 'how many RPM does it need?':** Without a physically established gravity or new source-to-observable law there is **no uniquely derivable required RPM**. Under a descriptive *fixed-2MHz* linear fit, 0.3% corresponds to ~6192rpm and 2% to ~35942rpm; this is deliberately marked extrapolation and is invalid to explain the *different* decelerating regime. A real RPM threshold would come from `J_c`, rotational torque/matched RF/slip or flux instability calculations after original source calibration, not from choosing a target anomaly and solving an unconstrained gain parameter. Rotor strength and stability then supply separate bounds, even under levitation.

Attribution: original historical measurements are claims owned by original authors; literature materials/quantum results remain respective experimental authors' work; the user's requested strongest nonlinear RPM/levitation steelman is a distinct hypothesis; exact rational arithmetic and sympy mathematical orchestration in this PR are new computational analysis, not experimental verification.


### Minimal ordered-material physics gate, rather than unsupported material strength

New exact checked `scripts/check_sc_driven_order_parameter_energy.py`: scalar Landau/relaxational `F=a(T-Tc)x²/2+b x⁴/4-k u x`, `xdot=-Gamma ∂F/∂x`, with
```
 dF/dt = -Gamma(∂F/∂x)² + (∂F/∂T) Tdot + (∂F/∂u) udot.
```
With positive `a,b,Gamma` and `T<Tc`, source-free ordered amplitude magnitude satisfies `x²=a(Tc-T)/b`. The work-port terms are exact and map into existing Filsinger signed source/material changes. **The potential has NO mechanical RPM dependence until a physically derived and calibrated `u(omega,B,geometry)` is supplied.** Nor does it have an external gravitational response equation. This tiny GL order-parameter truncation is *not* a complete charged/multi-band anisotropic YBCO Ginzburg–Landau / vortex pinning PDE; it merely proves why a superconducting transition and driven material state do not, on their own, determine a critical rotor RPM or gravitational force. The subsequent required weld is gauge-covariant material current/stress tensor plus Maxwell, measured pinning/critical current and constitutive/source constraints. User's existing atomic 369 hydrogenic C3 projected Hamiltonian is not a YBCO material Hamiltonian. Full SI sourcing of magnetic drive and coherent lattice parameters remains OPEN.


## 18 November — explicit gravity-sector coupling steelman and NASA decelerating field

**Question:** Can one build a physically specified extension of Maxwell + superconductivity that could in principle modify weight during braking, and ask whether NASA's rotating-field experiment tests it? **Yes as a conditional effective-field model; no derivation of an anomalous physical coupling from the standard superconducting Hamiltonian has been achieved.** The original Li–Torr paper is a *theory claim*, not a measured giant amplification. Kowitt's critique targets the interpretative identification of a bulk Meissner permeability with a microscopic gravitomagnetic constitutive coefficient.

### Two distinct gravitation/source claims

(A) **Local source-generated acceleration:** standard weak-field GR responds to stress–energy of disk, RF field, pump, pinning and mechanics. For approximate 0.8 kg at 0.1m, ordinary Newtonian rotor contribution `G m/(g_earth r²) ≈5.44e−10`. To obtain `|delta g|/g_earth=0.02` by boosting this local-source response at the same geometry would require an **extra factor ≈3.67×10⁷** relative to *the whole rotor's ordinary Newtonian field*, and much larger relative to the *increment from rotational kinetic energy*. This is not an exclusion of a *different coupling to ambient Earth's field*; it is the local-source inverse requirement.

(B) **External terrestrial field modification:** hypothetical composition-universal scalar contribution to test-body acceleration with effective action of the form
```
 S_scalar = integral d4x sqrt(-g) [
  -(1/2)(partial phi)^2
  -(1/2)(m0² + lambda |psi_SC|²) phi²
  + beta phi J_matter
 ].
```
This is a **new proposed scalar degree of freedom and couplings**, not the known Earth gravitational potential, not Li–Torr's established prediction, and not derived from the repository's hydrogenic atomic 369 Hamiltonian. One must define the units, kinetic normalization, covariant matter coupling and appropriate source `J_matter` before any physical numbers. Its bulk superconducting state increases a hypothetical scalar effective mass `m_eff²=m0²+lambda |psi_SC|²`; the scalar mode's slab transfer *could* change under a material transition. Whether this yields a negative change in *measured weight*, and whether it evades fifth-force/equivalence-principle constraints, is OPEN. A scalar mass barrier does NOT screen standard Newtonian or Einstein gravitational attraction. A scalar model affecting only a fraction `f_phi` of apparent acceleration can reduce weight by at most `f_phi`; a 2% attenuation already requires `f_phi≥0.02`.

**Exact finite mathematics:** `scripts/check_sc_gravity_coupling_braking.py` locally executed mathematical equivalent PASS; GitHub new script committed in 946cbf5. For a 1D static Fourier component in the scalar sector with effective wavenumber `q>0`, the exact finite slab transfer for state `(phi,partial_z phi)` is
```
  [cosh(q d)     sinh(q d)/q]
  [q sinh(q d)   cosh(q d)  ]
```
and its determinant is identically 1. Transmission amplitude depends on exterior boundary/source matching. Merely writing `exp(-q d)` is a **conditional single decaying-branch model**, not the actual slab transmission ratio in a static Earth geometry. In that simplified limit, if **all** measured gravity were assigned to this scalar branch, 2% attenuation over 10mm corresponds to `q≈2.0203 m^-1`. This illustrative number does not determine the coupling `lambda`, Earth source, material order parameter or lab observable. It is not an experimental fitted parameter or a field-theory prediction.

**Filsinger paid material/state work:** a finite Landau + scalar energy density,
```
 F = a(T-Tc)x²/2 + b x⁴/4 - u x
     + (m0²+lambda x²) phi²/2
```
has *exact* chain rule
```
 dF/dt = F_x xdot + F_phi phidot + F_T Tdot + F_u udot + F_lambda lambdadot.
```
`F_u=-x`, `F_lambda=x² phi²/2`. Under selected gradient-flow relaxational dynamics, `F_x xdot` is a dissipative term; the other terms belong to pump/temperature/field work and cannot be attributed to gravity or unexplained extraction. The physical scalar gradient/kinetic energy and full Maxwell Poynting stress must also be included to claim global conservation. This is a *minimal conditional local free-energy model*, not a Lorentz-covariant full superconductor-gravity dynamical solution.

### NASA rotating-field deceleration vs Podkletnov disk deceleration

Canonical pre-existing NASA owner: `DASHI/Physics/ExoticGravity/NingLiYBCORotatingFieldConstraintExact.agda` (Noever/Koczor/Robertson AIAA-98-3139, NASA https://ntrs.nasa.gov/citations/19990019627 ). Their rotating **applied magnetic field** ran up to 12000 RPM equivalent, in a ~15cm YBCO assembly with and without DC-field levitation; NTRS says no rotating-field/thermal effect observed. This is not evidence that the actual ceramic disk mechanically spun and braked at 12000 RPM. NTRS summary does **not** establish the waveform or angular acceleration during any ramp.

Use field phase `theta_field(t)`, rotor angle `theta_disk(t)`, pole multiplicity `p`. Define *slip phase* `psi=theta_field-p theta_disk` and
```
 omega_slip = omega_field - p omega_disk
 alpha_slip = alpha_field - p alpha_disk .
```
Three distinct candidate mechanisms:

| Hypothesis | Dependence | NASA driven field at stationary disk | Podkletnov braking disk |
| --- | --- | --- | --- |
| Moving mass/stress-energy / mechanical braking | `alpha_disk`, `I_disk omega_disk alpha_disk`, actual rotor currents | zero mechanical source if disk remains stationary | mechanically nonzero during braking |
| Field-acceleration constitutive response | `alpha_field`, field waveform, induced E and superconducting currents | can be driven by a field ramp, must know NASA time series | can also appear if RF/stator drive varied |
| Flux-slip/vortex history | `alpha_field-p alpha_disk`, field B amplitude, pinning, hysteresis | can be driven with disk stationary | can be driven by mechanical deceleration and RF modulation |

Purely *hypothetical*, if NASA's 12000RPM **field** went to rest in 25–30s, average `|alpha_field|=41.89–50.27rad/s²`; Podkletnov reported a **disk** slowing by 1500RPM in 25–30s, giving `|alpha_disk|=5.24–6.28rad/s²`. Ratio of speed changes `8×`, but **no** equal-source, equal-field, equal-sample inference: different disk state, B, geometry, RF, inertia, pinning, phase and probes. This is not evidence NASA performed a comparable deceleration. Even field-only response lacks a numerical prediction until a measured susceptibility/transfer is derived. Physical rotating-field NASA data can constrain that subclass; it cannot automatically exclude a moving-mass-only effect.

One additional NASA donor important for sources: NASA RF-illuminated (1–15MHz) YBCO tests https://ntrs.nasa.gov/search.jsp?R=19990064220 reported a tiny *apparent increase* in gravitational reading, not a 2% mass-independent shielding; keep as attributed observation, not independent replication or a positive force discovery. NASA static/rotating constrained experiments also report ~2×10^-8 g bounds in specific static geometries https://ntrs.nasa.gov/citations/19990023209. Do not apply that exact bound to a different original RF/mechanical source without transfer.

**Typed provenance:** new `DASHI/Physics/QuantumSensors/SuperconductingGravityBrakingCouplingDiscriminatorExact.agda` imports original Li–Torr, Kowitt, NASA and source-vs-constitutive owners; keeps separate mechanism and probe constructors. It proves only constructor separation and provides source-owned experimental witness interfaces. **No Agda kernel check was run**, and named receipts marked false indicate records not independently acquired here, not necessarily missing instruments in the historical lab.

### Highest-alpha physics gate still open

The *real* strong model must derive at least one of:
- A standard, universal coupling route (stress-energy to metric via Einstein constraints) producing the requested external-probe response under the actual disk/field pump; current scale estimate says simple rotor gravity is far too weak.
- A nonstandard **dynamical field** with explicit microscopic source operator, constitutive response `chi_phi(k,omega,T,Jc,...)`, exterior boundary conditions and independent measurable force/clock/gyro output. This must be tested against existing fifth-force/equivalence-principle bounds and the historical original NASA/Hathaway/Graham/Tajmar geometries. Choosing a numerical `lambda` to fit 2% does not derive it.
- A conventional **instrumental force mechanism** with comparable dependence on RF/motion/temperature and genuinely measured force. This is a competing world, not evidence of new gravity.

A stronger phenomenological steelman may use Filsinger's causal nonlinear material state and signed work ledger to predict an actual transient response shape *conditional on* physically specified source coefficients, then fit all original same-drive observations jointly. Without the original raw source histories, a perfect synthetic fit is not original experimental validation. A future unknown/undisclosed mechanism is not bounded by published component SOTA, but a theory needs nonarbitrary dynamics and quantitative discriminators.


## 18 November 2026 — KK zero-mode derived coupling, rotational braking and bremsstrahlung boundary

**Owner reuse verified:** `Docs/physics/KKSingleActionRadionPhysicalSteelman20261024.md`, `scripts/check_kk_radion_reduced_action.py`, `scripts/check_kk_coupled_radion_magnetic_5d.py`, `scripts/check_kk_jordan_sourced_sphere.py`, `DASHI/Physics/Foundations/TSFVKKSameArrowQuadraticMetricWeldExact.agda`, `DASHI/Physics/ExoticGravity/LiTorrKowittMagnitudeDisputeBidiExact.agda`, and Filsinger's signed dynamic material/drive source. These were not reimplemented as allegedly new KK theory.

**Source-attributed mathematical starting point:** ordinary five-dimensional Einstein–Hilbert reduction, circle isometry and Jordan metric `ds5²=gJ_mu_nu dx^mu dx^nu+b²(dy+kA)²`, gives (up to divergence/constants) `sqrt(-gJ)[b R_J - k² b³ F²/4]`. Conformal Einstein-frame transformation `gE=(b/b0)gJ`, `varphi=sqrt(3/2) M4 log(b/b0)` and **explicit assumption** ordinary 4D matter minimally couples to gJ produce `A(varphi)=exp[-varphi/(sqrt6 M4)]` and `beta=M4 dlnA/dvarphi=-1/sqrt6`; relative unscreened scalar fifth force **2 beta²=1/3**. This scalar is a geometric radion, not the previous ad hoc `lambda |psiSC|² phi²`. Different 5D matter origins/stabilization sectors can modify these terms and must be stated rather than quietly assumed.

The geometric KK Maxwell coefficient becomes `Z(varphi)=exp[sqrt6 varphi/M4]` in that normalization, hence `L_EM=-Z F²/4`; linear expansion has **fixed** derivative `∂L_EM/∂varphi|0=-sqrt6 F²/(4M4)`. A magnetic field and its superconducting redistribution can source the radion through *the EM field invariant*, without choosing an independent arbitrary electromagnetic–radion vertex. This is the useful **derived coupling** requested. It is suppressed by the Planck scale and is not an observed giant gravitational effect. The electromagnetic and matter terms must jointly enter a properly normalized radion field equation including the source/medium/5D stabilization. Cancellation/sign depends on conventions and original material coupling. Do not conflate the ordinary graviphoton KK U1 with observed massless electromagnetic photon if a winding/Higgs mass was generated elsewhere.

**New exact script** `scripts/check_kk_sc_radion_braking_reduction.py`, locally executed source-equivalent SymPy algebra; validates `beta²=1/6`, fixed electromagnetic derivative `-sqrt6 F²/(4M4)`, hypothetical one-channel 2% screening requirement and slip/braking work. This means **2% of Newtonian g_N requires 6% attenuation of a radion branch equal to g_N/3; 2% of the measured total (g_N+g_N/3) instead requires 8% radion attenuation**, with both denominators explicit. The oversimplified one-way-exponential optical depths are `-ln(0.94)=0.0618754` and `-ln(0.92)=0.0833816` respectively, not a full Earth/static KK boundary-value solution or source-calibrated material contrast. Crucially, a bare unscreened `alpha=1/3` scalar gives PPN `gamma=(1-alpha)/(1+alpha)=1/2`, strongly contradicted by Bertotti/Iess/Tortora, *Nature* 425 (2003) 374–376 https://doi.org/10.1038/nature01997 with measured `gamma-1=(2.1±2.3)e-5`. This is a genuine **bare-model rejection**, not proof all screened/stabilised KK constructions fail. A short-range massive radion might evade astronomical tests but then normally lacks an Earth-sourced long-range contribution to locally screen; an environment-dependent mass, matter source, screening profile or extra scalar sector needs explicit same-action verification. Bounds from torsion balances and atom physics apply to corresponding force ranges and composition couplings; see https://www.npl.washington.edu/eotwash/results and https://doi.org/10.1103/PhysRevD.110.055022.

**What the superconducting order can do without an extra vertex:** superconducting order changes the electromagnetic source `F²`, current/stress tensors and local condensate energy; those enter standard KK through the established `Z(varphi)F²`, plus assumed matter-frame stress source. Even with a very large field of 1 T, ordinary magnetic energy density `B²/(2mu0)≈3.98e5J/m³`, mass-equivalent density `u/c²≈4.43e-12kg/m³`. This does not create a plausible direct 2%-of-Earth-weight field by standard Planck-suppressed gravity. A **new superconducting state dependent radion mass** `m²(phi,x)=m0²+lambda |psiSC|²` still requires extra physical KK matter compactification action; existing reduction *does not* establish lambda. It is a legitimate constrained EFT hypothesis, not a derived standard KK fact.

**Braking radiation:** German *Bremsstrahlung* refers to radiation from **accelerated/decelerated charged particles**, commonly X-rays from electrons decelerating by ions/targets (NASA https://imagine.gsfc.nasa.gov/science/toolbox/xray_generation_el.html ; DOE https://www.energy.gov/documents/doe-hdbk-1122-2009-cn1-tocpart4pdf). It is **not radioactivity or nuclear decay**. A macroscopic neutral rotor deceleration does not by itself emit X-ray bremsstrahlung. Its changing superconducting currents and vortices, together with RF excitation, can produce ordinary EM field changes and dissipative radiation (including pump sidebands) subject to Maxwell and source work; distinguish low-frequency mechanical braking ~0.03–0.04Hz from 3.5MHz applied excitation and from individual-electron high-energy Coulomb scattering. Quantization gives photon energy h f, but a quantized low-frequency EM mode is not thereby a newly detected scalar/gravitational mode. This path deserves a *nonlinear finite-source radiation* calculation, not an inference from the shared word braking.

**Dynamic source discrimination:** `omega_slip=omega_field-p omega_disk`, `alpha_slip=alpha_field-p alpha_disk`. At fixed field phase, mechanical braking causes slip evolution; field-only braking with stationary rotor causes drive-field slip but not mechanical stress-energy. The Filsinger paid source ledger `d(LI²/2)/dt+RI²=P_mech+P_RF` remains the exact finite-circuit control. Neither a fast field RPM number nor a braking rate determines `F²`, `T_mu_nu` or a radion waveform without flux, current, geometry, thermal histories and 5D matter coupling. Physical NASA original waveform is not supplied; we can compute chosen hypothetical ramps, but must label them as the experimental plan.

**Unresolved same-action acceptance:** stable radion with near-zero 4D vacuum energy; unbroken massless ordinary photon with viable 5D matter source; gauge-covariant REBCO condensate and flux-vortex dynamics; exterior Earth scalar boundary solution; screened/short-range evasion of PPN/Eot-Wash constraints; independently testable test-mass/clock/gyro/flux output; full signed pump/heat/energy and measurement uncertainty. Without those, the derived KK interaction is scientifically meaningful but does not establish a 2% gravitation effect.


## 18 November — KK fixed-coupling physics max-cut: vortex braking radiation, 1T scale, explicit screening action

**Why this cut:** The owner `KKSingleActionRadionPhysicalSteelman20261024.md` already fixes the KK E-frame matter coupling `A(phi)=exp[-phi/(sqrt6 M_Pl)]` under an explicit Jordan matter action and `Z(phi)=exp[sqrt6 phi/M_Pl]` multiplying `F²`. This physics is from the prior KK literature, not an original anomalous-gravity discovery. For a **fixed externally applied magnetic field** `u_B=B²/(2mu0)`, a minimal local effective radion potential contains `V_eff(phi)=m0² phi²/2 + u_B Z(phi)`. Its exact second derivative near phi=0 is `delta m_eff² = 6 u_B/M_Pl²`. Using geometric SI `M_Pl²=c⁴/(8 pi G)`, the *corresponding spatial inverse-length shift squared* is
```
 delta k² = (48 pi G/c⁴) u_B = (24 pi G/(mu0 c⁴)) B².
```
This expression presupposes the fixed-field material/source ensemble. Fixed current or fixed flux and reactive source backaction may alter the proper thermodynamic potential; the full dynamical Maxwell–radion stress-energy is not covered by this local fixed-B calculation.

**Exact numeric result:** at **B=1 T**, `u_B=397887.36 J/m³`, `sqrt(delta k²)=7.041×10^-19 m^-1`. The exact source-equivalent SymPy script `scripts/check_kk_rebco_vortex_screening_maxcut.py` passed locally. Do not identify this with a physical radion mass independent of background or with the *change in* a nonzero preexisting mass: it is the square-root of the *magnetically induced mass-squared term alone*.

**A real boundary condition, not fake exp(-kd) transmission:** For a toy static 1D slab `phi''=k² phi` with `phi(0)=phi_bottom` and upper Robin `phi'(d)=-m_out phi(d)`, the exact upper amplitude ratio is `T=1/[cosh(kd)+(m_out/k)sinh(kd)]`. In the very optimistic `m_out→0` upper boundary limit `T=sech(kd)`, an **8%** reduction of the already-existing unscreened scalar *branch*, necessary for a 2% reduction of `g_N+g_N/3`, at `d=0.01m` requires
```
 k_required=acosh(1/0.92)/0.01 = 41.40645 m^-1.
```
For comparison a one-way exp toy would use `-ln(0.92)/0.01=8.33816m^-1` but does not solve the specified static slab BVP. The required / 1T inverse-length ratio is **5.88×10^19**, and assuming only the minimal fixed-B KK coupling would demand a fantastical `~5.88×10^19 T` magnetic field. **This is a conditional failure of the simple bare-KK electromagnetic mass mechanism, not a universal constraint on nonlinear screened 5D theories.** Moreover, the unscreened original KK `alpha=1/3` is already ruled out as a universal long-range solar-system force by Cassini; `8%` is therefore an inverse requirement for a *counterfactual* bare model, not a real extracted physical constant.

**Explicit stabilizer steelman—not merely naming screening:** `scripts/check_kk_chameleon_material_contrast.py` assumes a **NEW** four-dimensional EFT chameleon potential `V0(phi)=Lambda^5/phi`, and reverses the sign convention of phi (so `A=exp[+phi/(sqrt6 M)]`, `Z=exp[-sqrt6 phi/M]`). Linearized external matter and magnetic contributions give
```
 V_eff≈Lambda^5/phi + [beta rho*c² - sqrt(6) u_B] phi/M,
 beta=1/sqrt(6).
```
The minimum exists only if `lambda=beta rho c² - sqrt6 u_B >0`, with `phi_min=sqrt(Lambda^5 M/lambda)` and `m_eff²=2 lambda^(3/2)/(Lambda^(5/2) M^(3/2))`. Thus `m_eff∝lambda^(3/4)`. This is **not an existing pure 5D KK radion stabilization solution** and not proven consistent with a massless ordinary photon/flat exterior; it is an explicit alternative potential which would require a real 5D compactification parent action.

For illustrative high-density REBCO-like `rho=6000kg/m³`, `B=1T`, the fractional EM-to-matter source term is `6u_B/(rho c²)=4.427×10^-15`, giving a radion inverse-length fractional change around **3.33×10^-15** in this dense homogeneous, weak-field linearized EFT. This mathematical failure of *simple linearised magnetic-field-triggered screening in dense material* does not rule out nonlinear critical systems, vacuum-boundary regions, different 5D sectors or genuinely measured new interactions. It prevents claiming that a macroscopic superconducting magnetic field automatically creates a large KK chameleon change.

**What *braking radiation* actually pays:** Theoretical original donors include I. A. Bulaevskii and E. M. Chudnovsky, *Electromagnetic Radiation from Vortex Flow in Type-II Superconductors*, *Phys Rev Lett* 97, 197002 (2006), https://doi.org/10.1103/PhysRevLett.97.197002 and earlier *Transition radiation of moving Abrikosov vortices*, *Phys Rev B* 61, 12389 (2000), https://doi.org/10.1103/PhysRevB.61.12389. A moving ordered vortex lattice can emit harmonics of a **washboard** frequency and a vortex meeting a material edge can radiate, **without invoking atomic electron X-ray bremsstrahlung**. There is also experimental superconducting vortex microwave-emission literature: https://pmc.ncbi.nlm.nih.gov/articles/PMC6250723/. This is legitimate HF electromagnetic radiation research and is directly relevant to a driven/decelerating vortex population; it is NOT evidence of percent-level gravity shielding.

**Exact finite vortex/source math**, `scripts/check_rebco_vortex_braking_radiation.py`, local SymPy PASS, takes an *assumed* overdamped periodic pinning potential `U_pin=U0(1-cos(2pi x/a))` with `eta xdot + dU_pin/dx=Phi0 J`. It proves
```
 dU_pin/dt + eta xdot² = Phi0 J xdot,
```
then for *assumed* vortex drift velocity `v_vortex` and ideal lattice scale `a≈sqrt(Phi0/B)`, derives `f_washboard=v_vortex/a` with pump amplitude modulation generating `f_washboard ± f_brake` sidebands. At 1T, `a≈45.47nm`; an **illustrative** vortex speed 10 m/s yields ~220MHz, 100 m/s yields ~2.2GHz. **A vortex velocity is not the rotor's rim velocity**; the rotor RPM and flux-pinning/current equation must actually derive `v_vortex(t)`. Radiation POWER, coupling to the outside, and cavity/mode response were not determined. An exact driven scalar mode `Qddot+w²Q=J_mode` checks the separate energy equation `dU_mode/dt=J_mode Qdot` to prevent an unpowered radion signal.

**Filsinger non-promotion:** pump work, mechanical braking, vortex viscous losses, magnetic/condensate storage, EM radiation, and scalar-mode work are distinct signed ports. Recycling reactive energy or moving HF signal into a quiet band cannot establish new external gravitational work; likewise `hf` photon energy is not photon NUMBER/radiated POWER. Reuse `SmithFilsingerDispersiveMaterialPortExact`, `SmithFilsingerSpaceTimePoyntingTelescopeExact`, `ZeroPointExtractionFirewallExact` and existing KK same-action and source owners. Neither the prior NIST/SI registry nor atomic p²/369 calculations yields real YBCO vortex density, Jc or pinning.

**Current strongest conclusion:** The KK-derived magnetic coupling and a bare density-screening EFT now have explicit computed **negative-scale results**. The high-alpha physical alternative is an externally sourced, nonlinearly stabilised KK scalar whose Earth-compatible exterior profile, superconductor-dependent local source, waveform and test-mass force are derived from **one** 5D parent action *and* satisfy Cassini, fifth-force, laboratory atomic and torsion-balance constraints. That remains OPEN. The driven-vortex electromagnetic sideband model is a credible established physics donor for testing and estimating RF emission, not yet a demonstrated radion emitter or gravitation modifier.

**Attribution:** 5D KK reduction, chameleon mechanisms, vortex-flow/transition radiation, and external gravity constraints are attributed to their original literature; prior DASHI modules own existing formal fragments; the user's physics-first source-braking/KK synthesis request defines the research direction; our new scripts supply mathematically checked *conditional* algebra and numeric comparisons, not experimental evidence.


## 18 Nov — User clarification: coherent charged *mass* during braking, not braking photons transforming into gravity

**Conceptual distinction:** This user's steelman concerns a macroscopically coherent charged condensate with collective motion and sudden mechanical/RF braking. It does NOT posit EM bremsstrahlung directly converting into gravity. Ordinary type-II YBCO order `Psi=|Psi| exp(i theta)` describes a collective Cooper-pair state while lattice ions, weak links, vortices, quasiparticles and rotor mechanics require distinct degrees of freedom. A sample's entire rest mass does not occupy one Cooper-pair phase.

**Established physics donor:** Standard London superconductor quantization gives `m v_s + q A = hbar grad theta` and for uniform low-fluxoid rotating bulk `B_L=-2(m/q) Omega`, subject to boundaries, Meissner screening and flux trapping. See https://www.nature.com/articles/nphys646 ; https://journals.aps.org/prb/abstract/10.1103/PhysRevB.89.104501 . `scripts/check_sc_coherent_mass_london_braking.py` constructs exact symbolic curl and London law and calculates approximately **5.95 nT at 5000rpm** using the nominal pair mass/charge ratio. This is a rotating-superconducting-electromagnetic effect, not a known large gravitational force, and is a small ideal intrinsic field compared with externally applied RF/levitation fields.

**High-value nonlinear transient construction to build next:** mechanical lattice angle `theta_l(t)`, condensate phase `theta_s(r,t)`, applied field `A(r,t)`, trapped flux and vortices all separate. Solve a dynamical gauge-covariant superconducting order equation plus Maxwell with source-controlled `Omega_l(t)`, RF drive, pinning, dissipation and a signed mechanical/driver/EM work ledger. Braking can induce a phase-lag transient `delta Omega`, e.g. `tau deltaOmega_dot+deltaOmega=tau*(-Omega_l_dot)` as a response-model candidate, but the actual relaxation time `tau` is physical material-dependent, NOT selected to fit Podkletnov. Work flux and stress-energy `T_mu_nu` can then source ordinary GR and any viable KK radion.

**Coherence nuance:** `N` in-phase current amplitudes may interfere into a `N²` intensity in an angle/frequency-selected mode; this does not increase the source's rest mass to `N² m`, or establish that net emitted power scales `N²` at fixed total available energy or that a static gravitation field is enhanced. Coherence can enhance directional emission, collective radiation, correlations and signal readout. Standard gravity remains sourced by total conserved stress-energy; any claimed anomalous material/gravity constitutive coefficient needs a same-action derivation and external validation.

**Relation to KK:** Under the existing geometric KK zero mode, the coherent source changes Maxwell `F²` and material `T_mu_nu`; the radion couples at fixed Planck-suppressed strength with no free coherent `N²` mass multiplier. A physically viable *extra collective excitation* could appear as a new effective field or KK mode only after deriving its 5D matter Hamiltonian, compactification, source/observable map, stabilisation and fifth-force bounds. The above is a coherent-mass hypothesis suitable for falsifiable dynamic modeling, not a reported experiment or a proof of an exotic field.

**Attribution:** Original London/fluxoid/BCS and KK theoretical results remain attributed to published sources; DASHI existing Li–Torr, Filsinger, quantum and atomic owners reused. User originated the 'macroscopic coherent charged mass under braking' hypothesis here. New symbolic checks are computational identities only.


## 18 Nov — One-source coherent lattice/condensate braking (exact dynamics, no empirically claimed gravity)

**Original research lineage:** London moment measured for rotating superconductors (Phys Rev 184,460 (1969) https://doi.org/10.1103/PhysRev.184.460); rotating vortex energetics (Phys Rev B 62,9740 https://doi.org/10.1103/PhysRevB.62.9740); time-dependent GL for accelerating/rotating superconductors (Physica C 496, 17–22 (2014) https://www.sciencedirect.com/science/article/abs/pii/S0921453413003213); time-dependent London moving-vortex dissipation (Phys Rev B 97,094510 https://doi.org/10.1103/PhysRevB.97.094510). **User-origin idea:** coherent mass/charge state during abrupt braking. **New mathematical calculation:** finite coupled angular-mode equations and matched London/KK source observables; **not** a microscopic BCS/TDGL derivation or gravity experiment.

### Signed common-source angular model

`Omega_l`: ionic-lattice rotation rate; `Omega_s`: effective condensate angular-mode rate; `psi`: *relative mechanical angular displacement* (NOT automatically microscopic Cooper-pair U(1) gauge phase); effective inertias `I_l,I_s`; coupling stiffness `K>=0`, viscous drag `eta>=0`; possible condensate damping `D_s>=0`; independently funded torques `T_brake,T_RF`. A testable finite-mode constitutive truncation:
```
 psi_dot = Omega_l-Omega_s
 T_c = K psi + eta (Omega_l-Omega_s)
 I_l Omega_l_dot = T_brake - T_c
 I_s Omega_s_dot = T_RF + T_c - D_s Omega_s .
 E = (I_l Omega_l² + I_s Omega_s² + K psi²)/2
 dE/dt = T_brake Omega_l + T_RF Omega_s
         - eta (Omega_l-Omega_s)² - D_s Omega_s².
```
The identity is EXACT algebra, not an imposed free output port. This includes braking power (potentially extracted or dissipated externally), RF work (source paid) and collective elastic storage. An RF *torque* is only a phenomenological interface unless calculated from coupled Maxwell currents and drive phase; a real YBCO vortex ensemble has many internal modes, current-induced forces and hysteresis. Static constant-speed differential vanishes in the reduced drag-only, initially equilibrated case; braking transient requires actual source history.

**Exact verified local script and committed source:** `scripts/check_sc_coherent_braking_same_source_dynamics.py` PASS in this turn using Python/SymPy: proves two-inertia ledger, analytic one-pole braking ramp `Omega_s-Omega_l=a tau(1-exp(-t/tau))`, post-ramp relaxation, ideal London field `B_L=-2(m/q)Omega`, exact magnetic energy `delta(B²)/(2mu0)`, KK reduced `Z(phi)=exp(sqrt6 phi/M_Pl)` field-invariant source derivative, and radion-mode propagating threshold `omega=m_phi c²/hbar` at zero spatial momentum. The scalar dispersion relation by itself does not derive coherent radion emission or percent weight effect. Tau is unmeasured, so illustrations for a 27.5-second 5000→3500rpm ramp yield 0.057/0.571/5.712/53.47 rad/s lag for tau=0.01/0.1/1/10 seconds respectively. If one **extrapolates the ideal London field to a condensate effective angular velocity**, the tau=1s lag implies ~6.50×10^-11 T extra field. This extrapolation must **not** be presented as a direct microscopic London theorem for a non-equilibrium pinned vortex medium. Total B includes applied RF, trapped flux and boundary currents.

### Why the finite elastic mode corrects the tau-only picture

In `scripts/check_sc_coupled_rotor_frequency_response.py`, the same-source linearized *prescribed Omega_l* transfer with `D_s=0,T_RF=0` is
```
 H_s(z)=Omega_s(z)/Omega_l(z) = (K+eta z)/(I_s z²+eta z+K)
 H_lag(z)=(Omega_l-Omega_s)/Omega_l=I_s z²/(I_s z²+eta z+K).
```
Natural response scale `sqrt(K/I_s)`, damping `eta/I_s`. Exact symbolic tests PASS. In the `K=0` fluid relaxation limit, constant acceleration leaves an asymptotic velocity lag `Omega_l-Omega_s=-I_s a/eta`; with `K>0`, the relative **velocity** lag instead tends to zero during an arbitrarily prolonged linear ramp, while finite phase/angular displacement tends to `-I_s a/K`. This is a genuine qualitative distinction with a time-resolved experimental discriminator, not a fitted Podkletnov peak. The transfer model is a simplified modal response; a real sample's K must come from fluxoid/pinning or Josephson phase physics and cannot be identified with mechanical inertia by assertion.

### Matched Maxwell, standard gravitational and KK source

From exactly the same `Omega_l(t),Omega_s(t),psi(t),T_RF(t)`, predict magnetic output through a **separately calibrated** `J_s,A,B,mu0` map and a London limit, then calculate Maxwell Poynting and Lorentz stress tensor, rotor mechanical stress-energy including the lattice/condensate internal coupling, and feed `T_mu_nu` into GR and `F_mu_nu F^mu_nu` and Jordan matter stress into the existing KK radion action. The KK fixed zero-mode electromagnetic source derivative is `∂[-Z(phi)F²/4]/∂phi|0=-sqrt6 F²/(4M_Pl)`; mass threshold for propagating modes must be compared to actual braking/RF/flux frequencies (1–4MHz pump may emit EM sidebands but not automatically light radion radiation). **No external measured gravitational force has been calculated**: finite compactification/source boundary-value solution, microscopic parameters, time-dependent Maxwell/TDGL fields and probe geometry remain OPEN.

**Attribution and non-promotion:** original London and TDGL work is credited to original researchers; conditional coherent-mass hypothesis comes from user; finite symbolic dynamics/new code is our computational contribution; existing DASHI Filsinger/KK owner remains canonical. Do not count coherent Cooper-pair number as N² rest mass or mistake collective radiation amplitude for new energy.


### Rotating fluxoid ring: more constrained than generic angular phase mode (same round)

The exact locally executed source `scripts/check_sc_rotating_fluxoid_braking.py` (committed) models a simplified uniform superconducting ring with **quantized fluxoid n** and Cooper-pair mass/charge `m,q`, loop area `A`, kinetic inductance `Lk`, geometric inductance `Lg`, applied external flux `Phi_ext` and actual ring flux `Phi`. This is a finite reduced-circuit London model: microscopic gauge phase, superconducting winding, and mechanical angle have separate meanings. The assumed rotating-ring constraint `Lk*I+Phi+(2m/q)*A*Omega=n*Phi0` gives
```
 I = [n Phi0 - (2m/q) A Omega - Phi]/Lk
 U = (n Phi0 - (2m/q) A Omega - Phi)^2/(2Lk)
     + (Phi-Phi_ext)^2/(2Lg)
 Phi_eq = [Lg (n Phi0-(2m/q) A Omega)+Lk Phi_ext]/(Lg+Lk).
```
At `n=0, Phi_ext=0`, `B_eq=Phi_eq/A=-(2m/q) Omega Lg/(Lg+Lk)`, the ideal London form for `Lg>>Lk`. **Do not claim exact homogeneous bulk YBCO from this loop limit.** Changing Ω induces current/flux changes even without changing n. Phase slip `n→n+1` changes the on-shell energy by exactly `Phi0[2(nPhi0-(2m/q)A Omega-Phi_ext)+Phi0]/[2(Lg+Lk)]`; a real phase slip has barriers, activation and energy-balance terms not calculated here.

With a separate overdamped *flux* relaxation `Phi_dot=-U_Phi/eta`, exact paid source work is
```
 U_dot = U_Omega Omega_dot + U_Phi_ext Phi_ext_dot
       - U_Phi²/eta.
```
The relaxation time `tau=eta Lk Lg/(Lk+Lg)` is derived for this **assumed effective dissipative dynamics**, not measured or inferred for YBCO. Braking, applied RF flux, trapped integer winding and relaxational dissipation now coexist in one explicitly sourced energy function. Its spatial field, vortex pinning and emission require the same-original gauge-covariant Maxwell/TDGL source; KK receives no arbitrary extra coefficient and would use the derived `F²` and full stress-energy.

**Three independently executed local exact checks** in this implementation round: `check_sc_braking_coherent_dynamics.py` (two-inertia energy, ramp/hold, ideal London/KK source), `check_sc_coupled_rotor_frequency_response.py` (K>0 stiffness vs K=0 lag frequency response), and `check_sc_rotating_fluxoid_braking.py` (fixed-winding current/flux, phase-slip energy, signed flux/driving work). Committed files are named `scripts/check_sc_coherent_braking_same_source_dynamics.py`, `scripts/check_sc_coupled_rotor_frequency_response.py`, `scripts/check_sc_rotating_fluxoid_braking.py`. Corresponding code passed in local container before GitHub commit; exact remote HEAD replay and Agda kernel remain NOT VERIFIED. Scientific limitations: user-proposed coherent-charge braking mechanism is conditional; London/fluxoid results belong to original superconductor physics; finite energy/transfer identities are new computational synthesis, not 2% gravitational-force prediction.


## 19 November — executed spatial TDGL prescribed-link factorial

New executable `scripts/check_sc_spatial_tdgl_braking.py` (commit c9322419407c5e05c5dee5e6509d6d1cb9068488) locally executed before commit. Standard discrete GL energy on open 8x8 lattice: F=sum(a|psi|²+b|psi|⁴/2)+J sum|exp(-i A_e)psi_head-psi_tail|²; a=-1,b=1,J=.4; gradient relaxation psi_dot=-gamma partial_conjugate_psi F, gamma=1. Prescribed effective link phases A=r(t)rot+p*.12 sin(7t)rf, dimensionless r=.12 initially, declining to .04 over 10 time units in braking worlds. Rot is symmetric-gauge link pattern and rf is uniform x link pattern. All worlds start from same relaxed state. Temporal gauge, time-independent discrete gauge covariance explicitly checked; not full dynamical electromagnetism. Effective rotational link curl must NOT be interpreted as physical Maxwell F². A uniform oscillating RF link has zero spatial curl and represents a prescribed electric drive in the chosen temporal gauge. No SI mapping, physical carrier frequency or vortex event established.

Exact chain-rule ledger dF/dt=Wbrake_dot+WRF_dot-2 gamma ||partial_conjugate_psi F||². Numerical link derivative finite-difference and random spatial gauge transformation checks PASS. Four matched worlds, numerical tolerances 1e-8 vs 1e-10; all integrated work/energy differences <1e-5, maximum ledger residual <3.64e-8 at tighter tolerance. Table columns Wbrake, WRF, dissipation, deltaF:
hold 0,0,~0,~0;
brake -0.684033214,0,0.007765289,-0.691798467;
rf 0,1.17613984,0.878399829,0.297740003;
combined -0.681127246,1.08060980,0.787134210,-0.387651665.
Factorial interaction WRF=-0.0955300405 (~8.12% reduction), dissipation=-0.0990309073, deltaF=0.00640679828. This is a nonlinear interaction in selected model, not enhancement or novel energy production. Negative rotational parameter work is NOT proven mechanical shaft recovery. Peak link derivative norm 1.29780448 RF-only vs 1.27402122 combined. No actual phase-slip/vortex history, spatial mesh convergence, Maxwell backreaction, stress-energy or KK exterior solved. Source attribution: standard GL/link methods, existing BalabanLatticeCovariantDivergence and SmithFilsingerSpaceTimePoyntingTelescopeExact are relevant architectural donors (not imported or formally welded in this Python code). User's coherent braking/RF hypothesis is distinct from standard theory; new numerical fixture and factorial analysis are our contribution. No Agda kernel or exact remote replay claimed.

Next: promote physical electromagnetic links to dynamical variables with plaquette field energy and electric field evolution; keep mechanical inertial connection separate, include normal current/charge continuity, geometry and gauge-consistent scalar potential, vortex winding and mesh/physical parameter convergence. Feed physical Maxwell F² only into KK; total conserved stress-energy including drive/lattice/thermal reservoirs into Einstein. No measured anomalous gravity or calibrated YBCO prediction yet.


## 19 November — actual transverse Maxwell–TDGL replay and retarded scalar exterior

Replayed the supplied previous solver locally, retaining its actual 401-sample invariant histories (capture option in scripts/check_sc_tdgl_maxwell_braking.py, commit 0fcafd9). Reproduced all four previous integrated Maxwell/TDGL outcomes, gauge covariance and tolerance checks; max energy residual 4.25e-9. New scripts/check_sc_kk_retarded_source.py (afecebb) locally executed successfully before committing the same program text. It solves a dimensionless 1D semidiscrete Klein–Gordon field with positive quartic self-interaction, fixed endpoints at +/-32, edge sponge, zero initial perturbation and a normalized Gaussian source profile multiplying the actual baseline-subtracted integrated EM invariant. Unit coupling is a numerical fixture, not the derived SI Planck coupling. This is a **one-way** source replay, not self-consistent scalar feedback, a 5D stabilization derivation, or a 3D rotor exterior. The prior EM solver is transverse-only and its contraction uses dimensionless discretized field norms; no SI conversion or full stress-energy.

At x=5 the peak absolute gradient (brake, RF, combined) is:
m=.2, lambda=0: .0593254267, .0144096732, .0643294920.
m=1, lambda=0: .00526320433, .00848268997, .00728762193.
m=.2, lambda=10: .0359292041, .0124988858, .0319140786.
Peak absolute time-aligned factorial gradient differences .00316029339, .00424639791, .02510070488 respectively; these are interaction magnitudes, not superadditive peak gains. Steady residual gradient <=3.44e-7. Positive quartic suppresses combined peak compared to light linear; heavier mass changes relative importance of braking and RF. Light linear combined mesh comparison dx=.2 vs .1 changes gradient peak by .03663%; not full convergence across all models. Scalar signed ledger E=W_source-Q_sponge max absolute residual across cases <2e-10. Zero coupling yields identically zero response; half coupling gives half linear gradient within 1e-6. No feedback debit to Maxwell in this one-way fixture, so scalar ledger is not a combined conservation proof. No Agda check, exact remote replay, physical force or radiation detection claimed.

Attribution: classical Klein–Gordon and GL/Maxwell theory, prior KK reduction and Filsinger work ledgers remain respective original owners. User proposed coherent charged matter braking; this numerical synthesis and matched controls are new computational work, not historical evidence. Next high-alpha: reciprocal action-derived EM/radion source and backreaction with conserved total energy, physically sourced 3D geometry and normalization, longitudinal charge closure and vortex tracking, then constrained stable 5D radion parameters and actual probe force.


## 19 November — executed reciprocal Maxwell–TDGL–radion Hamiltonian

New script scripts/check_sc_kk_reciprocal.py (9ec0938), executed locally from matching program text. Reuses preceding 6x6 transverse GL/Maxwell fixture and 1D Gaussian-projected scalar exterior. Standard KK exponential gauge kinetic factor Z=exp(g*dx*sum(w*phi)); selected dimensionless g and projection are not derived SI coupling/geometry. Hamiltonian electromagnetic term P²/(2Z)+Z B²/2 yields A_dot=P/Z=E (electric velocity convention), P_dot=-Q^T j-Z R^T B-sigma E+f, scalar forcing -(g/2) Z (B²-E²) w. Thus both directions of coupling arise from same discrete Hamiltonian at fixed canonical P. Rotational link only enters GL. Full H=F_GL+H_EM+H_scalar; exact continuous semidiscrete chain-rule ledger Hdot=j·rot*r_dot+E·f-2||grad_GL||²-sigma E²-dx sum(damping*v²). No matter conformal radion coupling, longitudinal charge sector, gravity metric, real 5D stabilization, or physical YBCO normalization. Preparation uses extra scalar damping only before observation; residual steady drift remains, and factorial comparisons subtract hold waveform. Scalar projection is nonlocal finite-mode approximation, not a local 3D relativistic field theory.

24 executed runs: four worlds for g=0 and three g=.2 mass/quartic configurations, plus four worlds each for scalar dx=.125 refinement and tighter solver tolerance. Original rtol 2e-8 failed selected 2e-6 ledger criterion (2.49e-6); reran with 2e-10 successfully, selected tighter 2e-12 check. Main maximum residual 5.65e-8, selected tighter combined 5.12e-11. Zero coupling exactly zero scalar signal. At x=5 peak absolute gradient change (brake,RF,both) for m=.2 lambda=0: .002959060355,.000715767887,.003208164163; m=1 lambda=0: .000265726229,.000422407468,.000364361875; m=.2 lambda=10: .002790490051,.000666944716,.003046171182. Time-aligned factorial maximum absolute gradient interaction .000155215453,.000211931343,.000226743826 respectively. No superadditive peak demonstrated. Combined light linear scalar dx=.125 peak .00320990473 (~.0543% change); tighter tolerance dx=.25 peak .00320816416. No mesh convergence for GL lattice or all scalar models. Prior one-way model used different coupling normalization, background and source projection; absolute amplitudes cannot be directly compared to isolate feedback. All results dimensionless.

Attribution: KK gauge kinetic factor, Hamiltonian Maxwell and GL/Klein-Gordon physics are standard literature and prior DASHI operators; user proposed coherent charged-mass braking; reciprocal finite numerical construction and matched comparisons are new computational work. No Agda kernel, exact remote execution, physical experiment or gravitational acceleration claim. Next maximum cut: matched reciprocal vs frozen-source control at identical coupling and preparation, source-spectrum/pump-frequency and mass scans under matched work, selected resonance stability and physical SI geometry/normalization. Do not claim physically admissible resonance before actual constraints.
