# KSW668 F8 maximum cut V — ORIGINAL moving AdS5 compact TT prepotential, three regular multipoles, both electric-Weyl readouts

**15 November 2026 · Single current rollup PR #1512**. Existing #1508 was merged. No new competing PR. This is the same original \(\ell=1,\sigma=1,\kappa_5^2=6,\ a(t)=t\) AdS5 Einstein–Israel source background, not a stationary RS2 propagator or a flat 5D test scalar.

**Current disposition:** exact source-level tensor decomposition and conditional Agda transport owner added, a new 3D compact TT moving-boundary time-domain solver added, and **both distinct Weyl tensors evaluated numerically**, but three-grid convergence and beyond-cone residual tests still **FAIL**. The nonzero early grid values must not be interpreted as observed or mathematically certified gravity-wave shortcuts.

## 1. Avoid the old UV/IR inverse numerically, without abandoning the original tensor stress

Pre-existing exact compact TT source:
\[
S_{ij}[f]=(P_i{}^a P_j{}^b-\tfrac12 P_{ij}P^{ab})Q_{ab}f,\quad
P_{ij}=-\delta_{ij}\Delta_{\bf x}+\partial_i\partial_j,\quad Q=\mathrm{diag}(0,1,-1).
\]
It has no \(1/k^2\) singularity, is trace-free and divergence-free for every spatial momentum (checked symbolically for arbitrary \(k_x,k_y,k_z\)), and preserves the spatial compact support of smooth \(f\).

For the ORIGINAL linear AdS5 tensor operator and the ORIGINAL moving Israel Neumann normal condition,
\[
L=-\partial_T^2+\partial_z^2-\frac3z\partial_z+\Delta_{\bf x},
\quad B=(1-v^2)\partial_y+v\partial_T|_y,\quad y=z-b(T),
\]
all coefficients depend on \(T,z\), not on \({\bf x}\). Therefore **on smooth fields**
\[
[L,S]=0,\qquad [B,S]=0,
\]
by mixed spatial derivative commutation. Given auxiliary prepotential \(\Psi\) with \(L\Psi=0,\ B\Psi=g\), then \(H_{ij}=S_{ij}[\Psi]\) solves the original **tensor equation** with original compact TT physical boundary source \(B H_{ij}=S_{ij}[g]\). This preserves the physical Israel coefficient if \(g=-6\) times the scalar source carrier.

**New owner:** \`scripts/ksw668_f8_prepotential_commutation.py\` verifies a nonseparable smooth test field, arbitrary Fourier momenta, trace/divergence and the actual oblique normal operator (**7/7 local tests**). \`DASHI/Physics/Gravity/KSW668AdS5TensorPrepotentialCommutationExact.agda\` transports exactly the two commutation hypotheses through a typed Agda contract; it does **not** manufacture the actual differentiable manifold or kernel certify the differential commutation. The SOURCE-equivalent operator identity is mathematically proved by coefficient independence, but F11 pinned kernel remains OPEN.

This route removes the old fourth-derivative **source injection** from the auxiliary evolution; differentiating \(\Psi\) four times after evolution still amplifies numerical errors, so the following angular decomposition is preferable.

## 2. Exactly three nonzero zonal angular harmonics, no Fourier inverse

Set \(r=|{\bf x}|,\ \mu=x/r\) relative to the original source/receiver x-axis. The azimuthal average of the physical local \(yy\) TT operator on a radial \(f\) is
\[
S_{yy}^{\mathrm{zonal}} f=\tfrac18\left(\partial_x^4+6\partial_x^2\Delta+\Delta^2\right)f
=\sum_{\ell\in\{0,2,4\}} S_\ell f(r)P_\ell(\mu).
\]
Its Fourier angular factor is **exactly**
\[
\frac{\mu^4+6\mu^2+1}{8}
=\frac25P_0(\mu)+\frac47P_2(\mu)+\frac1{35}P_4(\mu).
\]
New \`KSW668AdS5TTMultipoleAngularRationalExact.agda\` records/proves this rational polynomial identity and the three effective dimensions, with \`solve-∀\` and closed rational ring solves. Source-equivalent SymPy/MPMath checks compare the **real-space** coefficients at four independent radii with \(<10^{-10}\) relative discrepancy. **Agda 2.9 kernel not run.**

The real-space radial multipole source coefficients are
\[
\begin{aligned}
S_0 f &= \tfrac25(f^{(4)}+4f^{(3)}/r),\\
S_2 f &= \tfrac47(f^{(4)}+f^{(3)}/r-6f''/r^2+6f'/r^3),\\
S_4 f &= \tfrac1{35}(f^{(4)}-6f^{(3)}/r+15f''/r^2-15f'/r^3).
\end{aligned}
\]
At \(\mu=1\), \(P_\ell(1)=1\), so \(H_{yy}=\sum_{\ell=0,2,4} H_\ell(r)\) at the same axis observer. This is **not** an approximation that discards other modes for this axisymmetric projection; the azimuthal \(m\ne0\) components vanish at the x-axis by rotational symmetry of the propagation operator.

Conjugate \(H_\ell=(r/\epsilon)^\ell V_\ell\). Then
\[
\big(\partial_r^2+2r^{-1}\partial_r-\ell(\ell+1)r^{-2}\big)H_\ell
=(r/\epsilon)^\ell
\big(\partial_r^2+(2\ell+2)r^{-1}\partial_r\big)V_\ell.
\]
Thus the original tensor problem becomes **three regular radial numerical systems of effective dimensions 3,7,11**, each coupled to its own original moving-wall \(y\)-characteristic and Israel source. These are effective radial operator dimensions, **not extra physical bulk dimensions**. Origin-regular normalized source values for the chosen \(C^\infty\) bump are exactly \(-24,-32,16/35\) for \(\ell=0,2,4\).

## 3. The new actual moving 3D TT numerical producer

**Code:** \`scripts/ksw668_f8_tt_multipole.py\`, tested by \`scripts/test_ksw668_f8_tt_multipole.py\` (**16/16 PASS**). Uses SSPRK3, 2nd-order characteristic upwind in \(y=z-b(T)\), radial volume-measure finite difference for dimensions 3/7/11, a smooth temporal pulse, *analytic radial Gauss–Legendre **cell-averaged** compact TT source*, and cubic interpolation to the **identical physical receiver r** across all meshes. No spatial k-FFT or Fourier-Bessel inverse is used.

**Critical physical support accounting:** averaging over radial cells thickens the represented compact source support by at most \(\Delta r/2\); the numerical photon-dark guard subtracts that half-cell margin from the original photon exclusion. The original \(t=12\) reference control uses
\[
r_g=2.549365760961938,\quad r_{\rm recv}=r_g-0.012=2.537365760961938,\quad
r_\gamma=\log12=2.484906649788,\quad \epsilon=.04.
\]
Therefore \(\ r_{\rm recv}-\epsilon-\log12=0.01245911117>0\); after half-cell enlargement the three **positive** numerical photon-dark margins are 0.0064591, 0.0084591, 0.0094591.

The source begins at \(t=1\) with temporal support \(\Delta T=.065\). The far negative control \(r_{\rm far}=r_g+0.1=2.64936576096\) lies at least 0.06 beyond the entire continuum source's bulk causal future; the discrete half-cell thickening still leaves a positive gap. All three meshes use the **same outer domain** (\(r_{\max}\approx3.15,y_{\max}\approx2.6\)), and the 0.008 run was independently reproduced with a larger domain with identical displayed values.

## 4. Numerically evaluate TWO DIFFERENT Weyl observables

Use physical proper time \(t\) and \(\eta=\log t\); along the moving brane
\(S=dT/d\eta=\sqrt{1+t^2}/t\). At the source-free receiver:
\[
H_{\eta}=S H_T,\quad
H_{\eta\eta}=S^2H_{TT}-H_T/(t\sqrt{1+t^2}).
\]
For \(H_\ell=(r/\epsilon)^\ell V_\ell\), \(H_{xx}\) and \(\Delta_3 H\) at \(\mu=1\) are reconstructed using only \(V_\ell,V_\ell',V_\ell''\) and the exact angular eigenvalue. We then compute the distinct curvature components
\[
\boxed{E_{yy}^{(4)}=-\frac{H_{\eta\eta}+\partial_x^2H_{yy}}{4t^2}}
\quad\text{and}\quad
\boxed{\mathcal E_{yy}^{(5)}=-\frac{H_{\eta\eta}+2H_\eta-\Delta_3 H_{yy}}{2t^2}}
\]
in the normalized TT conformal gauge, where the projected 5D identity is the source-free receiving limit of the previously derived Shiromizu–Maeda–Sasaki tensor-effective equation. The source-containing term is not discarded near the emitter; the formula is invoked **only at source-free receiving coordinates**.

The time derivatives are centred across the **same physical moving-brane endpoint** and the radial quantities come from cubic local interpolation. These are **numerical curvature diagnostics, not rigorous gauge/constraint or physical-detector receipts**.

### Three-grid original \(t=12\) receipt

All receiver quantities scaled by \(\epsilon^4\) and a chosen dimensionless scalar carrier amplitude; do not read them as SI detector strain or a calibrated wavelength.

| \(\Delta r\) | Retarded \(H_{yy}\) | Intrinsic \(E^{(4)}_{yy}\) | Projected \(\mathcal E^{(5)}_{yy}\) |
|---:|---:|---:|---:|
| 0.012 | −4.77056316e−6 | −6.51175894e−5 | −3.57761806e−6 |
| 0.008 | −5.28480046e−6 | −4.24421644e−5 | −2.33019008e−6 |
| 0.006 | −1.00303410e−5 | −5.93398237e−4 | −1.74154712e−5 |

Fine-to-middle relative differences **47.31%**, **92.85%**, **86.62%**, respectively. Beyond-bulk-cone finest absolute values \(2.289\times10^{-7},\ 7.237\times10^{-6},\ 1.540\times10^{-7}\), corresponding to **2.28%**, **1.22%**, **0.88%** of the respective early receiver amplitudes. **All three numerical acceptance gates FAIL.** The coarse-to-middle H drift is smaller (9.73%), but the third mesh explicitly defeats a premature convergence promotion.

Previous point-source sampling (rather than analytic cell averaging) yielded a sign-changing early field on two grids, illustrating how dominant source quadrature errors were. The new cell-averaged source repairs that *specific* discretization mechanism but not yet the solution's overall numerical accuracy.

**Reproducer:** \`scripts/ksw668_f8_tt_multipole_refinement.py\` runs the identical \(r_{\max}=3.15,y_{\max}=2.6\) three-grid benchmark, records all three observables and outside-cone controls, and **exits 42** on failure. \`Artifacts/ksw668/ads5_f8_tt_multipole_threegrid_20261115.json\` retains the exact local source-equivalent measurements. The previous legacy 3D Fourier producer still independently fails its own \`--legacy-full\` gate.

## 5. Revised exact lemmas, phases and deliverable acceptance

| Cut | Exact lemma / owner | Accepted this round | Still REQUIRED |
|---|---|---|---|
| F8-ALG1 | \`ads5OriginalMovingTTPrepotentialBulkAndIsraelCommutation\` | General Fourier TT trace/transversality, coordinate-homogeneous operator commutation; conditional Agda transport owner/source-equivalent PASS | actual smooth differential analytic witness and pinned Agda kernel |
| F8-ALG2 | \`ads5OriginalTTZonalMultipoleFiniteExact\` | exact Legendre 0/2/4 identity and radial-source formulas; rational Agda source authored/source-equivalent PASS | pinned Agda 2.9 compile |
| F8-ALG3 | \`ads5OriginalTTMultipoleRegularRadialConjugacy\` | exact radial algebra \(\ell\to d_{\rm eff}=3+2\ell\), nonzero original Israel normal carried identically | typed continuum PDE/Sobolev operator weld into Agda |
| F8-NUM1 | \`ads5OriginalCompactTTConservativeRadialCellSource\` | analytic compact-bump source cell averaging, regular origin and photon margin incl half-cell; PASS 16-case tests | quantitative quadrature error bounds vs independent source profile |
| F8-NUM2 | \`ads5OriginalMovingTTBothElectricWeylNumericalReadout\` | actual 4D intrinsic/5D projected readouts source-level implemented, same receiver, source-free SMS | **FAILED numerical convergence** |
| F8-NUM3 | \`ads5OriginalMovingTTThreeMultipoleThreeObservableConvergence\` | reproducible three-grid error and beyond-bulk negative controls | **OPEN**: uniform two-dimensional \(\Delta r,\Delta y,\Delta T\) refinement; spectral/finite-volume convergence estimate; null-cone leakage bound; no multiple stencils with arbitrary percent cut |
| F8-FIO | \`ads5OriginalT2NeumannToWeylEllipticFIOComposition\` + \`ads5OriginalT2ActualCompactTTNonzeroEarlyBothWeyl\` | earlier original \(t=2\) high-frequency microlocal external-theorem **proof candidate**, separate from \(t=12\) numerical control | **OPEN** independent microlocal cutoffs/reflection/remainder proof review; no unqualified theorem promotion |
| F9 | \`ads5CompactTTMatterActionRealization\`; \`ads5MovingModeStabilityAndBackreaction\`; \`cylinderDoubledDiscPerturbedBulkAndRetardedGreen\` | no new physical generating action or coupled dynamics in this round | **OPEN** |
| F10 | \`ads5PhysicalScaleSourceDetectorComparison\` | horizon and source supports in dimensionless units | **OPEN** physical epoch/AdS length/band, source and detector delays, constraints |
| F11 | \`braneBulkOriginalAnalyticAgdaKernel\`; \`ads5OriginalSourceToObservationSemanticWeld\` | new Agda conditional/finite-poly source owners imported by KSW rollup | **OPEN** pinned Agda 2.9 kernel, continuum proof and semantic detector |
| D1 | \`physicalGravitonObservation\` | none | **OPEN** independent physical measurements |

**Local acceptance:** the consolidated \`scripts/check_ksw668_f8_maxcut.sh --smoke\` now runs **134 distinct source-equivalent unit tests** (previous 111 + 7 prepotential + 16 multipole) via Python test discovery, without duplicated invocations. Those 134 tests were independently run locally and passed. The extra exploratory radial-prepotential simulator has 13 local tests but is **not included** in the committed 134-case runner. Exact GitHub-head checkout and pinned Agda 2.9 were not executed and must remain OPEN. \`--legacy-full\` checks the older Fourier source-to-Weyl solver and \`--multipole-full\` checks the new three-observable solver; \`--full\` runs both and fails closed when either does.

**Scientific status:** genuine original tensor wave source and receiver calculations are materially advanced, but numerical nonzero early Weyl has NOT been established, source-to-observation calibrated dynamics are NOT built, and no five-dimensional causal violation or free-energy claim follows from these results.
