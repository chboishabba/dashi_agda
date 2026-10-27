# Charged KK circle: Wilson, radion, metastability, chirality, slow rotation (2026-10-24)

## Scope and original source authority

This is a **source-specific five-dimensional effective field theory**, extending the earlier gravitational Casimir radion candidate in PR #1241. The direct same-physics paper is:

- Yugo Abe, Takeo Inami, Yoshiharu Kawamura, Yoji Koyama, *Radion stabilization in the presence of Wilson line phase*, PTEP 2014 073B04 (2014), DOI **10.1093/ptep/ptu097**, arXiv:1404.5125. It computes the joint radion/Wilson loop Casimir potential for flat 5D gravity + U(1) with charged and neutral fermions, including the physical gauge/graviton ghost-counted mode multiplicities. We do **not** claim to have discovered this physical mechanism.
- Rubin and Roth, Phys. Lett. B 127 (1983) 55–60, DOI 10.1016/0370-2693(83)91629-5, classical massive-fermion KK radius stabilisation.
- Standard S1 fermion chirality failure and S1/Z2 orbifold projection, see e.g. Scherk–Schwarz orbifolds at the LHC, Phys. Rev. D 100 (2019) 075016, DOI 10.1103/PhysRevD.100.075016; Georgi, Grant and Hailu, Phys. Rev. D 63 (2001) 064027, DOI 10.1103/PhysRevD.63.064027.
- The existing DASHI source-facing KK action/reduction is PR #1239, and the observable/steelman consumer is PR #1241. **PR #1244 Alexander horns is unrelated to this physical critical path**.

## One candidate-specific action / fields

Five-dimensional Einstein-Hilbert action, a tuned renormalised bulk cosmological term, one independent U(1) Maxwell action, one periodic neutral real massless scalar, three periodic neutral 5D Dirac fermions with common positive bulk mass mN, and one periodic 5D Dirac fermion of independent Maxwell charge qB=1 with bulk mass mQ=4mN. Matter and gravity are expanded around Minkowski4 x S1 with no classical condensate. The 5D spinor content is **vectorlike**.

The physical photon **B_mu**, zero mode of the independent U(1) Maxwell field, is distinct from the KK graviphoton **g_mu5**, and its gauge invariance is unbroken by a constant Wilson phase. The Wilson phase theta = e5 * contour_integral(B5) is a physical periodic scalar. It is not the KK radion, a classical Higgs field, nor a Stueckelberg winding condensate.

Let b0>0 be the radius, x=b/b0, z=2*pi*mN*b0, k=mQ/mN=4. Define

f(z,theta) = [sum_{n>=1} exp(-nz) * (1+nz+(nz)^2/3) * cos(n theta)/n^5] / zeta(5).

For the chosen one-loop free spectrum the Einstein-frame potential is

U(x,theta)=ell/x + [-9 + 12 f(z*x,0) + 4 f(k*z*x,theta)]/x^6,

V_E=c0/b0^4 * U, c0=3*zeta(5)/(64*pi^6).

The coefficients -9, +12 and +4 count respectively 5D graviton(5), Maxwell(3), scalar(1); three 5D Dirac fermions(3*4); and a charged Dirac fermion(4). The bulk term ell is tuned to obtain a 4D Minkowski stationary point; this is a cosmological counterterm, not a prediction of vanishing observed cosmological constant.

## Concrete joint solution, including its failure witnesses

Executable: `python3 scripts/check_kk_charged_wilson_bidi.py`. The 180-term high-precision periodic Casimir series agrees with independent mpmath numerical derivative calculations.

At k=4 a local 4D Minkowski stationary point exists at
- z=**1.6025140734913201**; kz=**6.410056293965281**;
- theta=**pi**;
- ell=**0.955826013027045**;
- U_xx=**16.490381877279744 > 0**;
- U_theta_theta=**0.13383881477844324 > 0**;
- U_x_theta=0 at the exact periodic phase pi.

The Wilson minimum is not merely sampled numerically. When kz>6 the first sine harmonic dominates all higher harmonic derivatives: `|sin(n theta)|<=n sin(theta)` for 0<theta<pi, and the positive first harmonic exceeds the bound `sum_{n>=2} n^2 a_n`. An explicitly evaluated geometric-series upper bound on the latter/first ratio is **0.00536523<1**. Therefore U(x=1,theta) strictly decreases for 0<theta<pi and pi is the unique global Wilson phase minimum modulo 2pi **at the selected radius**.

A second flat stationary root at z approx **0.490783** exists only if ell is independently retuned at that root. Its U_xx is **negative**, i.e. it is not another stable vacuum of the SAME tuned potential. The stationary roots meet in a saddle-node at **kcrit approx 3.012656125** with z approx **1.06135444**, under the same declared spectrum; this is a numerical local bifurcation result, not an all-k analytic exclusion theorem.

**Important global instability:** at fixed theta=pi and x ->0, f(zx,0)->1 and f(kzx,pi)->-15/16, so the leading x^-6 coefficient is `-9+12+4*(-15/16)=-3/4`. Thus `U(x,pi)->-infinity`: the vacuum is **metastable at best**, NOT a globally stable circle compactification. With ell fixed at the local stable vacuum, a shrinking-circle potential barrier occurs near **x=0.296345014** with `U approx 260.018874` dimensionless. This barrier is distinct from the *separately retuned* lower flat stationary root. No Coleman–De Luccia bounce, nonperturbative completion or vacuum lifetime is supplied, and one-loop semiclassical physics eventually fails in the collapse region.

## Explicit physical scale, not experimental inference

At illustrative b0=10^-24 m and reduced Planck scale MPl=2.435e18 GeV:
- radion Compton range ≈**5.234166054e-13 m** (radion mass 0.00037699794 GeV);
- Wilson scalar Compton range ≈**2.020441228e-22 m** (canonical Wilson mass ≈9.7665291e5 GeV);
- neutral bulk mass ≈**5.0327859e7 GeV**, charged bulk mass ≈**2.0131144e8 GeV**;
- due to Wilson theta=pi, lightest charged four-dimensional mode has KK momentum shifted by **1/(2 b0)** and mass ≈**2.241891574e8 GeV**;
- b0*M5 ≈**2.893888e6** in the stated convention, within the semiclassical-radius regime.

The Wilson scalar canonical normalisation for theta=e5 contour B5, physical e4=e5/sqrt(2pi b0), is `f_theta=1/(2pi b0 e4)`, with mass squared `m_theta^2=(c0/b0^4)*U_theta_theta/f_theta^2`.

This is NOT a model of the electron. No light charged matter, no chiral Standard Model, no fit of collider precision data or observed vacuum energy is established. The separate Maxwell vector itself remains massless by gauge symmetry, but all these stronger physical claims need more.

## Chirality consumer: actual compactification obstruction

`scripts/check_kk_chiral_slow_spin_consumer.py` records separate constraints:
- Smooth periodic S1 with a free 5D Dirac spinor has one 4D left and one 4D right zero-mode component: net chiral index 0, including under ordinary constant Wilson phases.
- S1/Z2 orbifolding can select a left OR right zero mode with a spinor parity, but the geometric KK graviphoton g_mu5 is odd and its zero mode is **removed**; the independent Maxwell B_mu can be even and retained; B5 Wilson-line zero mode is odd and also removed.
- A constant 5D Dirac bulk mass for that chirality-projected field is odd under the simple orbifold spinor parity, so obtaining a massive chiral sector changes the source action/boundary conditions (e.g. a kink mass or additional fields).

**BIDI consequence:** the orbifold may repair the chirality consumer but cannot inherit the periodic-circle graviphoton/Wilson potential without rederivation. This is a genuine source-specific transport failure, not evidence for new physics from horns, C3 or 369 notation.

## First-order rotating-source consumer

The same script tests the leading scalar-tensor gravity power counting:
- In the Einstein frame the radion has no independent *vector* source at first gravitational order for a static spherical profile, while its stress enters the tensor equation quadratically.
- For a fixed physical tensor momentum source, the linear gravitomagnetic component g_E,0i is the GR one at order GJ.
- The Jordan conformal relation `gJ=A(varphi)^2*gE`, with scalar perturbation O(GM), shifts gJ,0i by O(G^2 M J) relative to gE,0i. Therefore the **leading** spin metric is GR at fixed bare tensor coupling and source, and the scalar influence at macroscopic altitude is exponentially suppressed for this microscopic radion range.
- At an altitude 100 km, the Yukawa e^(-altitude/lambda_rad) logarithm is approximately -8.3e16 in base 10. This is a mathematical suppression estimate, not a computed LARES-2 orbit, a complete PN calculation, a full 5D rotating fluid or a measured bound.

## Status / acceptance

`python3 scripts/check_kk_charged_wilson_bidi.py`
`python3 scripts/check_kk_chiral_slow_spin_consumer.py`

Local independent execution of the mathematical scripts passed. GitHub source is committed. Exact-head Agda kernel, nonlinear 5D source matching, full charged Standard Model, chirality and metastability lifetime remain OPEN. This cut uses the native BIDI/steelman machinery from PR #1241 and no new generic factorisation layer.
