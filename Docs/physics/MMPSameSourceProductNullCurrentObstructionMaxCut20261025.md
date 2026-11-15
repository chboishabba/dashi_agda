# MMP P1/P2 max-cut: one-source product obstruction and warped radial null identity (2026-10-25)

**Status:** a restricted analytic rejection result, NOT construction/nonexistence proof of an actual MMP wormhole.
**Owner:** Agda draft [PR #1248](https://github.com/chboishabba/dashi_agda/pull/1248), existing same-state optical loop, charged-Dirac Cauchy and Einstein/Maxwell donors.
**Executable acceptance:** `python3 scripts/check_mmp_product_same_source_einstein_maxwell_obstruction_20261025.py` and `python3 scripts/check_mmp_warped_null_curvature_identity_20261025.py`. Independently developed expanded local analogues executed and passed (2026-10-25); no exact committed-head runner or proof-assistant kernel receipt claimed for these new scripts.

## Original source attribution and native reuse

- **Maldacena, Milekhin, Popov**: original *Traversable wormholes in four dimensions*, arXiv:1807.04726 (2018 preprint); *Classical and Quantum Gravity* 40 155016 (2023 journal), DOI 10.1088/1361-6382/acde30. Their charged massless fermions, magnetic return paths and long nonconstant geometry are **not** this ultra-simple product.
- The renormalized massless 1+1D complex-Dirac circle / Bernoulli-Casimir energy and Polyakov stress belong to established QFT; the existing DASHI `scripts/check_global_dirac_optical_circle_source_20261024.py` is our already-implemented specific same-functional reduced application. In this new check we take its **fixed-phase constant-lapse** limit; we do not recalculate or claim original authorship for the general theorem.
- **Zahn**, *The renormalized locally covariant Dirac field*, arXiv:1210.4031 (2012 preprint; 2014 published): original source for locally covariant charged-Dirac current/stress Wick-renormalization and finite ambiguities. Nothing about our particular product state is a full application of Zahn's subtraction.
- Native formal owners: `DASHI/Physics/QFT/MMPWilsonHadamardSameBackgroundBidiExact.agda` (Hadamard difference, Wilson, source boundaries), `DASHI/Physics/QFT/MMPDiracCauchyNoncompactCompactDoubleBidiExact.agda` (conditional Cauchy), `DASHI/Physics/YangMills/CompactLieLatticeGauge.agda` (Wilson gauge covariance), `DASHI/Promotion/MaxwellFiniteExteriorChainStrengthening.agda` (finite Bianchi, sourced Maxwell **unpaid**), `DASHI/Physics/GR/EinsteinTensor.agda` (Einstein algebra; matter source unfinished), and existing MMP optical-circle/same-action numerical donors.
- We repaired four INVALID `//` lines in the Hadamard bridge to valid Agda `--` comments, retaining unchanged theorem statements. This is a parser correction only; it is **not** an Agda kernel receipt.

## Hypotheses, geometry and exact same-source identity

The **restricted comparison manifold** is an ultrastatic direct product:
```text
ds² = -dt² + dx² + R²(dtheta² + sin²theta dphi²),
x periodic of circumference L, R>0.
F_theta,phi = q sin(theta)/(2e), q integer not zero.
```

This geometry is compact spatial `S1 x S2`, **not** the one-ended `(S1 x S2) minus a point` required by the same-universe handle construction. We include only (i) a classical purely magnetic Maxwell stress with coupling normalization `B=q/(2e R²)`; and (ii) `c |q|` ideal *massless LLL* complex Dirac circle species, with Wilson/spin phase `alpha in (0,1)` and selected renormalized optical energy `E_LLL=(2 pi c |q|/L) B2(alpha)`. The coefficient `c>0` is fixed by the selected reduced theory. No higher spherical tower, thermal matter, independent shell, nonlocal curved fermion state, finite local counterterm, or dynamic three-plasma source is added.

```text
B2(alpha)=alpha²-alpha+1/6.
E_EM=pi L q²/(2 e² R²).
V=4 pi R² L.
rho=E/V,
p_x= -(1/(4 pi R²)) * partial_L E,
p_perp= -(1/(8 pi R L)) * partial_R E.
```

Both fermionic and Maxwell stress components are derived by differentiating ONE total stationary energy `E_LLL+E_EM`, not by fitting pressures:
```text
rho_LLL = c |q| B2(alpha)/(2 R² L²),    p_x,LLL = rho_LLL,    p_perp,LLL = 0
rho_EM  = q²/(8 e² R^4),                  p_x,EM = -rho_EM,    p_perp,EM = rho_EM
```

The global Wilson phase is `theta_W=2 pi (alpha-spin_phase)` on a smooth spectral branch. The SAME energy produces persistent current via `partial_theta_W E`:
```text
J^x = [partial_theta_W E]/(4 pi R²)
    = c |q| (2 alpha - 1)/(4 pi R² L).
```
The sign convention is selected by whether matter action uses `+J A` or `-J A`; its **vanishing/nonvanishing** is convention-independent. A purely static monopole magnetic Maxwell tensor on this product has zero electric/Ampere source in the x direction, hence requires `J^x=0`.

The product Ricci tensor is zero in the flat time/circle directions and `Ric_S2=g_S2/R²`. Therefore
```text
G_tt=1/R², G_xx=-1/R², G_theta,theta=G_phi,phi=0
G_kk = G_tt + G_xx = 0 (k=unit timelike + unit circle spatial).
rho_EM+p_x,EM=0,  rho_LLL+p_x,LLL=2 rho_LLL.
```
Einstein `G+Lambda*g=8 pi G_N(T_EM+T_LLL)` gives **necessary** radial-null equation `0=16 pi G_N rho_LLL`. Thus for fixed `G_N>0,c>0,|q|>0` it requires `B2(alpha)=0`. Meanwhile the static purely magnetic Maxwell current equation requires `B2'(alpha)=0`, hence `alpha=1/2`; but `B2(1/2)=-1/12 !=0`. The resultant of `B2` and `B2'` is nonzero. At spectral-flow cusp `alpha mod 1 = 0`, one-sided derivatives are nonzero and cannot remove this obstruction.

**Precise bounded conclusion:** there is NO joint solution of these two **necessary** Einstein-null + Maxwell-current conditions for nonzero q and the specified isolated ideal massless LLL energy on a constant-radius ultrastatic product, even allowing a cosmological constant (which is null-contraction zero). This conclusion is not a proof of absence of a wormhole with nonconstant geometry, additional states/modes or renormalized counterterms.

## Independent curved geometry calculation

For `ds²=-N(x)²dt²+dx²+r(x)² dOmega²`, a separate coordinate-level computation constructs Christoffel symbols, Ricci, scalar and Einstein tensors, checking all off-diagonal components and recovering:

```text
G_kk = 2/r [(N'/N)r' - r''],
r'=0 => G_kk=-2 r''/r.
```

Hence at a **flaring** throat (`r''>0`), the geometric radial null Einstein component is strictly negative, consistent with the **necessary** negative null stress requirement. This is the correct geometric direction for subsequent global P1/P2 work but does NOT supply any 4D quantum state or solve a BVP. Returning to the ultrastatic product `N=1,r=R constant` gives the flat2 × sphere Einstein diagonal `(1/R²,-1/R²,0,0)`, as independently verified.

## Reproducibility and adversarial state/pressure checks

The local expanded SymPy prototype ran with q=12, L=7.2, R=3.1, e=1.2, Wilson/spin phases alpha=1/2,1/6,5/6 and a `B2=0` root, and checked that numerical centered variations of **one total energy** matched radial/angular pressures and Wilson current within `1e-9`. At alpha=1/2, current vanishes but radial LLL null stress is negative/nonzero; at a B2 root, radial null stress vanishes but current is nonzero (example `J^x≈-0.0079681` in model units). The **independent** full Christoffel/Ricci/Einstein symbolic checker also passed.

Locally validated expanded prototype SHA-256:
- `check_mmp_same_source_product_null_cut_20261025.py`: `56f9b9e330fa98ca956b1f9f4a924e8eafcd7820cbe3667f1929063bb9907878`;
- `check_mmp_warped_null_curvature_identity_20261025.py`: `b2f67efefeae9041c6f9acb849b22d4ad40624055b2fa38304a0202628897bd0`.

These hashes name **expanded local files**, not automatically the shorter same-theorem scripts committed in GitHub. Independent **exact-PR-head run remains pending**. Avoid conflating paper/original-theorem authority, this symbolic calculation, repository source-writing and kernel-certification.

## Max-cut routing after this result

1. **Retire ultrastatic constant-radius S1xS2 as an acceptable full self-consistent MMP state**, except as a controlled kinematic comparison. Reject shortcut claims that negative optical-circle energy alone solves Einstein–Maxwell.
2. **P1 top priority:** instantiate an actual one-ended globally hyperbolic magnetic-return spatial handle with metric varying across throat and exterior; choose physical spin-c bundle, Wilson loop and charged Dirac CAR Hadamard covariance on that SAME geometry. Use native Cauchy/AQFT and source-established Gérard–Stoskopf existence and Zahn renormalization, without treating their hypotheses as source-selected.
3. **P1 stress+current:** point-split same charged two-point distribution, including spin connection, spherical higher modes, state transitions, all radial/angular tensor components, local-covariant counterterms, `nabla J=0` and `nabla T=F J`; compare full current/energy obligations at EVERY radial coordinate, not only a tuned throat.
4. **P2:** solve coupled Maxwell+Einstein boundary equations with that SAME stress/current, taking existing PR effective BVP as initialization only. Include global return-line optical length fixed point, smooth source matching, mass/charge constraints, ANEC, finite reference scheme.
5. **P3/Q and physical P4:** only afterward promote the conditional two-LLL qubit and three-material-region actuator to physical accessibility/causal scattering experiments. 3D finite lattice QED precursor is not a noncompact quantum curved state.

**Nonpromotion:** This is a real analytic conditional exclusion result and an exact derived curved radial-null identity, not a globally self-consistent wormhole proof, quantum gravity result or evidence of anomalous plasma-driven gravity.
