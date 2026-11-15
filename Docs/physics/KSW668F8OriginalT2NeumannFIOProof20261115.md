# KSW668 F8: original moving-AdS5 Neumann-to-Weyl causal lens — theorem-application proof

**Scope:** a mathematical result about the **linear tensor PDE with prescribed smooth conserved TT boundary anisotropic stress** on the *original* five-dimensional Poincaré AdS spacetime with flat three-space FRW brane `a(t)=t`. This is **not** a generated brane matter action, nonlinear self-consistency, Agda kernel acceptance, or an empirical gravitational shortcut.

## Imported authority and exactly defined source problem

The input theorem is Plamen Stefanov & Yang Yang, *The inverse problem for the Dirichlet-to-Neumann map on Lorentzian manifolds*, *Analysis & PDE* **11** (2018), 1381–1414, DOI `10.2140/apde.2018.11.1381`, Theorems 3.1 and 4.2, especially §§3–4 and Proposition 4.1. Their work defines the local outgoing DN operator **microlocally modulo smoothing**, proves it is elliptic pseudodifferential of order 1 at timelike boundary covectors, and proves the non-glancing, first-return DN map is an **elliptic FIO of order 1** on the null lens relation. It explicitly permits **spacetime dimension 1+n with n≥2**, and points out that its local arguments do not need a global PDE existence proof. Complementary actual globally retarded smooth Neumann existence is available via Ginoux–Murro (2022) and the KSW compact boundary-data lift.

For the ORIGINAL 5D metric `g5=z^-2(-dT²+dz²+dx_1²+dx_2²+dx_3²)`, physical domain `z≥b(T)`, the original brane has `b=1/t`, `dT/dt=sqrt(1+t²)/t²`, and `v=b'=-1/sqrt(1+t²)`; the dimensionless tensor PDE is precisely `Box_g5 H_ij=0`. For the tensor Israel channel the physical Neumann source is `n·∂H_ij=-6 pi_ij^TT` (with a fixed inward/outward orientation; sign convention only changes the nonzero overall factor).

The finite source is constructed by the **local fourth-order TT operator** `S_TT[phi] = [P_i^k P_j^l - (P_ij/2)P^kl]Q_kl phi` where `P_ij=-delta_ij Delta+∂_i∂_j`, `Q=diag(0,1,-1)`. It is smooth, compactly supported, divergence-free, tracefree and nonzero on a spatial wave direction along `x_1`. Multiply by a compact smooth temporal drive, vanishing near initial time, so the mixed FRW perturbative brane stress is background-covariantly conserved. It is a prescribed stress, not the stress obtained from an action.

## Hypothesis audit at the original receiver — no change of geometry

Select original source onset `t=1`, original receiver **exactly** `t=2` at comoving `r=r_g(2)=0.697797781099381`. Choose the source spatial ball radius `epsilon=0.001`, temporal support interior point `T_e-T(1)=0.0002`, corresponding to `t_e≈1.000141436357416`, `x_e≈0.00014471324980684235` strictly inside the source ball. The **entire source** is brane-photon-dark at that receiver: `r_g(2)-epsilon-log(2)=0.003650600539435688>0`.

On the conformally Minkowski direct bulk-null chord, `z_line(T)` lies strictly above `b(T)` except at the two endpoints because `b''(T)>0`; the ray has no earlier boundary intersection and meets both endpoint boundary patches transversely, with outward normal principal factors `+0.17622301193802767` and `-0.07558371447219975` in the declared phase normalization. The boundary is uniformly timelike (`1-v²≥1/2` on `1≤t≤2`) and **strictly outward null-convex** `kappa(L,L)=t³/(1+t²)^(3/2)>0`. Along this fixed unique chord, the AdS constant-curvature screen Jacobi tidal term is zero; the direct lens canonical graph is locally smooth and nondegenerate. There are no competing direct/first-reflection rays at the exact earliest null-chord event: a broken null path between fixed source and receiver points has strictly greater Minkowski optical length unless it coincides with the straight chord.

At each endpoint, the null covector's **tangential boundary projection is timelike** because the normal symbol is nonzero, exactly the microlocal elliptic region of Stefanov–Yang's Theorem 3.1. All hypotheses for their local outgoing DN and first-return lens FIO are therefore identified on small conic source and receiver neighborhoods. The original Poincaré radial domain is noncompact, but all constructions are microlocal along a finite compact chord, where it can be embedded in a smooth compactly extended globally hyperbolic boundary domain without changing the retarded solution by finite propagation speed.

## Exact causal two-patch operator inversion (reuse DASHI Balaban finite Neumann)

Microlocally at the selected emission patch E and later receiving patch R, decompose the causal outgoing **Dirichlet-to-Neumann** map (modulo smoothing off the specified canonical relation):

```
   [g_e]   [D_e    0 ] [f_e]
   [g_r] = [ F_re  D_r] [f_r]
```

Here `D_e` and `D_r` are elliptic local outgoing order-1 pseudodifferential DN maps, while `F_re` is the elliptic first-return order-1 lens FIO. The **upper-right** block is zero by retarded time ordering. `f` is the boundary Dirichlet trace and `g` is the outward Neumann input. The physical experiment prescribes `g_e` and `g_r=0`. Let `E_e=D_e^-1`, `E_r=D_r^-1` be local order −1 microlocal parametrices. The exact **noncommutative** inverse block algebra is

```
 A=[[D_e,0],[F_re,D_r]]
 G0=diag(E_e,E_r)
 R=I-A*G0=[[0,0],[-F_re*E_e,0]]
 R**2=0
 G=G0*(I+R)=[[E_e,0],[-E_r*F_re*E_e,E_r]]
 A*G=G*A=I (modulo smoothing / parametrix inverse errors)
```

The finite residual `R²=0` is the **exact depth-two** case of the repository's already verified `BalabanFiniteNeumannParametrix.finiteRightNeumannExactAtDepth`; there is **no contraction estimate or limit** required. It differs from freezing the stationary `K2/K1` radial resolvent: the latter *does* require high-Laplace-frequency contraction and fails for low frequencies, as the separate new counterexample proves.

Therefore the actual **off-diagonal Neumann-to-Dirichlet** microlocal map is

`ND_{r<-e}= - E_r ◦ F_re ◦ E_e` modulo smoothing/FIO-lower-order errors. Its canonical relation is the **same original first-return null chord** and its principal symbol is the product of three nonzero symbols, so it is an **elliptic order −1 FIO** on that branch. None of the three operator factors is commuted or omitted. This is an application of Stefanov–Yang 2018 Thms. 3.1/4.2 plus exact finite noncommutative block algebra.

## Source-to-Weyl nonzero symbol and smooth compact existential witness

Compose `ND_{r<-e}` with the actual local fourth-order source `S_TT` on the **emitting boundary** and with the *two distinct* electric Weyl readouts at the receiving boundary. The compact source has a nonvanishing `yy` TT principal symbol along the selected spatial-x direction. The **intrinsic 4D electric Weyl** differential principal symbol is nonzero (verified factor `0.0840263224215478`), and the **SMS projected 5D electric Weyl** principal symbol at the source-free receiver is nonzero (factor `0.002856448946707509`), as separately checked with the sign-correct linearized SMS equation. Each readout has differential order 2, giving the composite order `(4 - 4 normalisation) + (-1) + 2 = +1` on high-frequency input.

Take an actual *real* spatially and temporally compact oscillatory packet `phi_lambda = chi(T,x) cos(lambda*(-T+s*b(T)+k_x*x)+theta)`, with `chi` smooth, positive near the emission interior point, and with source `pi_lambda=lambda^-4 S_TT[phi_lambda]`. Smooth compact support and exact TT/conservation hold **for every finite lambda**; the amplitude remains nonzero on the chosen branch. Ellipticity of the composed first-return lens FIO means its response is of the form `lambda*c(T_r,x_r)*cos(lambda*psi(T_r,x_r)+theta+theta_0)+O(1)` for the differentiated Weyl readout, **with nonzero principal coefficient** `c`. Selecting `theta` avoids a zero real cosine; choosing a sufficiently large *finite* `lambda` prevents the lower-order and smoothing remainder from cancelling its leading amplitude. The same packet's two Weyl readouts have nonzero leading coefficients at the *same* receiver, and a generic phase can avoid zeros in both simultaneously. The retarded solution exists by the Neumann IBVP theorem, and the explicit KSW compact lifting + tangential multiplier yields a weighted finite-energy bound for every fixed lambda. Finally scale the entire source by a nonzero arbitrarily small multiplier to stay in the linear regime; nonvanishing persists.

**Result at the mathematical paper-theorem-application level:** for the *prescribed smooth compact conserved TT source* on the original moving AdS5 background, there exists an actual retarded, finite-energy linear tensor response with **nonzero intrinsic and projected Weyl curvature before the brane-confined photon** at that original receiver. The proof imports the published general-dimensional microlocal ellipticity theorem. It is neither an explicit numerical waveform nor an independently Agda-kernel-certified continuum theorem; further peer/referee audit should check the extension and tensor perturbation gauge convention.

**Not inferred:** a matter action producing that stress, complete nonlinear Einstein/Israel solution with all channels, actual receiver electronics, physically realistic AdS radius, experimentally measurable superluminality, free energy, CTC or independent physical observation.

## Cross-domain Neumann inventory and separate negative control

- `DASHI/Physics/YangMills/BalabanFiniteNeumannParametrix.agda`: exact `A(G_n)=I-R^n` algebra (used directly at n=2).
- `BalabanWeightedNeumannRemainder.agda`, `BalabanGeometricNeumannClosure.agda`: only relevant if the physical inverse residual is *not* nilpotent and an actual weighted contraction is known.
- `KSW668AdS5LinearIsraelTTRationalSliceExact.agda`: physical sourced tensor boundary and no invented Robin term.
- `KSW668AdS5MovingNeumannCharacteristicRationalExact.agda`: rational t=4/3 actual incoming/outgoing characteristic reflection beta=1/4, exact sourced g, source-level Agda (kernel unrun).
- `KSW668AdS5FrozenNeumannSeriesReuseExact.agda`: generic imported Balaban finite, weighted, and n=2 exact nilpotent consequence, source-level Agda (kernel unrun).
- Frozen stationary `K2/K1` used on the original oblique boundary: residual `R=-v*s*Z_b(q)` satisfies `|R|<(1+4/s)/sqrt(2)<1` for *real s>=16* uniformly in t∈[1,2], all |k|>=0; at t=1,s=0.05,k=0, |R|≈28.3949>1 and the series diverges. This is not a contradictory statement: the **causal two-patch** residual is algebraically nilpotent after microlocal diagonalization, whereas the **frozen resolvent** is a different approximate inverse.
- `KSW668F8` PDE code's compact 3D Fourier/Weyl reconstruction remains numerically **unconverged** (48.4% field / 83.0% curvature last-pair drift); an external theorem-based *existential* argument does **not** turn that failure into a numerical acceptance receipt.

## Remaining actual gates after this mathematical theorem application

F8.1 full linear **microlocal theorem**: theorem application/proof above at mathematical level, not Agda or explicit Green kernel; mathematical case can be reviewed and tested independently. F8.2 existential compact TT early Weyl: paper-theorem-application level, not Agda/experiment. F8.3 **quantitative converged numerical signal** still OPEN. F9.1 physical generating matter action OPEN. F9.2 all-mode stability/backreaction OPEN. F9.3 other doubled-disc cylinder coupled gravity OPEN. F10 physical calibration/source/detector OPEN. F11 continuum Agda kernel OPEN. F11 source-to-observation semantic weld OPEN. D1 independent physical observation OPEN.

**Caveat to the proof ledger:** no bounded-operator norm, explicit global amplitude, microscopic brane source or measurement is provided by the FIO theorem. Acceptance levels must remain distinct: `external mathematical theorem applied` versus `Agda kernel verified` versus `3D numerically converged` versus `physical observation`.


**2026-11-15 phase-matching correction:** The spatial-temporal oscillatory source phase must be the restriction of the ORIGINAL interior null covector onto the MOVING emitting boundary: `Phi|_brane(T,x)=-T+s*b(T)+k_x*x`, where `s=Delta z/Delta T` for the chosen direct ray and `s²+k_x²=1`. Omitting `s*b(T)` would prepare the wrong tangential covector and would not license the original-ray FIO conclusion. All FIO, Agda and physical promotion boundaries remain unchanged.