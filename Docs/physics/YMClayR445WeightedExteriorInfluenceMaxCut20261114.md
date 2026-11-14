# R445 weighted exterior influence: exact finite lemma and physical maximum cut (14 Nov 2026)

## Purpose / ownership

PR #1503; original F19/P0/R445 Wilson effective vs *renormalized target*.
This file strengthens the generic same-carrier conditional mixture comparison in
`Docs/physics/YMClayR445OriginalLocalizedTVCorrectedMaxCut20261114.md`.
It does **not** instantiate a physical Wilson conditional influence bound.

## Exact theorem (finite probability spaces)

Let `P,Q>0` be laws on the same finite `X × Y`. Write `P_Y,Q_Y` for
exterior marginals and `K_P(x|y),K_Q(x|y)` for their conditional kernels.
Define `A = Σ_y P_Y(y) TV(K_P(·|y),K_Q(·|y))`.

For **every** coupling `π ∈ Couplings(P_Y,Q_Y)`,

`TV(P_X,Q_X) ≤ A + E_π[TV(K_Q(·|Y),K_Q(·|Y'))]`. (I)

*Proof.* Insert `M_X=Σ_y P_Y(y)K_Q(·|y)` and triangle-inequality split
`TV(P_X,Q_X) ≤ TV(P_X,M_X)+TV(M_X,Q_X)`. The first term is at most
`Σ_y P_Y(y) TV(K_P(·|y),K_Q(·|y))`. Represent the second as
`Σ_(y,y') π(y,y') [K_Q(·|y)-K_Q(·|y')]` and use convexity of TV.
No assumption of independence or boundary decorrelation is used. QED.

Let `κ_Q = sup_(y,y') TV(K_Q(·|y),K_Q(·|y'))`; choose a maximal coupling
so that `π(Y≠Y')=TV(P_Y,Q_Y)`. Then (I) gives the improved Dobrushin
contraction bound

`TV(P_X,Q_X) ≤ A + κ_Q TV(P_Y,Q_Y)`. (II)

This improves the existing coefficient 1, but `κ_Q` may still be too
large when the whole exterior is perturbed.

### Site-resolved, spatially sensitive theorem

For `Y=Π_{i=1}^n Y_i` with a fixed coordinate order, define

`c_i(X)=sup{TV(K_Q(·|y),K_Q(·|y')): y_j=y'_j for all j≠i}`.

By successively replacing coordinates that differ in `y,y'`,
`TV(K_Q(·|y),K_Q(·|y')) ≤ Σ_i c_i(X) 1_{y_i≠y'_i}`.
Thus (I) yields, for **every** exterior coupling,

`TV(P_X,Q_X) ≤ A + Σ_i c_i(X) π(Y_i≠Y'_i)`. (III)

Infimizing the RHS over `π` is legitimate. It is **not** generally
valid to replace each mismatch probability separately by its individual
infimum and retain the sum: one coupling need not optimize all coordinates.
This weighted form can remain small despite almost maximal full exterior TV
if differences occur where the conditional influence vanishes.

## Reproducible exact regression

`python3 scripts/check_ym_r445_weighted_exterior_influence.py`

Independent exact `Fraction` arithmetic checks (II) on 6,561 pairs of
strictly positive 2×2 rational laws; 5,906 cases have `κ_Q<1` and
nonzero exterior TV. A two-exterior-site positive example has

- `TV(P_Y,Q_Y)=49/50`;
- `κ_Q=1/2`, hence coarse bound `49/100`;
- identical local conditional kernels, exterior changes only at far site;
- `c_near=1/2, c_far=0` with a coupling preserving the near site;
- actual local `TV(P_X,Q_X)=0`, and weighted RHS (III) is **0**.

This is a concrete reason to estimate *where* the Wilson target changes
its exterior law rather than estimate the huge total exterior TV.

## Original physical A/B/C gates, not discharged by this lemma

A: `originalR445F19P0LocalizedMarginalSameSource`,
`originalR445TargetCountertermNormalizedDensity`,
`originalR445PhysicalConditionalKernelDisintegration`.

B1: `originalR445ActualConditionalKernelTVUniform`:
`sup_boundary TV(K_P^X(·|y),K_Q^X(·|y)) ≤ a_k(X)`
on the **same** actual blocked effective and renormalized target.

B2: `originalR445PhysicalExteriorInfluenceSiteBound`:
`c_{k,i}(X) ≤ C_X exp(-μ dist(i,X))` (or source-specific summable
polymer bound), uniformly over original cutoff, boundary and volume.
This must NOT be obtained by assuming the target D1 mass-gap conclusion.

B3: `originalR445ExteriorDisagreementCoupling`: construct a coupling
of the *actual* exterior source laws with
`Σ_i c_{k,i}(X) π(Y_i≠Y'_i) ≤ b_k(X)`.

B4: `originalR445ActualLocalizedEffectiveTargetTVBound`: apply (III)
to derive `D_k^X ≤ a_k(X)+b_k(X)`.

B5: `originalR445LocalTVCutoffUniformSummable`:
`Σ_k (a_k(X)+b_k(X))<∞` with uniform physical constants. Only then
reuse the original F,G,FG three-moment and OS/RG machinery. Independent
projective consistency, reflection positivity, clustering and E1/D1/D2
remain separate obligations.

This is a mathematical finite lemma, checked computationally on stated
finite carriers. It is **not** a kernel proof of a physical estimate,
and must not be labeled as the Yang–Mills mass gap.
