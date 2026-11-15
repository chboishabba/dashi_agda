# R445: original Wilson effective/bare TV — sharp likelihood-ratio maximum cut

14 November 2026. Stacked original physical Wilson F19/P0 PR #1503, source #1444. The source objects are exactly:
- `YMClayE1A3OriginalR445CrossCutoffSourceExact.originalR445EffectiveCoarseExpectation` — pushforward of the **actual** 1024-link fine Gibbs law through the SU(N) block map, coupling beta(3)
- `YMClayE1A3OriginalR445CrossCutoffSourceExact.originalE1BareCoarseExpectation` — **different** 2^4 coarse bare Wilson Gibbs law at beta(1)
- `YMClayE1D1OriginalR445BoundedMomentMajorantsExact` — bounded, complement-stable original F,G,FG coarse tests
- `YMClayE1D1OriginalR445QuantitativeThreeMomentRGCutExact` — original 3-moment covariance error <= sum of three bounded moment errors
- original #1498 Wilson/FP/Haar P0 sources and `YMClayOriginalWilsonPhysicalF19PartitionExact` — physical source definitions, not a proved RG density approximation

## New exact finite measure theorem (analytically proved, not Agda-accepted)

Let X be one actual finite coarse SU(N) configuration carrier, with normalized probabilities `Q(x)>0` and `P(x)=s(x)Q(x)/Z`, `Z=E_Q[s]`, and positive ratio `m<=s(x)<=M`.

Then for every same-carrier test `0<=F<=1`,
`|E_P[F]-E_Q[F]|<=D` where

```
  D = TV(P,Q) = E_Q[(s-Z)_+]/Z.
```

The convex chord bound on `(s-Z)_+`, for `s in [m,M]`, gives

```
  D <= (Z-m)(M-Z)/(Z(M-m)).
```

Writing `u=√m,v=√M`, AM–GM `Z+mM/Z>=2√(mM)` yields the **sharp** bound

```
  D <= (√M-√m)/(√M+√m).
```

Equality occurs for the two-state source `m=1/4`, `M=4`,
`Q=(4/5,1/5)`, `P=(1/5,4/5)`, `Z=1`, `D=3/5`.

If the original coarse weights on the **same Haar reference** are `wP=exp(-S_eff)`, `wQ=exp(-S_target)` and the action difference `Delta=S_eff-S_target` obeys `osc_X Delta <= R`, then
`M/m<=exp(R)`, hence

```
  D <= tanh(R/4).
```

This is sharper than independently bounding each signed F,G,FG error. Existing product complement gives all 3 differences <= D and covariance <= 3D.

## Critical volume/cutoff counterexample

An absolute plaquette-local `O(1)` bound on `Delta` **per plaquette** allows total action oscillation `O(|Lambda|)`. It cannot establish `D_k->0` uniformly in infinite volume.

Indeed tensor powers of the sharp two-state pair have

```
  P=(1/5,4/5), Q=(4/5,1/5).
```

Their exact product-measure total variation rises from `3/5` at volume one to `30258804339/30517578125 > 99/100` at volume 16. This is a **mathematically valid obstruction to the naive volume-uniform TOTAL TV strategy**, not to Yang–Mills itself: local/projective test-marginal TV, coupled conditional kernels, a renormalized reference action or Dobrushin/cluster locality may still control the original finite-source F,G,FG moments without full-volume TV vanishing.

## Exact next original-source theorem

Prove **either**:
1. `originalR445PhysicalRelevantMarginalTV(k, F,G) <= epsilon_k` for the selected original bounded local coarse tests, with summable cutoff error, on the **renormalized effective family**; or
2. actual local absolute continuity + source bound on an appropriately restricted coarse observation algebra, preserving exact F,G,FG and the original Wilson-F19 Haar normalizations; or
3. direct original interacting marked covariance bounds bypassing full TV.

It is **not enough** to assert `|S_eff-S_bare|<=constant` per plaquette, or to identify the renormalized effective and bare laws.

## Reproduce

```sh
python3 scripts/check_ym_r445_action_oscillation_tv.py
```

361 rational examples; exact sharp two-point saturation; exact volume tensor counterexample through 16 factors. The theorem is finite probability arithmetic, source-donor test **not** an Agda 2.9 kernel certificate or a physical uniform moment estimate. E1/D1/D2 and YM Clay remain OPEN.
