# Original SU(2) Wilson one-link analytic bound and the bare-link UV obstruction

9 November 2026. This is a finite-lattice analytical result, NOT a solution to any Clay physical endpoint. It uses the original four-dimensional SU(2) Wilson action normalized by trace(U)/2.

Six plaquettes touch a positive oriented link U. Fix the other three-link staples V_j. Their quaternion sum S=Σ_j V_j=R V, 0≤R≤6, V∈SU(2) for R>0. The original one-link conditional density is proportional to exp(β ReTr(U S)/2). Haar rotation of UV to Q gives exp(κ t(Q))dH(Q), κ=βR and t(Q)=ReTr(Q)/2=cos θ. Normalized Haar is (2/π) sin²θ dθ.

## Positive one-link large-field estimate, from original conditional

The negative hemisphere {t≤0} has Haar mass 1/2. The cap {t≥1/2} has Haar mass 1/3−√3/(4π)>1/6, using √3<2 and π>3. Thus the one-link normalizer is ≥exp(κ/2)/6, while the numerator of P(t≤0) is ≤1/2. Consequently:

**P(t≤0 | six original staples) ≤ 3 exp(−β R/2)**.

This is a genuinely derived finite-volume-uniform SU(2) *conditional* large-field estimate, and equals 3 exp(−3β) when the six staples align (R=6). Integrating the same conditional law for any r₀>0 yields the exact original-source reduction:

**P(t(UV_staple)≤0) ≤ P(R<r₀)+3 exp(−β r₀/2)**.

The second contribution is derived. The original Wilson frustrated-staple probability P(R<r₀) is NOT yet bounded, and neither term by itself provides distant gauge-invariant covariance decay. The needed CMP116 large-field polymer estimate concerns physically localized *connecting regions*, not simply the bad link event.

## Additional original-action pointwise inequality: frustration costs Wilson energy

Let u, v₁,…,v₆ be the actual unit SU(2) quaternion coordinates of the link and its oriented staples. The original six adjacent Wilson deficits (one minus normalized real plaquette trace) sum exactly to
`D₆(u;v)=Σ(1−Re(u vⱼ))=6−<u,S>` with `S=Σvⱼ` (orientation may use conjugates to express the real trace as the Euclidean dot product). Cauchy–Schwarz for the four real quaternion coordinates gives `<u,S>≤||S||=R`. Hence the **pointwise original physical action inequality**
`D₆(u;v)≥6−R` holds for every original SU(2) link/staple configuration, with no probabilistic premise. In particular, any frustrated event `R<r₀` necessarily has `D₆>6−r₀` at the incident link.

This identifies a genuine large-field energy penalty, but **does not** establish the Gibbs probability of that event: a finite-volume lower bound on the original partition function relative to the bad set, or a local gauge-compatible surgery/polymer entropy argument, is needed. Merely exponentiating the pointwise action inequality and ignoring the integration/normalization of all neighboring links would be invalid. The missing **distance-dependent large-field polymer/bridge estimate** remains D1.03.

## UV bare-link Dobrushin limitation (not a Clay no-go)

Fix all six staples to +I versus −I; the conditional densities are exp(±6βt). The event {t>0} gives total variation ≥1−6 exp(−3β), and L¹ conditional row distance ≥2(1−6 exp(−3β)), approaching 2 with increasing β. Therefore an original *bare-link* L¹ Dobrushin contraction q<1 cannot remain uniform for every such boundary condition along a diverging-β trajectory. This says nothing against the physically blocked-cube CMP119/R445 route, nor against gauge-invariant Wilson tests: the distinguishing bare-link event is gauge variant.

An executable exact-rational certificate, scripts/check_ym_su2_wilson_singlelink_uv_influence_20261109.py, replaces exp(3β) by its fourth-order Taylor lower bound and yields at β=2 the rigorous L¹ bound 218/115>1. It was executed successfully, with Fraction arithmetic and no numerical integration.

## Trust and remaining physical source

To formalize the result on the repository's ORIGINAL Agda SU(2) source, prove the normalized SU(2) Haar conjugacy/one-link conditional identity and feasible opposite staple boundary assignment; these are not new scalar or measure postulates. More importantly, E1.03 actual Schwinger/QFT limit, D1.01/03 full Wilson small/large uniform spatial decay, D2.03/04 same-H spectral completion, N1.02 continuum noncollapse and G1.03 every compact simple group remain OPEN. One-link conditional suppression is not a complete D1 estimate, an OS gap or a continuum theory.


## 9 November additional derived bound — frustrated-staple event from ORIGINAL Wilson action expectation

This is an actual new elementary inequality for the **same original finite-volume SU(2) Wilson Gibbs measure**, not a new conditional source record. For the six original oriented staples around one positive link, use the pointwise relation already proved above:
`D₆=6-<u,S> ≥ 6-R`, where `R=||S||`.

Fix `0<r<6`. On the frustrated event `A_r={R<r}` we have `D₆>6-r>0`, so, pointwise,
`1_{A_r} ≤ D₆/(6-r)`.
Taking expectation with respect to the ORIGINAL normalized finite Wilson measure gives the exact **same-measure** reduction:

```
P_original(R<r) ≤ E_original[D₆]/(6-r)

P_original(t(UV_staple)≤0)
  ≤ E_original[D₆]/(6-r) + 3 exp(−β r/2).
```

These inequalities make **no independence, convergence, translational invariance, or RG assumptions**. The second uses the already-derived SU(2) one-link Haar conditional suppression. The probability bound may be trivial (greater than 1) until a physically useful estimate on `E[D₆]` is proved. It is NOT the spatial connecting-polymer or full-Wilson covariance estimate of D1.03.

For a translation-invariant periodic finite four-dimensional original Wilson system with `N_p` unoriented plaquettes and normalized action `S_β=β∑_p t_p`, finite-volume differentiation of the genuine Haar integral gives
`∂_β log Z=∑_p E[t_p]`. Every positive link borders six plaquettes, hence `E[D₆]=6(1-(1/N_p)∂_β log Z)`.
Writing `p(β)=(1/N_p) log Z(β)` gives the exact pressure-slope criterion

```
P_original(t≤0) ≤ 6(1−p'(β))/(6−r) + 3 exp(−β r/2).
```

This is a *reduction*, not a proof of a favorable uniform pressure derivative: the latter may depend on cutoff/volume and does not itself establish spatial covariance decay. To use this for a physical B1/D1 path, prove an actual original pressure-slope or localized polymer estimate with cutoff-uniform strength, then the **distance-dependent connected bad-region** control on the same original Gibbs measure. In particular, high-β suppression of a single *gauge-variant* bad-link event is not sufficient.

**Independent finite rational control:** `scripts/check_ym_su2_original_staple_frustration_action_20261109.py` (commit `b9783761884c2a5d43700194a95748ef2b8e4f13`) tests all 5^6 choices from five rational unit-quaternion source vectors, three rational unit-link choices and four rational thresholds: **187,500 exact rational event/action checks, including 110,010 frustrated-event cases**. Independently executed in the current task runtime. This is not an Agda-kernel check, and the inequality is proven by the analytic argument above, not by finite enumeration.

**Cross-program comparison:** the same “single source / no invisible sector / no vacuous chosen domain” discipline applies to Monster kernel reflection and the YM D2 full-H spectral detector; this is methodological cross-pollination only, not a theorem-level dependency between Monster and YM. Observer/KK/TSVF and Bishop remain independent of Clay.


## 9 November 2026 — NEW original SU(2) *volume-uniform* local D1.03 estimate

[Original SU(2) Wilson volume-uniform plaquette-deficit theorem](YMClaySU2OriginalWilsonUniformPlaquetteDeficit20261109.md) proves analytically, for the literal periodic 4D normalized-product-Haar SU(2) Wilson partition function and every `β≥16`, that `E[1-(ReTr U_p)/2] ≤ [8+(2/3)log24+log β]/β`, **uniformly in the finite lattice volume**. The argument restricts the true Haar integral to an all-links identity cap of Haar mass at least `δ³/24`, `δ=β^(-1/2)`, and uses convexity of `(log Z)/N_plaquettes`. It then closes the earlier formerly unknown local frustration term:
`P(R<r) ≤ 6[8+(2/3)log24+log β]/[β(6-r)]` for `0<r<6`.
The original one-link Haar tail therefore admits an explicit closed `β` bound for its full finite-volume bad-link probability, with no arbitrary `E[D6]` source.

**D1.03 still OPEN:** a volume-uniform *single-link probability* does NOT provide spatially connecting polymer suppression at fixed physical scale, especially with a diverging number of UV links in each physical block. No CMP116 original long-distance full-covariance estimate, E1 4D interacting continuum, or mass gap follows. This is a genuine original finite-measure pressure theorem, not a theorem that the physical scaling uses any prescribed `β(a)`. Source receipt: original analytic derivation in the linked doc; rational finite quaternion regression script `scripts/check_ym_su2_original_wilson_pressure_uniform_20261109.py` had 2,401 rational plaquette-product controls locally. **No native Agda 2.9 kernel proof** yet.

**Exact next D1-03A (new):** obtain a cutoff-uniform bound on *connected geometrically spanning frustrated polymers* using an admissible gauge-invariant block event; quantify polymer entropy against the actual original Wilson weight/pressure, not independent bare-link failures. **Exact next D1-03B:** prove original full Wilson small+large-field covariance decomposition and CMP116 marked-source applicability with physical distance exponent. Both are mathematically unproved and not replaced by the local result.
