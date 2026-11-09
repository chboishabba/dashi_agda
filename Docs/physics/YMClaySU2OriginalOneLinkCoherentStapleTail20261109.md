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
