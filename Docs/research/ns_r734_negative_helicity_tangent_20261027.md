# R734 / NS369: negative-helicity entry tangent and dyadic-defect temporal lag

**27 October 2026.** Companion to the **original** PR #1271 R734/R735 six-mode physical source and existing R92/R102 Waleffe + NS369 owners. New regression: `tests/test_ns_r734_negative_helicity_tangent.py`. **Proof status:** exact finite Fourier/SymPy calculation plus the classical finite-dimensional Galerkin ODE Taylor rule; local matching-implementation tests; not an independently kernel-checked Agda/Lean theorem and not unrestricted Navier–Stokes regularity.

## Same physical source, no switch to helical decimation

Reuse the *identical* real, solenoidal positive-helicity datum of `tests/test_ns_r734_pure_plus_physical_w2_no_go.py`, the *identical* cube cutoff `N=2`, the *identical* Leray-projected unforced Galerkin force, and the original `H_s(k)=(I+s i k×/|k|)/2`. Positive seed modes: `p=(1,0,0),q=(0,1,2),k=(1,1,2)` with real seeds `(0,1,1),(1,0,0),(1,-1,0)`, respectively; add conjugate negatives. All initial `H-` mode coefficients vanish. Do **not** replace the full NSE by a projected-on-H+ evolution.

Let `F(u)=-P_N P_L(u·∇u)`; by direct symbolic projection of the complete *full* nonlinear convolution,
```
||H-_q F_q(u0)||² = (5/24)(6+sqrt(5)-sqrt(6)-sqrt(30)) > 0.
```
The exact sign is certified by `(6+sqrt(5))²-(sqrt(6)+sqrt(30))²=5`, with both parenthesized terms positive. No decimal comparison is needed. The same coefficient survives each of three proper cyclic NS369 coordinate permutations. As expected for a real field, `-q` contributes an equal squared norm.

Let `u(0)=a u0`, `a>0`; at the initial time, viscosity contributes zero to the negative sector because `H- u(0)=0`. Hence
```
H-_q u'_q(0) = a² H-_q F_q(u0) != 0.
```
Consequently, with `M_-(t)=Σ_{m≠0}|m| ||H-_m u_m(t)||²`,
```
M_-(0)=M_-'(0)=0,
M_-''(0)=2 a^4 Σ_{m≠0}|m| ||H-_m F_m(u0)||²
       >= 4 sqrt(5) a^4 ||H-_q F_q(u0)||² >0.
```
The finite Galerkin ODE is smooth, so `M_-(t)=(M_-''(0)/2)t²+O(t³)` for fixed a, N, ν. This is a full-evolution source fact, not the invariant decimated model.

## Nonpromotion and useful new no-go

The previously established same-datum R734 dyadic critical production is
```
P_dyadic^NL(0)=(5+sqrt(5)-sqrt(30))/10 >0.
```
The original R92/R102 true signed helicity has vanishing *nonlinear* derivative here; `M_-'(0)=0`. Thus all the initial dyadic critical growth comes from the exact curl-vs-dyadic weight defect `R_w=X_dyadic-H_signed-2M_-`:
```
R_w'(0)|NL = a³ P_dyadic^NL(0) >0.
```
Therefore **no universal instantaneous inequality** of the form `|R_w'(t)|<=C (M_-(t))^α`, with `α>0` and finite `C` at this initial field, can hold for all smooth full Galerkin solutions: its RHS is zero at t=0. This is *not* a no-go for estimates that include same-helicity activity, positive-sector norms, a time integral, defect cancellation, or a separately justified source-dependent allowance. It does not imply finite-time singularity.

A correct future critical-payment attempt must explicitly keep (1) genuine same-helicity dyadic spectral flux; (2) negative-helicity generation/exchange; (3) original selected cutoff and possible physical signed cancellation; and (4) the actual viscous margin. Simply quoting global regularity of the **helical-decimated** equation or a 369 sign-quotient cannot pay the full-equation estimate.

## Attribution/source genealogy and literature cross-pollination

- Fabian Waleffe, *The nature of triad interactions in homogeneous turbulence*, *Physics of Fluids A* **4** (1992), 350–363, DOI **10.1063/1.858309**. Original eight helical triadic channels, transfer structure; first-link bibliographic record: https://ntrs.nasa.gov/citations/19920038608 . Original transfer genealogy remains in repo R92/R102.
- Luca Biferale and Edriss S. Titi, *On the Global Regularity of a Helical-decimated Version of the 3D Navier–Stokes Equations* (2013), https://arxiv.org/abs/1303.1215 . Original result concerns **a different projected equation**, not full Galerkin evolution.
- Ö. D. Gürcan, L. Manfredini and P. Morel, *Solutions of the Navier-Stokes Equation Through Affine Transformations: The Triad Triplet*, https://arxiv.org/abs/2609.20710 (17 September 2026). Recent independent **inviscid triad-triplet technique donor**, not a full-viscous 3D regularity certificate and not the source of this particular calculation.
- Stan Palasek, *A logarithmic regularity criterion for the axisymmetric Navier-Stokes equations*, https://arxiv.org/abs/2610.29012 (21 October 2026), assumes **axisymmetry** and a logarithmic circulation condition. Conditional technique donor only.
- Existing DASHI R734/R735 selected observable, R92/R102 true curl-helicity, and NS369 cyclic orientation already have original in-repository authorship. **This PR's distinct contribution** is the exact *negative-helicity entry tangent/lag calculation* on their same witness, not a rediscovery of the external papers.

## Acceptance and roadmap

**Local receipt:** four SymPy tests passed against a matching standalone implementation of the fetched source helper functions (not an exact-head repository pytest run). The new committed test imports the pre-existing R734 witness and NS369 rotation helpers on the PR branch. The analytic inequalities follow from exact projector algebra and finite ODE differentiation. No Agda typecheck or Lean kernel verification performed.

**Next true Pareto gate:** either prove a *valid* cutoff-uniform, same-solution signed estimate paying both the dyadic same-helicity flux and H- exchange across the uncovered arbitrary-large-data middle interval, **or** replace the false R734 W2 leaf with an independently justified physical critical continuation mechanism. Do not promote R369 Gram floor, A1/A2 physical attachment, R406 continuum seam, or B7 continuation without their original separate proof obligations.
