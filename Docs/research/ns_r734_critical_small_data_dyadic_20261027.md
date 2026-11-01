# R734 full-Galerkin: valid small critical-data dyadic dissipation cut


> **27 October follow-up and supersession (strict source boundary):** The last section below optimises the *older separate-energy/enstrophy averaging certificate*, not the strongest known source-specific entry receipt. The stronger **correlated-energy** \(\int X_N^2\le E_0^2/\nu\) identity and improved waiting time, with \(A_{\rm new}=C_{\rm crit}^2E_0/\nu^2=A_{\rm old}/\sqrt2\), are proved in [ns_r734_critical_residence_pareto_20261027.md](ns_r734_critical_residence_pareto_20261027.md). That new result also gives the sharp heat-shear constant and post-entry Riccati decay. The older optimised time in this document remains valid, but it is **superseded**. No false all-data R734 signed W2 payment or early-time continuation has been inferred.


**Date:** 27 October 2026. **Repository owner:** original `NSTriadKNR650AugmentedCriticalWeightedNormalFormRound734Exact.agda` and `NSTriadKNLiteralFiniteCriticalObservableFoldExact.agda`, not a parallel global proof compiler. **Status:** analytic deduction from classical 3D periodic Sobolev embeddings and the exact full Fourier Galerkin identity, with five new locally passing exact arithmetic regressions. No new Agda/Lean kernel proof. NOT the original unrestricted positive-margin R734/W2 hypothesis, which has a physical counterexample on large data.

## One exact physical Galerkin source

Let `u_N` be a real, zero-mean, divergence-free, unforced periodic Fourier-Galerkin solution for viscosity `nu>0`, with the *original* sharp cube cutoff `max_i |k_i| <=N`. The source's literal dyadic weight on nonzero `k in Z^3` is
```
m(k)=||k||_infty >=1, w(k)=2^ceil(log2 m(k)).
```
Set, in Fourier/Parseval normalization with universal Sobolev constants for that same normalization,
```
X_N(t) = sum_{k≠0, |k|∞<=N} w(k)|u_hat(k,t)|²,
D_N(t) = sum_{k≠0, |k|∞<=N} w(k)|k|²|u_hat(k,t)|²,
P_N(t) = 2 Re sum_{k≠0, |k|∞<=N} w(k) <u_hat(k,t), F_hat(k,t)>,
F(u) = -P_N P_L (u·grad u).
```
The actual full finite Galerkin ODE has the exact derivative identity
```
X_N'(t)+2 nu D_N(t)=P_N(t).
```
This is **not** the separate original R734 claim `X_N(T)-X_N(0)+delta int D_N <= 12 C_N(T)`; the latter has an independently verified false universal positive-margin input. The next bound targets `P_N` absolutely on a restricted small-data class.

## Cutoff-independent nonlinear bound and complete constant bookkeeping

For every nonzero integer `k`, with `r=|k|_2` and `m=|k|∞`,
```
m<=w<2m,       m<=r<=sqrt(3)m;
r/sqrt(3)<=w<2r.
```
The last inequality follows from integer dyadic rounding, no smoothness of the piecewise multiplier needed. Let `C6` and `C3` be fixed periodic mean-zero Sobolev embedding constants
```
||u||_L6 <= C6 ||u||_dotH1,
||grad u||_L3 <= C3 ||u||_dotH3/2.
```
All norms here are full physical vector norms; constants absorb the choice of vector-component norm and torus Fourier normalization. The output projector `P_N P_L` is contractive in L2, **independent of N**. Hence
```
|P_N|
  <= 2 ||w(D)u||_2 ||P_N P_L(u·grad u)||_2
  <= 4 C6 C3 ||u||_dotH1² ||u||_dotH3/2.
```
The exact Fourier Cauchy interpolation is
```
||u||_dotH1² <= ||u||_dotH1/2 ||u||_dotH3/2.
```
Since `w(k)>=r/sqrt(3)`,
```
||u||_dotH1/2² <= sqrt(3) X_N,   ||u||_dotH3/2² <= sqrt(3) D_N.
```
Combining without dropping exponents gives the explicit **source-weighted critical estimate**
```
|P_N(t)| <= Ccrit sqrt(X_N(t)) D_N(t),
Ccrit = 4 * 3^(3/4) * C6 * C3,
X_N'(t) + [2 nu - Ccrit sqrt(X_N(t))] D_N(t) <= 0.
```
Ccrit is common to every finite sharp cube cutoff; it depends only on the **fixed physical torus normalisation and classical embeddings**, not on unknown high norms, cutoff, initial support or solution time. This argument uses no global bootstrap hypothesis.

If `sqrt(X_N(0)) < 2 nu / Ccrit` (or a uniform common upper bound on initial `X_N(0)` satisfies it), define
```
delta = 2 nu - Ccrit sqrt(X_N(0)) > 0.
```
Continuity/first-exit bootstrap yields `X_N(t)<=X_N(0)` for all `t>=0`; therefore
```
X_N(T)+delta*integral_0^T D_N(t)dt <= X_N(0)
```
for every `T>=0` and every finite `N`. This is genuine same-velocity, cutoff-independent positive dissipation **in a restricted critical-small-data class**, in line with classical Fujita–Kato. It is *not* a proof of an all-data R734/W2 signed-work inequality, R406 physical continuum bridge, an arbitrary-data W1 middle payment, or Clay A/B. Deriving uniqueness and a physical limit requires the standard compactness/critical well-posedness argument rather than asserting it from this finite algebra.

## Why this improves the earlier restricted R735 H1 lane

Small initial dyadic critical energy is **not** the same as small enstrophy. For real divergence-free transverse Fourier shear with only modes `±(n,0,0)`, `n=2^j`, choose each modal amplitude `n^(-3/4)`. Then
```
X_N(0)=2*n^(-1/2) ->0,
||u(0)||_dotH1²=2*n^(1/2) -> infinity.
```
The associated full unforced solution happens to be a linear heat shear, but it rigorously demonstrates non-equivalence of small critical data and small H1 on smooth initial data. The critical lane therefore admits initial configurations outside the earlier small-H1 *threshold* even while retaining an all-time coercive budget. It does **not** remove the large-data obstacle.

The existing large-amplitude six-mode R734 physical counterexample belongs outside any sufficiently small-data regime, so its positive initial critical growth is consistent with this estimate. No conflict with the earlier exact dyadic curvature and phase-reversal regressions.

## Test/source audit and attribution

- `tests/test_ns_r734_critical_small_data.py`: **5 locally passing tests** on 27 October 2026 using container `python -m pytest -q`. Tests include every nonzero integer triple in `[-9,9]^3`, exact squared weight/radius inequalities, rational finite Cauchy determinant, exact critical absorption scalar, explicit small-critical/large-H1 shear family, and failure to infer a universal positive margin at large amplitude. They do not independently verify Sobolev embeddings or kernel-check a PDE proof.
- Classical original source **Hiroshi Fujita and Tosio Kato (1964)**, `On the Navier–Stokes initial value problem. I`, *Archive for Rational Mechanics and Analysis* **16**, 269–315, DOI 10.1007/BF00276188. A modern clear attribution and critical-space hypothesis is in the 2026 ICM invited survey https://epubs.siam.org/doi/full/10.1137/25M1801980 ; classical analytic source and all-dimensional smallness are not assigned to this PR.
- Original source-critical dyadic weight and selected cutoff are the pre-existing DASHI R734/R735 owners. The **specific** local calculation of the literal `2^ceil(log2||k||∞)` multiplier and its explicitly named constants is this PR's specialisation.
- **Bastounis, Circelli, Hansen**, arXiv:2610.08144v1 (2026-10-06): original semantic-fidelity warning concerning autoformalisation. This note keeps the natural-language full-NS, source-specific sharp cube, finite Galerkin hypothesis separate from the rational source-written identity, test fixtures and any missing Agda kernel receipt; Agda #1273 and Lean #88 own that independent source audit.
- **Fabian Waleffe (1992)**, DOI 10.1063/1.858309, owns classical helical triad transfer structure; this bound does *not* require an assumed homochiral cancellation and is for the **full** Galerkin equation.

## Remaining proper Pareto gates

1. Physical R734/W2 all-data positive-margin **retired as false**; retain this valid small-critical counterpart and the exact pure-helicity counterexample.
2. For unrestricted B, prove a different **true** time-integrated physical signed compensation or critical continuation estimate, including dyadic same-helicity flux and generated H- sector across the arbitrary-large-data middle interval.
3. The original R369 Gram proof still needs an actual same-operator phase-resolved Rayleigh bound; positive-part finite-to-tail scripted incidence cannot be conflated with signed R734 core transfer.
4. Agda/Lean checked compilation and exact-natural-language-to-formal-source interpretation still open for these new lemmas; the finite tests are acceptance checks, not their substitute.


## Stronger 27 October result: universal late critical absorption from kinetic energy alone

This branch's critical-small-data estimate can also be activated **eventually for arbitrary initial finite energy** without imposing an initial H1 bound or invoking the separate R735 `H1` cubic differential inequality. This is the classical eventual dissipative smoothing mechanism expressed directly in the original R734 `X_N,D_N` variables.

Write `E_N(t)=||u_N(t)||_2²`, and `E0=||u0||_2²>0` common to all Fourier cutoffs. The standard unforced finite Galerkin energy identity and mean-zero Poincaré inequality yield, uniformly in the cutoff,
```
E_N(t) <= E0 exp(-2 nu t),
int_t^(t+L) ||u_N(s)||_dotH1² ds <= E_N(t)/(2 nu).
```
For `L=1/nu`, the averaging principle gives some `s_N in [t0,t0+1/nu]` (possibly different for each N) with
```
||u_N(s_N)||_dotH1² <= E_N(t0)/2.
```
The *same velocity's* exact H0-H1 Fourier interpolation and `w(k)<2|k|` give
```
X_N(s_N) <= 2 ||u_N(s_N)||_dotH1/2²
         <= 2 ||u_N(s_N)||_2 ||u_N(s_N)||_dotH1
         <= sqrt(2) E_N(t0).
```
Set `Ccrit=4*3^(3/4)*C6*C3` from the previous section, and for `E0>0` define
```
t0 = max(0, log( sqrt(2)*Ccrit²*E0 / nu² )/(2*nu)),
t_enter = t0 + 1/nu.
```
Then `sqrt(2) E_N(t0) <= nu²/Ccrit²`; hence `X_N(s_N)<=nu²/Ccrit²`. The small-critical absorption argument is forward invariant, so **at one common time**, despite the individual intermediate `s_N`,
```
X_N(t_enter) <= nu²/Ccrit²,
X_N(T) + nu int_(t_enter)^T D_N(t)dt <= X_N(t_enter)
     <= nu²/Ccrit²,    T>=t_enter, uniformly in N.
```
The **late budget is independent of E0 and N**; E0 affects only the logarithmic waiting time. This is a separate, valid physical-source critical-energy analogue of the earlier R735 eventual `H1` entry, and no claim of independent discovery of classical eventual regularisation is made. New exact squared-threshold/absorption checks added to the existing test file: **seven locally passed** in total.

**Important boundaries:** The proof is for the unforced mean-zero 3D periodic full Galerkin flows at the original sharp cube cutoff. It gives neither a cutoff-independent estimate on `[0,t_enter]` for arbitrary data nor an all-data R734 positive-margin **signed W2** inequality. Identifying the same physical limiting solution, and any compactness/uniqueness claim, requires independent legitimate PDE arguments. In particular a late-time estimate cannot simply be glued to the initial local estimate across the known arbitrary-large-data gap.


## Pareto optimisation: sharpest entry time from this single-window energy-averaging certificate

The prior choice `L=1/nu` is convenient but not optimal. Let
```
A = sqrt(2)*Ccrit²*E0/nu² > 0,       z=nu*L>0.
```
Using the **same** energy/interpolation chain, a window `[t0,t0+L]` certifies the entry threshold `X(s_N)<=nu²/Ccrit²` whenever
```
t0(z)=max(0, log(A/sqrt(z))/(2nu)).
t_enter(z)=z/nu+t0(z).
```
For `z<A²`, differentiate `nu*t_enter=z+log(A/sqrt(z))/2`:
```
d/dz (nu*t_enter) = 1-1/(4z),
d²/dz²(nu*t_enter)=1/(4z²)>0.
```
For `z>=A²`, the decay-waiting term vanishes and `t_enter=z/nu` increases. Hence the *exact global minimum among these single-window averaging bounds* occurs at
```
z_* = min(A²,1/4),              L_*=z_*/nu,

if 0<A<=1/2:
  T_* = A²/nu.
if A>=1/2:
  T_* = [1/4 + log(2A)/2]/nu.
```
Both formulas agree at `A=1/2`. For `E0=0`, the zero flow is trivial and one can set `T_*=0`. For `E0>0`, this `T_*` is **no larger than** the previous `1/nu+max(0,log(A)/(2nu))` receipt and normally substantially smaller. Despite different `s_N in [t0,t0+L_*]`, every Galerkin cutoff has
```
X_N(T_*) <= nu²/Ccrit²,
X_N(T)+nu int_(T_*)^T D_N <=nu²/Ccrit² for all T>=T_*.
```
This is an optimisation **only of the displayed one-window energy-decay certificate**, not a claimed universally earliest actual smoothing time. Two additional exact SymPy calculus/branch-continuity tests passed locally; total in `tests/test_ns_r734_critical_small_data.py`: **nine**. The difficult arbitrary-data initial/middle finite interval remains open.
