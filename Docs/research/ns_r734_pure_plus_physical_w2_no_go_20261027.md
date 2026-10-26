# R734/R735 W2 max-cut: a physical positive-helicity counterexample to the universal payment

**27 October 2026.** Mathematical objective: test the original unforced Navier–Stokes B continuation compiler against its own **literal dyadic-critical** and **mixed-helicity** inputs. Result: the unrestricted original R734 positive-margin augmented payment is **FALSE** on a smooth, real, divergence-free six-mode periodic Galerkin trajectory. This is a counterexample to an auxiliary inequality, **NOT** to Navier–Stokes global regularity, smooth existence, or the unrestricted Clay theorem.

## Source genealogy and credit

* Navier–Stokes, Leray projection, viscous Galerkin dynamics and exact energy identity are classical mathematics.
* **Fabian Waleffe**, *The nature of triad interactions in homogeneous turbulence*, Physics of Fluids A **4** (1992), 350–363, DOI **10.1063/1.858309**, is an original source for the nontrivial helical triad interactions and signed polarization classes: https://ntrs.nasa.gov/citations/19920038608 . Helical transfer is *not* an original DASHI discovery.
* **Luca Biferale and Edriss S. Titi**, *On the Global Regularity of a Helical-decimated Version of the 3D Navier–Stokes Equations*, arXiv:1303.1215 (2013), https://arxiv.org/abs/1303.1215, prove regularity for a separately **decimated** dynamics restricted to one helicity. They do **not** prove arbitrary-trajectory regularity of the full non-decimated NSE, and their decimated dynamics must not be substituted for the present real Galerkin flow. Our initial data occupy one helicity, but the actual full projected NSE dynamics need not preserve that helicity.
* The original DASHI `NSTriadKNLiteralDyadicShellConstants`, `NSTriadKNLiteralFiniteCriticalObservableFoldExact`, `NSTriadKNLiteralCriticalEnergyPointwiseExact`, `NSTriadKNR650GlobalMixedEnergyBalanceRound691Exact`, `NSTriadKNR650AugmentedCriticalWeightedNormalFormRound734Exact`, and `NSTriadKNR650SharedWeightedQuarticCutRound735Exact` own the *specific* S0/R734/R735 carriers. In particular, R734 already proves a **conditional equivalence**, not the universal estimate. This cut's original contribution is the explicit irrational-algebraic physical counterexample and proof-status audit.
* The existing Ibrahim Pareto/snowball framework is used to retain first-link authorship and avoid counting same-author work as independent validation. A source-written code unit or numerical check is not a theorem proved by Agda.

## The EXACT physical source and cutoff

Take the normalized 2π-periodic three-torus with unit viscosity `nu=1` and original sharp Fourier input/output cutoff `N=2`. The three positive frequencies and real transverse seed vectors are

| frequency m | transverse seed v_m | source weight w(m) |
|---|---|---|
| p=(1,0,0) | (0,1,1) | 1 |
| q=(0,1,2) | (1,0,0) | 2 |
| k=p+q=(1,1,2) | (1,-1,0) | 2 |

Here **w(m)=2^ceil(log2(||m||∞))**, exactly the repo's literal shell convention, NOT ||m||². Let `H+_m=(P_m+i m×/|m|)/2` be the genuine **norm-one physical** positive curl-helicity projector on the transverse plane, and set `uhat(m)=H+_m v_m`, `uhat(-m)=conj(uhat(m))`, zero elsewhere inside the same literal cutoff cube.

Consequently the field is real, mean-zero, divergence-free and smooth; the initial velocity is **positive helicity at EVERY nonzero mode**, including conjugate negatives:
  H+_m uhat(m)=uhat(m),  H-_m uhat(m)=0.
The exact source-selected mixed field `M_j=sum_(a+b=j) (H+_a uhat(a))×(H-_b uhat(b))` is therefore identically zero at initial time for all outputs, not merely zero after summation. Thus original `E_M(0)=0`, its derivative `E_M'(0)=0`, and original signed weighted work instantaneous rate `W'(0)=0`.

For the ACTUAL physical Navier–Stokes Fourier nonlinearity
  `F_m=-i P_m sum_(a+b=m)(b·uhat(a))uhat(b)`
(with zero output at m=0 and original cutoff N=2), exact SymPy gives

  Xcrit(0)=sum_m w(m)|uhat(m)|²=8,
  Dcrit(0)=sum_m w(m)|m|²|uhat(m)|²=36,
  Pcrit(0)=2 Re sum_m w(m)<uhat(m),F_m>
          =(5+sqrt(5)-sqrt(30))/10 > 0.

This is **same physical field, same viscosity, same input/output cube**, not an arbitrary cubic scalar in a different field.

## Exact positive-margin failure, even when δ depends on cutoff/time

Multiply the entire smooth real initial field by scalar `a=512`. At time zero, all H-minus amplitudes remain zero and hence all mixed incidences vanish. Homogeneity gives
  X_a(0)=8 a²,  D_a(0)=36 a²,
  P_a(0)=a³ (5+sqrt5-sqrt30)/10.
The original S0 source proves
  X_a'(0)=P_a(0)-2 nu D_a(0)
         =a² [a*(5+sqrt5-sqrt30)/10-72] > 0
when nu=1 and a=512.

The R734 `AugmentedCriticalWeightedPayment` sought, for positive δ,
  [X(T)-12 E_M(T)] - [X(0)-12 E_M(0)]
     +δ ∫_0^T Dcrit(t)dt <=12 W(T).
Let `R_δ(T)` denote LHS minus RHS. For the actual Galerkin solution,
R_δ(0)=0 and
  R_δ'(0)=X_a'(0)+δ D_a(0) > 0,
since E_M'(0)=0 and W'(0)=0.
The finite Galerkin ODE has smooth coefficients/solutions and the
integrands are continuous. Therefore **there is T>0 so small that**
  R_0(T)>0.
Because Dcrit(t)>=0, `R_δ(T)>=R_0(T)>0` for EVERY δ>0 at the SAME
terminal T. Hence there is **no positive-margin R734 W2 inhabitant**
on this original same-cutoff, same-physical-trajectory case. The
counterexample defeats even an existential δ depending on the
cutoff/terminal. It is stronger than the prior bound δ<=2nu derived
from a single-mode heat shear.

The argument does NOT assert that this flow blows up. Indeed,
finite-dimensional Galerkin dynamics remains smooth, and its initial
unweighted kinetic energy is dissipative. It proves one auxiliary
universal signed-payment route to a general B theorem is **invalid**.

## What survives: the correct Pareto repair

* **W1**: the proven local, classical small-H1 global, and
  late-time **selected-output upper** estimates remain valid. The
  large-data middle-time W1 obstacle remains.
* **W2/R734 as written**: must not be labelled merely 'unpaid but
  plausibly universal'. The universal positive-margin version is
  physically **FALSE**. Its conditional algebraic implication remains
  valid for any restricted trajectory on which the hypothesis is true.
* **Potential positive repair**: include a separately typed
  **same-helicity (++ and --) critical-production channel**, or
  switch to a signed decomposition with sufficient channel coverage,
  rather than expecting the mixed (+−) work to control all physical
  critical production. Any repair needs a *new honest analytical
  inequality* with correct scaling, cutoff independence and same
  Galerkin solution. An extra nonnegative 'residual' term introduced
  solely to cover the defect is not a proved bound or global theorem.
* **A1/A2/A3**: these original continuum obligations remain
  separately open. No forced-to-unforced, shell-model-to-PDE, or
  helical-decimation-to-full-NSE transfer is permitted.

## Execution and proof levels

New `tests/test_ns_r734_pure_plus_physical_w2_no_go.py`:
**six locally executed exact SymPy tests passed**. They check real
Fourier conjugation, transversality, genuine normalized H±
polarization at positive and negative modes, actual projected
Galerkin nonlinearity, exact dyadic critical energy/dissipation/
production, zero original mixed work at t=0, amplitude homogeneity
and positive first derivative for any δ>0.

The mathematical short-time conclusion additionally uses standard
finite-dimensional ODE smoothness/continuity. This is a symbolic
exact arithmetic + analytic-ODE argument, **not** an Agda/Lean
kernel inhabitant of the full physical trajectory. The original
rational-carrier Agda implementation does not automatically inherit
the irrational helical eigenprojectors in this concrete physical
witness. No exact GitHub Actions/Agda/Lean kernel run is claimed.
