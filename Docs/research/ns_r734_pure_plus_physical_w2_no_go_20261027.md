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
**twelve locally executed exact SymPy tests passed**. They check real
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

## Two extra independent source controls and rational barrier

(1) The SAME nonlinear Galerkin forcing satisfies the exact
unweighted physical kinetic energy cancellation
  2 Re Σ_m <uhat(m),F_m> = 0.
Thus the positive dyadic critical-energy production is a
frequency-weighted *redistribution*, not energy creation.

(2) The full unforced projected Navier–Stokes nonlinearity from
pure-plus initial data has a **nonzero H-minus component**:
`||H-_q F_q||²>0` at `q=(0,1,2)`. Do not confuse this
trajectory with the independently globally regular
Biferale–Titi *helical-decimated* dynamical system.

(3) There is a strictly rational, radical-free quantitative
certificate for the crucial sign. Since sqrt(5)>2 and
sqrt(30)<11/2,
  Pcrit=(5+sqrt(5)-sqrt(30))/10 > 3/20.
Thus with scaling factor a=512, ν=1 and Dcrit=36,
  Xcrit'(0)/a² = a Pcrit - 72
              > 512*(3/20)-72 = 24/5 >0.
The obstruction is not an uncertain floating-point result.
All three further checks run in the exact SymPy test file,
bringing the total to **12 passing tests**.

**Source-state update:** the existing original
`NSTriadKNR650AugmentedCriticalWeightedNormalFormRound734Exact.agda`
and `NSTriadKNR650SharedWeightedQuarticCutRound735Exact.agda`
now contain source-local audit comments identifying this
counterexample. Their conditional algebraic record types and
false promotion flags remain unchanged. No new numbered
positive compiler was created or asserted.

## Essential existing R92/R102 cross-pollination: true helicity versus dyadic defect

The repo ALREADY has the correct original Waleffe-energy/helicity
invariant algebra in
`NSTriadKNWaleffeCommonAmplitudeInvariantsRound92Exact.agda`
and its helical signed/unsigned critical exchange reduction in
`NSTriadKNHelicalCriticalExchangeReductionRound102Exact.agda`
plus `NSTriadKNHelicalCriticalExchangeFieldRound102Exact.agda`.
Their true helicity invariant carries a signed **physical curl
eigenvalue** `s_m |m|`, NOT the approximate dyadic
`2^ceil(log2(||m||infty))` weight of R734 S0.

On the SAME six-mode physical datum the exact nonlinear
*true positive-helicity* production is ZERO:
  `2 Re sum_m |m|<u_m,F_m>=0`,
and the positive helicity mass is exactly
  `2+sqrt(5)+2sqrt(6)`.
The original S0 dyadic critical production is nevertheless
  `2 Re sum_m w(m)<u_m,F_m>
     =(5+sqrt5-sqrt30)/10>0`.
Since the true helicity production is zero, the entire difference
is EXACTLY the weight residual
  `P_dyadic =
    2 Re sum_m [w(m)-|m|]<u_m,F_m>`.

This explains the apparent tension with R102's sound statement that
homochiral production vanishes under the exact signed-helicity
invariant: R102 is about **exact curl eigenvalue weights**, whereas
the original R734 continuation currency uses **rounded-up dyadic
weights**, equivalent as positive norms but *not invariant under
nonlinear transfer*. Uniform norm equivalence never implies
equivalence of the corresponding derivatives or signed work.

**Highest-value positive follow-on:** retain the exact physical
helicity cancellation from R92/R102 and isolate a *signed dyadic
weight-defect commutator*, with all same-helicity and mixed-helicity
channels, on the original projected velocity. This route must
produce a genuine cutoff-uniform bound with the original critical
dissipation and an initial-data dependence that survives the
realizability tests; algebraic weight rewriting alone cannot
supply it. No new R-numbered conditional compiler was added here.

The tenth independently passing exact SymPy test in
`tests/test_ns_r734_pure_plus_physical_w2_no_go.py`
verifies the original physical true-helicity production cancellation,
true weighted mass and *exact* dyadic residual decomposition.
The original R92/R102 theorem authors and their cited Waleffe
mathematics retain attribution; DASHI supplies the particular
counterexample and exact comparison.

## Exact GENERAL polarization-resolved critical-energy reconstruction

Let `u_m=u_m^+ + u_m^-` be the TRUE orthogonal normalized
H+ and H- Fourier projection of an arbitrary real divergence-free
velocity, with `e_m^±=|u_m^±|²`, `r_m=|m|` and
`w_m=2^ceil(log2||m||infty)` (the exact source dyadic weight).
Then an EXACT finite algebraic identity, with no unproved PDE
inequality, is

  `X_dyadic = H_signed + 2 M_negative + R_defect`,
  `H_signed=Σ_m r_m(e_m^+ - e_m^-)`,
  `M_negative=Σ_m r_m e_m^-`,
  `R_defect=Σ_m (w_m-r_m)(e_m^+ + e_m^-)`.

For the nonlinear projected NSE tangent, the classical Euler
signed helicity cancellation and R92/R102 prior art give
  `P_dyadic^NL = 2 dM_negative^NL/dt + dR_defect^NL/dt`.
No W2 sign conclusion follows: both components can carry signed
source production, and the defect multiplier `w_m-r_m` can itself
have either sign. This avoids confusing *equivalent positive
critical norms* with *equal nonlinear tangents*.

At the explicit six-mode, initially pure-plus witness,
`dM_negative^NL/dt(0)=0` but
`dR_defect^NL/dt(0)=Pcrit>0`, which is now separately tested
through the FULL physical projected nonlinear force, not only
from substitution into scalar variables.

This is the highest-leverage **constructive REPLACEMENT program**:
retain exact-helicity cancellation, account for negative-helicity
production and the dyadic defect together, with the original
cutoff, physical mode projection and actual trajectory. Existing
R92/R102 already provide the invariant algebra; add only the
necessary physical estimate/attachment, never an uninhabited
positive record renamed as 'closed'. No all-data bound has been
proved for either surviving signed component.

**Receipt:** `tests/test_ns_r734_pure_plus_physical_w2_no_go.py`
now has **12 locally passing exact SymPy tests**, including the
general abstract polarization identity and the source-realizable
tangent decomposition. The original R734 and R735 conditional
Agda modules remain untypechecked with the new audit comments;
no new complete Clay A/B theorem.


## Formal source-side exact identity added to the ORIGINAL R734 owner

`NSTriadKNR650AugmentedCriticalWeightedNormalFormRound734Exact.agda`
now has the new source-written `dyadicCriticalEnergyAsSignedHelicityPlusNegativeAndDefect`.
It proves, for four arbitrary **rational** scalar arguments
`(w,radius,plusMass,minusMass)`,
the full identity
  `w(eplus+eminus) =
     radius(eplus-eminus)
     +2 radius eminus
     +(w-radius)(eplus+eminus)`
by the existing `Data.Rational.Tactic.RingSolver.solve`
(no new mathematical axiom, conditional record or R-number).
It is a reusable FINITE POLYNOMIAL theorem, whose content also
passes the 12-test local SymPy regression.

**Formal limitation:** the real physical `radius=|k|` is
generally irrational and cannot simply be imported into a
rational `ℚ` theorem owner as though a kernel-checked real
embedding or modal decomposition had been proved. This source
term is not kernel-checked in the current environment. It must
not be promoted as the missing all-data helicity/critical
continuum estimate or a valid substitute for the falsified W2.
