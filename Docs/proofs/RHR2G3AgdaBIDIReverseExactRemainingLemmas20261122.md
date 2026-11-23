## 22 November 2026 — A2 source-exact leading local asymptotic SIGN and the true FarExact cut

**Original source ownership** (re-read merged `chboishabba/dashi_lean4` PR #22 on `main`):
`Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleA2ScalarAudit.lean`
owns the exact `postSixthTerminalM6BudgetAt_lt_threshold_iff`.
`...SignedPolePostSixthAbsorb.lean` owns literal expanded count,
signed M6 cap, original sixth envelope, eighth envelope,
`literalFarExactAt`, its base+horizontal decomposition,
and the CURRENT absolute shell `farShellBound`.
`...SignedPoleV4EndpointAbsorb.lean` owns the actual N-mu V4
discrepancy, expanded-count producer and smooth-mu lower envelope.
`...SignedPoleConeDecomposition.lean` owns
`compensationTargetThreshold rho = 4*combinedZeroHeightDefect rho
+ integral (signedOrdinateTest*Zeta23.mu)`.
The latter smooth integral and the target's height defect MUST
be retained separately from the local A2 budget.

**Local asymptotic with no surrogate count.**
Set `v=t/16`, `eta=1/(pi+1)`, `r=eta*v`,
`ell=log(t)/(2*pi)`,
`S=W.targetStrength`, `L=W.fourthLipschitz`,
and literal `NZ=(zetaZeroConfig.N (t-r-1) (t+r) : R)`.
The original RvM N-mu producer yields `NZ=2*r*ell+O(log t)`
on this positive proportional width, assuming the usual
fixed canonical eta. The source's chosen `EV=O(r^4*log t)`.
Its contributions in local budget after dividing by `v^6`
have orders `EV -> O(log t/t^2)`,
`(3/2)r² NZ -> O(log t/t^3)`.
The leading real-source *local* A2 terms are all of order
`ell/v = O(log t/t)`:
```text
MuGain     =   eta^5 * ell / v * (S/15)         + lower order
SixthDebt  =   eta^5 * ell / v * (pi^6*eta²/2400)+ lower order
EighthDebt =   eta^5 * ell / v * (L*eta²/8500) + lower order

LocalPositiveDebt - MuGain
  = eta^5*ell/v *
    [-S/15 + pi^6*eta²/2400 + L*eta²/8500]
    + lower order.
```
Here `lower order` is for a fixed witness shape or a
uniformly controlled witness family; the repository's
`exists W(t)` alone does NOT imply uniform control of
S(t), L(t), R(t), derivatives or errors. This is NOT
a statement about `FarExact` or `T_W(rho)`.

The exact negative local leading-coefficient criterion is
```text
S > pi^6*eta²/160 + 3*eta²*L/1700.
```
At the original theorem's floor `S >= 7pi^4/1600 ~=0.426165`,
this condition is guaranteed only when the actual L is
below approximately 737.365. The floor + sixth cap
alone do not provide this L upper bound.

**New exact original atomic high-pole test**:
local SymPy/exact rational executable
`scripts/check_rh_a2_atomic_high_pole_sign_20261122.py`
(commit `5453c8f9`). Source uses the ORIGINAL 4 centres
`(0,pi/3,pi/2,pi)`, original J2-null mu roots,
original high pole `P_two=1`, `P_half=9/8`, and actual
signed projective `4G*(A1 cos2-A2 cos1)`.
The selected profile's atomic centre masses are EXACTLY
```text
(-40/117, 0, 160/351, -40/351).
```
Consequently, with ORIGINAL source normalization,
```text
S_atom=5*pi^4/234                      ~= 2.0813908341,
M6_atom=-25*pi^6/234                   ~= -102.71252068,
L_atom=5*pi^5/351*(cosh(pi/2)+8cosh(pi)) ~=415.19636904.
```
The `L_atom` formula is the **cosh-weighted absolute fifth
moment** of the original high-pole *atomic* selected profile,
matching the definition consumed by the G1 fourthLipschitz
carrier as a formal atomic limit. It is NOT an already
Lean-kernel-checked value of `W.fourthLipschitz` for R>0.
Both `S_atom >=7pi^4/1600` and
`-(3/20)pi^6 <= M6_atom < 0` hold exactly.
The resulting leading local A2 coefficient is
```text
C_atom = -S_atom/15
       + pi^6*eta²/2400
       + L_atom*eta²/8500
       ~= -0.11255808466253.
```
A **non-decimal rational certificate** proves
`C_atom < -1/20`: use `3<pi<22/7`,
`eta²<1/16`, `cosh(pi/2),cosh(pi)<cosh4<28`.
The last follows from the exact rational Taylor-geometric
bound `exp(4)<55`. The actual inequality passes exact
SymPy rational assertions. This establishes the
**atomic high-pole local asymptotic sign only**, and
supplies a robust margin available for future R>0/t-large
source-continuity weld. It does NOT establish that the
actual smooth selected `W(t)` inherits this L/S bound
uniformly, or that the **full** A2 strict inequality holds.

**Why existing absolute far shell does not settle this.**
Lean's owned `farShellBound A |t| J =
18*A*log(|t|+4)/J + 72*A/sqrt(J)`, with
`A>=1` and canonical `J=floor(t/2000)`,
carries a positive `t^(-1/2)` MAJORANT component.
Even optimizing J within the local far cutoff leaves
a `sqrt(t)^(-1)` upper-envelope scale, coarser than
the local `log(t)/t` leading balance. This is a
**resolution obstruction of this specific absolute
majorant**, NOT a lower bound on the true signed FarExact
and NOT a refutation of RH. The source separately
identifies `FarExact = FarBaseExact + FarHorizontalExact`,
with the horizontal term's uniform bound conditional on a
`HorizontalFarCurvatureBound CH`.
The exact A2 remaining condition is
```text
FarExact - compensationTargetThreshold(rho)
  < MuGain - LocalPositiveDebt
```
on the actual finite/exhausted signed source.
Crucially `compensationTargetThreshold` contains both
`4*combinedZeroHeightDefect rho` and the full
`integral Psi_W*Zeta23.mu`, whose sign/scale
has NOT been inferred from the atomic local sign.
Keep the open left endpoint atom, true Zeros multiplicities,
SameOrd exclusion, negative far and local slack in every weld.

**Next narrow proof gate:** (1) transfer the strict atom
`S/L/M6` margin to the **same selected R>0 finite-t W**,
including its target band/quantitative radius, then
(2) improve the literal far-vs-threshold comparison by
source-aware signed cancellation or a genuinely sharper
zero-shell theorem; do not confuse improved *absolute*
far bounds with a signed payment.
No Agda/Lean kernel, CI, actual off-line ζ-zero test,
or RH/GRH completion is claimed. Our 8-vertex,
12-map, 6-face indexed geometry retains its
history/time/refinement/Frobenius/consumer labels,
balanced ternary sign, distinct zero types and unpaid
analytic commuting/transport faces.

---

## 22 November 2026 — A2 source-priority recut: strongest existing actual-zero compiler

Following the reflected-cloud finite negative control, the MERGED
`chboishabba/dashi_lean4` PR #22 source was re-read from Lean `main`.
The original `RiemannProjectiveQuarticFourWindowSignedPoleRvMFourth.lean`
ALREADY supplies the actual ordinate-only `V4` from the literal
Riemann–von Mangoldt/Abel discrepancy, e.g. its exact
`quarticSignedPoleRvMVerticalFourthDiscrepancy_eq_abel`
and `abs_le_of_cumulative_bound` `<=9r^4 E`.
The original `...SignedPoleV4EndpointAbsorb.lean` ALREADY pays
the closed-local vs half-open-`(t-r,t+r]` mismatch with the
possible left-endpoint atom, and retains the original `SameOrd`
exclusion where nontrivial. `...SignedPolePostSixthAbsorb.lean`
retains signed sixth and FarExact rather than taking their
absolute values. `...SignedPoleA2ScalarAudit.lean` ALREADY proves
`postSixthTerminalM6BudgetAt_lt_threshold_iff`:

```text
  postSixthTerminalLocalPositiveDebt(EV)
    + literalFarExactAt(eta0,n)
  < compensationTargetThreshold(rho)
    + postSixthTerminalLocalMuGain,
eta0=1/(pi+1), r=eta0*t/16.
```

This is an **unproved strict inequality**, although the
equivalence/normal form itself is source-written. The positive
mu gain for t>=200 and favorable dominant M6 coefficient are
already source-written. A2's remaining obstruction is the
**numerical/analytic sign of that exact real-source balance**,
including actual RvM count NZ, the eighth profile debt,
the literal SIGNED far, and the target/slack. Therefore a new
Montgomery fourth-marked producer is **not the primary missing
A2 weld**; it is a possible alternate sharpening if the
existing V4/H4/complete-jet A2 budget cannot pay. Do not
duplicate paid owners or mislabel the earlier reflected-cloud
counterexample as a failure of the actual A2 theorem.
The previous section's algebraic reverse-marked-fourth
threshold remains a legitimate alternative lens only.

This priority correction is recorded in controlling
`Docs/roadmaps/ClayRHR2ExplicitA160SelectedWRemainingLemmas20261117.md`
(commit `145eb63b`). No new A2 strict estimate, no Agda/Lean
kernel check, and no RH/GRH completion is asserted.

---

## 22 November 2026 — P0 marked-fourth same-source actual-zero gate and reflected-cloud no-go

**Original producer already exists**: Lean main `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleBidiMarkedFourth.lean` proves `literalLocalFourthPhaseMomentAt_eq_bidi_marked` and `literalLocalCenteredFourthAngularAt_eq_bidi_discrepancy`. Its finite actual-zero terms run over `centeredZeroFinset t n` with `quarticSignedPoleLocal t eta rho` AND `rho ∈ ((SameOrd t)ᶜ : Set Zeros)`, with original positive multiplicities `zetaZeroConfig.mult`. Thus the target zero and all same-ordinate zeros are EXCLUDED from this local off-ordinate carrier. Its mu background is the real `Zeta23.mu` integral over the same local interval. The exact paid operator is `D_A(ΔM0,ΔM2,ΔM4)=ΔM4/2 - 3 A² ΔM2 + 5 A⁴ ΔM0 = literalLocalCenteredFourthAngularAt`. The existing Lean `localizedBidiMarkedProducer_exact` packages already-defined moments; it does NOT prove an analytic pair correlation or prime-side estimate.

**Already-paid donor separated:** Agda `DASHI/Analysis/RiemannQuarticSignedPoleBidiMarkedFourthExact.agda` marks the 0/2/4 operator and the specific short-support cosh-marked literal prime channel as owned at source level, but still lists the localized one-centre marked pair ANALYTIC estimate, centred fourth-angular bias and coupling to signed far source/G3 as open. That specific prime-channel vanishing does not establish a bound for the local zeros minus mu and the archimedean/far/slack terms.

**New local SymPy exact geometry negative control.** Source-directed executable `scripts/check_rh_marked_fourth_reflected_cloud_obstruction_20261122.py` (commit `93198e65`). Fix `h>0`, target horizontal A=5h/2, and abstract off-ordinate cloud C with four events `(+A,5h),(-A,5h),(+A,5h),(-A,5h)`, versus cloud D with `(+A,h),(-A,h),(+A,7h),(-A,7h)`. Each event has positive integer multiplicity one and each cloud is invariant under horizontal `a↔-a`. All have strictly positive ordinate displacement, respecting the original `SameOrd t` exclusion. For `0<h<1/10` and `7h<eta*(t/16)`, they fit the physical strip and source's chosen local window. These finite abstract events are NOT an inhabitant of Lean `Zeros`; no actual zeta zero existence is implied. Negative-ordinate conjugate chart/far source is not silently deleted.

Both clouds have vertical `M0=4`, `M2=100h²` and marked-pair `M2=-100h²`. Yet:
- C: vertical `M4=2500h⁴`, marked-pair `M4=-7500h⁴`, original fourth angular zero sum `D_A=-4375h⁴/4<0`.
- D: vertical `M4=4804h⁴`, marked-pair `M4=-2892h⁴`, original fourth angular zero sum `D_A=4841h⁴/4>0`.

The difference in marked `M4` is `4608h⁴`, and in actual fourth-angular zero contributions `2304h⁴`, exactly as the source operator predicts. The local test checks both the marked-pair formula and the independent pointwise source `P4(a,δ)=a⁴-6a²δ²+δ⁴`. Adding an IDENTICAL smooth-mu background to both leaves the difference unchanged, but opposite sign of the CENTRED statistics is not asserted. These synthetic clouds exclude precisely the invalid inference that a signed fourth payment follows from M0/M2, horizontal reflection, positivity of multiplicities and support alone; they do not refute any actual-zeta-specific hypothesis.

**Sharp moment cone for actual positive-multiplicity local zeros:** for `Vj=Σ mult*δ^j`, `|δ|<=L`, `V0>0`, Cauchy and support prove `V2²/V0 <= V4 <= L² V2`. For the restricted subcase every zero has the SAME horizontal absolute displacement `|a|=A`, the fourth-angular ZERO sum lies between `V2²/V0-6A² V2+A⁴ V0` and `L² V2-6A² V2+A⁴ V0`. C attains the Jensen lower bound; D is within `96h⁴` of the upper vertical bound when `L=7h`. The interval crosses zero. This fixed-|a| statement is NOT a universal assertion about the real source where zero horizontal coordinates may differ.

For the full original physical strip `|a|<=1/2`, the pointwise identity `P4(a,δ)=(a²-3δ²)²-8δ⁴` gives `-8δ⁴<=P4(a,δ)<=δ⁴+1/16`; hence the entire positive-multiplicity local zero sum is between `-8L² V2` and `L² V2 + V0/16`. Subtract the exact original smooth-mu fourth integral to get a corresponding interval on the local centred angular statistic. This is a conservative universal inequality, not the paid strict sign.

**Reverse-solve the missing actual-zero estimate:** since the source operator is already exact, a needed lower bound `D_A(Δ)>B` is mathematically equivalent to `ΔM4 > 2 B + 6A² ΔM2 - 10A⁴ ΔM0`; an upper bound reverses it. Lean merged PR #22 identifies the A2 finite strict remaining comparison as `localPositiveDebt + signed FarExact < compensationTargetThreshold + localMuGain`. This must be proved using actual zero measures AND same-source far/compensation, not a per-zero generic cone estimate alone. Do not rebuild 0/2/4 algebra or treat the short-support prime vanishing as the whole explicit formula.

**Original geometry preserved:** eight typed cube vertices, twelve ordered maps, six face obligations; source/reflection/finite-to-limit/smoothing histories, time/refinement/Frobenius/consumer, actual Zeros tag and multiplicity, target-vs-off-ordinate, signed near and FarExact, mu and local slack. Cyclotomic ζ3/ζ3², exponent-zero unity, scalar zero, nonempty balanced C3 cancellation, Fourier-observed zero and actual ζ(s)=0 are different objects. Only established algebraic commuting faces are paid. The actual finite terminal `H_n+E_n+S_W<T_W(rho)` and global RH/GRH remain OPEN. Local SymPy is not Lean/Agda kernel acceptance.

---

## 22 November 2026 — EXPLICIT original Mathlib-bump J2/q4 radius certificate (P0, no RH promotion)

**Source-checked, independently calculated mathematical inequality**;
local SymPy + exact rational majorant test:
`scripts/check_rh_original_bump_explicit_radius_20261122.py`
(source commit `67e6bdf2`). Earlier
`scripts/check_rh_four_window_uniform_horizontal_transfer_20261122.py`
supplies the independent finite-pole bound, not a surrogate Gaussian.
All numeric radii are intentionally extremely conservative.

**Attribution / exact owners.** Original
`Synthesis/RiemannQuantitativeScaledBump.lean` has
`unitContDiffBump : ContDiffBump 0` with `rIn=1/2`,
`rOut=1`, and `scaledUnitBump c R u=unitBump((u-c)/R)`.
The three needed underlying Mathlib API properties are
`ContDiffBump.neg` (evenness at centre zero),
`ContDiffBump.le_one` and `ContDiffBump.one_of_mem_closedBall`
(0<=b<=1; b=1 on |x|<=1/2), together with support |x|<1
(source already proves nonneg and support). Read source:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/BumpFunction/Basic.html
These facts are from **Mathlib**, not novel DASHI results.
Existing `RiemannQuantitativeSymBumpLocalization.lean` and
`RiemannProjectiveQuarticFourWindow.lean` give the exact normalized
four-window pairings; `RiemannProjectiveQuarticFourWindowAtomicCorridor.lean`
gives the original mu corridor/J4 margin; `PoleSameObject.lean`
and `SignedPoleJointHorizontalJet.lean` give the physical pole and
horizontal factors. A new Lean import/weld has **not** been kernel checked.

Set **R=10^-10**, and let b be the actual unit bump, Z its mass-normalized
coordinate, Y=RZ and `eps=E[Y²]/2`.
The plateau and upper bound give
`1<=M0<=2`,
`E[Z²]>=(integral_-1/2^1/2 z² dz)/2=1/24`;
thus `R²/48<=eps<=R²/2`.
The normalized translated/reflected bumps represent precisely this even
Y carrier at each centre for every even source weight.

**Exact J2 near-atomic branch, not a guessed linear mu.**
For lambda in {1/2,2/3}, original `J2=A1*M2-A2*M1`.
The mu coefficient at R=0 is `pi²(8-3lambda)/4>=3pi²/2`.
With `mu_trial=mu0(lambda)+mu1(lambda)*eps` and previously
source-verified `mu1`, Fourier Taylor envelopes yield
```text
|J2_exact(mu_trial)-J2_truncated(mu_trial)| <= 720 R^4,
|J2_truncated(mu_trial)|                 <= 4560 R^4,
|J2_exact(mu_trial)|                     <= 5280 R^4.
d_mu J2_exact >= 3*pi²/2-1188 R² >10 (R<=1/100, |mu|<=1/10).
```
IVT on `mu_trial +/-600 R^4` (derivative>=10) gives an
**exact unique original J2 root** for each selected endpoint,
`|mu_exact-mu_trial|<=600 R^4`. For R=10^-10 the
original corridor `|mu_exact-mu0|<=1/10000` and `|mu|<1/10`
are respected. The second, remote quadratic root, if any, is
**not** promoted.

**Original J4 witness sign.** For |x|<5,k=1,2,
`|(x^4 cos(kx))''|<=4800`, hence
`|J4_smooth(lambda,mu)-J4_atom(lambda,mu)|<=65700 R²`.
Atomic J4 changes by at most `392*|mu-mu0|`
over the corridor, and `|mu_exact-mu0|<=0.56R²`.
The total deviation from the original J4-null value is <`67000R²`.
The original `J4_atom(lambda,mu0)<=-pi^4/243<-1/3`
implies `J4_smooth(lambda,mu_exact)<-1/4` at R=10^-10.

**High-pole positive q4 margin with explicit R4 envelope.**
All source frequencies are at most 18. At each original endpoint,
the Fourier surrogates obey
`phi=1-eps*k²`, `phi'=-2eps*k`, `phi''=-2eps`
up to the explicit R4 errors.
For original `P=(A15+A17)A2/2-(A14+A18)A1/2`,
`Q=2[A1(A2+A6)-A2(A3+A5)]`, `K=P_two Q_half-P_half Q_two`:
```text
|P_exact-P_truncated| <= 78744 R^4
|Q_exact-Q_truncated| <=  7776 R^4
|K_exact(mu_trial)-K_truncated(mu_trial)| <=11619072 R^4
|K_exact(mu_exact)-K_exact(mu_trial)|     <= 2073600 R^4
K_truncated(mu_trial)= (120/13)*eps + Rem_poly
|Rem_poly|<= 91395200000000*eps² <=22848800000000 R^4
total |K_exact-(120/13)*eps|<=22848813692672 R^4
                                      <23000000000000 R^4.
```
These numbers follow from conservative coefficient ℓ¹
majorants, not floating-point samples. Consequently
```text
kappa_R=K_infty(0,4;R)
 >= (120/13)*(R²/48)-22848813692672 R^4
 > R²/6  (R=10^-10).
```
By independent same-source finite-pole transfer,
`|K_t(a,4;R)-kappa_R|<13,000,000/t²` for
`|a|<=1/2,t>=200`. For **every t>=10^14**:
```text
K_t(a,4;R) > R²/6 - 13,000,000/(10^14)^2
           = (11/300) R² >0.
```
The source-defined `q=4` is **moving physical ordinate**
`gamma=5t/4` and is NOT an actual zero census.

**Mandatory negative sign control.**
Original atomic high-pole `K_infty(0,1)=-80/351<0`.
There is no pointwise all-q positivity; do not transfer the
q=4 fixed-radius certificate into a sum over unrestricted
actual off-line zeros or infer a signed compensation from it.

**Our indexed geometry / proof-state receipts.** Keep the
three axes reflection, smoothing and finite-pole limit
(8 typed vertices / 12 maps / 6 square faces) together with
history/time/refinement/Frobenius/consumer, balanced ternary
sign and the distinction between scalar zero, exponent-zero
C3 unity phase, nonempty cancelled C3 orbit, zero Fourier
observation and actual ζ(s)=0 (with multiplicity).
Source-checked algebraic reflection is accepted;
no unverified analytic zero-transport, q-to-gamma cross-chart
or smoothing/pole face is marked proved. Retain negative far
source, mu background, prime side and local slack
in **`H_n+E_n+S_W<T_W(rho)` (OPEN)**.

**Acceptance ledger:** local SymPy source algebra and rational
majorants PASS; exact Mathlib bump API references identified;
the written analytic inequalities are mathematical derivations,
**not** independent interval-code/kernel-certified Lean/Agda
theorems. No Agda/Lean CI or root-closing RH/GRH assertion.

---

## 22 November 2026 — uniform horizontal finite-t transfer from a positive smooth high-pole margin

**New explicit source estimate** (local mathematical derivation; no kernel):
`scripts/check_rh_four_window_uniform_horizontal_transfer_20261122.py`.
Original Lean source owners reread:
`RiemannProjectiveQuarticFourWindowPoleSameObject.lean`
(finite pole weight `cosh(8x/t)*cos(16x)*cos(cx)`),
`RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean`
(physical `cosh(16*a*x/t)` pair),
`RiemannProjectiveQuarticFourWindow.lean`
(normalized four signed bumps, coefficients `1,-1,lambda,mu`),
`RiemannQuantitativeScaledBump.lean`, and
`RiemannQuantitativeSymBumpLocalization.lean`.

For `0<R<1`, `lambda in [1/2,2/3]`, `|mu|<=1/10`,
all `t>=200`, all physical `|a|<=1/2` and fixed normalized
`q=4`, each normalized signed source has total variation
at most `1+1+2/3+1/10<3`, original support `|x|<pi+R<5`,
and both pole and horizontal cosh arguments have modulus <=40/t<=1/5.
Using `cosh z<=2` and `|cosh z-1|<=z²` in this interval:

```text
|P_lambda(t)-P_lambda(infty)| <=28800/t²;
|P_lambda(infty)| <=18;
|F_lambda(t,a,q)-F_lambda(infty,0,q)| <=115200/t²;
|F_lambda(t,a,q)|<=144;
|K_selected(t,a,4)-K_selected(infty,0,4)|<=12441600/t²
                                            <13000000/t².
```

These are **coarse but explicit rigorous scalar estimates** for
the original normalized source, independent of the detailed unit-bump
shape or evenness, as long as the established normalized symmetric
window, mass and support conditions hold. The chosen mu is held fixed
when comparing t to infinity. The scalar `K_selected(infty,0,4)`
is NOT assumed equal to its atomic value.

For a source witness radius R with exact J2-selected muHalf and
muTwo and strict `kappa_R=K_selected(infty,0,4;R)>0`, this yields
```text
t > max(200,sqrt(13000000/kappa_R))
   ==> K_selected(t,a,4;R)>0 for all |a|<=1/2.
```
The earlier independent fixed-shape even-bump jet
`kappa_R=(120/13)*eps+O(R⁴)`,
`eps=m2*R²/2`, `m2>0`, implies **qualitative existence**
of some small R with kappa_R>0, PROVIDED the exact selected
J2 branch equals the locally continued IFT branch and the original
unit bump is even (the latter remains a Lean source lemma to verify).
No numerical kappa_R or explicit radius has been constructed.
Unlike a merely formal mixed-jet bound, this source transfer gives an
explicit finite-t dependence conditional only on the high-limit margin.

**Geometry and no-promotion:** this estimate is uniform in horizontal a
at one fixed normalized q=4. Since q=16*(gamma-t)/t, it is a
moving ordinate gamma=5t/4, not a claimed actual zeta zero.
Reflection a->-a commutes with even hyperbolic observation but does
not identify distinct zeros or merge signed residuals. Preserve
8 vertices, 12 typed directed edges and six face obligations, including
the *unpaid* smoothing/pole-limit and analytic-zero transport faces.
Keep scalar zero, neutral C3 phase, cyclotomic cancellation, kernel
observation zero and actual zeta zeros separate.

The original actual-zero/prime-side terminal
`H_n+E_n+S_W<T_W(rho)` is **OPEN**. A positive q=4 kernel
is not an aggregate signed payment; all real q, multiplicities, far
signed residual, actual mu background and S_W must be retained.
No RH/GRH closure or Lean/Agda kernel receipt.

---

## 22 November 2026 — ORIGINAL finite-frequency positive-width envelope and quadratic J2 branch

Local SymPy regression committed as
`scripts/check_rh_original_four_window_fourier_envelope_20261122.py`.
Source-readback: original Lean
`Synthesis/RiemannQuantitativeScaledBump.lean`
(`unitContDiffBump` scaled by R),
`Synthesis/RiemannQuantitativeSymmetricBumpMass.lean`
(`quantitativeSymBump` is the sum of reflected translated bumps),
`Synthesis/RiemannQuantitativeSymBumpLocalization.lean`
(exact normalizations), `Synthesis/RiemannProjectiveQuarticFourWindow.lean`,
`Synthesis/RiemannProjectiveQuarticFourWindowPoleSameObject.lean`,
and `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean`.

**Important proof dependency:** the existing Lean source supports fixed-shape affine scaling and reflection of translated bumps. The simple cosine-only centre formula additionally requires that the base `unitBump` be even. Although Mathlib's radial `ContDiffBump` should have this symmetry, the cited source files do NOT explicitly prove it; retain as a named source lemma. Without it, use the general complex characteristic function with odd/sine components instead. Never promote the cosine-only formula to checked Lean source without paying this condition.

Conditional on the even base bump, let Y=R Z be the normalized underlying even window displacement with |Z|<=1, and `phi_R(k)=E[cos(kY)]`, `eps=E[Y²]/2`. For the four weights (1,-1,lambda,mu) and centres (0,pi/3,pi/2,pi), define `A(k)=phi_R(k)*sum_j w_j cos(k*c_j)`, and `M(k)=-A''(k)`. Then the original **same-object J2** equation is `J2=A(1)M(2)-A(2)M(1)=0`, exactly a polynomial of degree at most two in mu.

The exact quadratic coefficient is
```text
[mu²] J2 = phi_R(1)*phi_R''(2)-phi_R(2)*phi_R''(1).
```
At R=0 it vanishes, so the old atomic linear equation is recovered; at positive R it generally does not vanish. Therefore continue the **near-atomic IFT branch**, not an arbitrary solution of the smooth quadratic. Source-independent scalar symmetry/IFT alone does not prove the actual Mathlib bump's exact chosen J2 root equals a preexisting existential Lean witness unless that witness is selected/identified.

The original q=4 high-t transform uses exactly
```text
B1=(A(15)+A(17))/2, B2=(A(14)+A(18))/2,
P=B1*A(2)-B2*A(1),
Q=2*(A(1)*(A(2)+A(6))-A(2)*(A(3)+A(5))),
K_selected=P_two*Q_half-P_half*Q_two.
```
The frequencies are on-line {1,2}, profile {2,3,5,6},
and pole {14,15,17,18}; all reuse the same original source
rather than inventing a surrogate density. Local SymPy reproduces
`P_atomic=3(2-lambda)/4`, `Q_atomic=3(lambda-2)`,
zero selected atomic q4 constant, and **+120/13** epsilon coefficient
after moving the near-atomic J2 root.

**Explicit universal compact-window moment remainder envelopes:**
For any positive even normalized bump supported in |Y|<=R,
```text
|phi_R(k)-(1-eps*k²)| <= |k|⁴*R⁴/24,
|phi_R'(k)+2eps*k| <= |k|³*R⁴/6,
|phi_R''(k)+2eps| <= |k|²*R⁴/2.
```
These follow from the scalar Taylor inequalities for cos and sin and
E[Y⁴]<=R⁴. At all source frequencies |k|<=18 the respective explicit
bounds are `4374 R⁴`, `972 R⁴`, `162 R⁴`. Derivative bounds
are only required for k=1,2 in J2 but the larger uniform envelope
is convenient. Local symbolic checks of coefficients and Fourier
reduction PASS, and these elementary analytic bounds are
mathematically derived but **not yet Lean kernel-checked**.

**Remainder weld still open:** compose these explicit envelopes
through the *near-atomic quadratic root* and the true finite-t
`cosh(8x/t)` pole weight while retaining cancellations. A coarse
absolute O(u²) pole perturbation is insufficient for q4 sign,
because atomic q4 starts at O(u⁴). Establish a source-specific
`|Rem|<=C(R⁴+R²u⁴+u⁶)` with an actual C and effective radius,
or exhibit a counterexample to this bound before claiming a
uniform positive finite-t wedge.

**Original indexed cube invariants unchanged:** 8 vertices/12 edges/6
faces; separate source actual analytic zero, multiplicity, reflection,
pole/smoothing chart, physical beta/gamma/t vs normalized a/q,
signed near/far source, observer cancellation, C3 tagged phase and
local slack. No Fourier observation yields a zeta zero and no
frequency identity proves the actual-zero signed terminal.
`H_n+E_n+S_W<T_W(rho)` remains OPEN. No RH/GRH or Lean/Agda kernel completion.

---

## 22 November 2026 — original J2 smooth-branch transversality and conditional positive wedge

Local exact independent SymPy:
`scripts/check_rh_j2_branch_wedge_20261122.py`, evaluated in a local Python environment before committing. Original four-centre source: J2=A1 M2-A2 M1 with finite atomic weights (1,-1,lambda,mu). At its exact atomic null `mu0=(13lambda-8)/(144-54lambda)`,

```text
dJ2/dmu = pi²(8-3lambda)/4 >= 3pi²/2 > 0,
lambda in [1/2,2/3].
mu1(1/2) = -4*(77+2sqrt(3))/(507*pi).
mu1(2/3) = -16*(34+3sqrt(3))/(729*pi).
```

For an **individual fixed reference nonnegative even compactly supported normalized bump shape** B, scaled as Y=R*Z with E[Z²]=m2>0 and bounded support |Z|<=1, source pairings are locally real analytic in R for the trigonometric, polynomial and cosh functions actually in this source; by the nonzero derivative the exact J2=0 root mu(lambda,R) is locally unique/analytic at each endpoint and even in R. The same IFT is uniform over the compact selected lambda interval, subject to the source family hypotheses. This is a mathematical implicit-function argument, **not** Lean compiler acceptance or a numerical explicit radius. The original normalized Mathlib bump must be checked to be precisely a fixed-shape scaling before identifying this branch with its source witness.

**Conditional local two-parameter positive wedge.** At q=4, u=pi/t, physical |a|<=1/2-delta with fixed 0<delta<1/2, the existing exact jets give the nonnegative leading polynomial
```text
K = (120/13)*eps
  + 640*(2pi-sqrt(3))/(39pi)*eps*u²
  + 2560*(sqrt(3)+2pi)/(39pi)*eps*a²*u²
  + (5120/351)*(1-16a^4)*u^4
  + Rem.
eps=m2*R²/2.
```
With even compact bump and analytic J2 branch the formal Taylor remainder can be bounded on a sufficiently small compact polydisc by
`|Rem| <= C*(R^4+R²*u^4+u^6)`, with C finite, independently of bounded physical a. This **bound is not presently explicit or kernel-checked** and must be verified against the original source branch and all omitted terms; in particular its coefficient and radius are not certified.

Algebraic exact domination (SymPy tested):
```text
R^4+R²*u^4+u^6 <= (R²+u²)*(R²+u^4), R,u>=0.
```
On |a|<=1/2-delta, the coefficients of R² and u⁴ have a strictly positive minimum `cmin`. If `C*(R²+u²)<cmin`, then `K>0` for R>0 or u>0 in this small wedge. This is a mathematically valid **conditional compiler** under the source-specific remainder bound, not a proved finite-t global sign certificate. It gives no sign at other q and cannot replace a signed sum over actual off-line zeta zeros.

**Retain our six-face indexed geometry:** original reflection of a, smoothing R and finite-pole u are separately typed axes; eight vertices, twelve directed maps and six face obligations. The algebraic parity of the kernel is paid; a Fourier-zero observation is not an analytic zeta zero; other smoothing/pole commuting faces and actual-zero transports remain uninhabited. Retain signed ternary orientation, multiplicity, nonempty balanced cancellation and prime-side/local slack. Main missing actual-zero terminal is still `H_n+E_n+S_W<T_W(rho)`, and no RH/GRH completion follows.

---

## 22 November 2026 — off-line horizontal mixed positive-width jet (normalization explicit)

Exact original-source local SymPy algebra in `scripts/check_rh_offline_positive_width_horizontal_jet_20261122.py` extends the previous q=4 a=0 result to physical off-line a=beta-1/2. The argument is **not** a generic kernel, it is the original J2-selected four-window pair and original finite pole orientation.

Write `u=pi/t`, `eps=E[Y^2]/2` for the symmetric normalized bump, and move mu(lambda,eps) to preserve J2=0 at both endpoints. The original horizontal response cosh(16*a*x/t) expands as
```text
1 + (128/pi^2)*a^2*x^2*u^2 + O(a^4*u^4).
```
The raw x²-profile selected jet is `20*pi*(sqrt(3)+2*pi)/39`. The actual **physical a²u² coefficient** has the indispensable factor `128/pi²`, giving
```text
[eps*a²*u²] K = 2560*(sqrt(3)+2*pi)/(39*pi) > 0.
[eps*u²] K   = 640*(2*pi-sqrt(3))/(39*pi) > 0.
[eps] K      = 120/13 > 0.
[a²*u²] K_atomic = 0.
[u^4] K_atomic = 5120/351*(1-16*a^4).
```
Any earlier informal coefficient `20*pi*(sqrt(3)+2*pi)/39` without the physical scaling is **only the raw x²-weighted moment**, NOT the physical horizontal coefficient. The two-parameter formal expansion at q=4 is
```text
K = 120/13 eps
  +640*(2*pi-sqrt(3))/(39*pi) eps*u²
  +2560*(sqrt(3)+2*pi)/(39*pi) eps*a²*u²
  +5120/351*(1-16*a^4)*u^4
  + higher-order terms, including eps² and eps*u^4.
```

**Geometry constraint:** a↔-a reflection is exact at the kernel level; it does not assert any off-line ζ zero exists. The q=4 high-ordinate band is a moving physical ordinate and no fixed-zero map across changes of t is assumed. Preserve eight vertices, twelve history-/sign-/residual-carrying maps and six faces, but report only algebraically checked maps as paid; smoothing/pole-limit uniformity and analytic zero/multiplicity intertwiners remain open. Distinguish actual analytic ζ-zero, scalar zero, neutral exponent-zero C3 phase and balanced nonempty C3 cancellation. The signed actual finite source still has near/far/mu background/prime-side charge and local slack. The full terminal `H_n+E_n+S_W<T_W(rho)` is unchanged and UNPAID.

---

## 22 November 2026 — finite-t × positive-width J2-preserving mixed jet; six-face geometry audit

Original same-source definitions consumed: `RiemannProjectiveQuarticFourWindowAtomic.lean`, `RiemannProjectiveQuarticFourWindowPoleSameObject.lean`, and `RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean`.
Local executable: `scripts/check_rh_positive_width_finite_t_mixed_jet_20261122.py`.

Fix physical horizontal a=0 and normalized q=4; u=pi/t and eps=E[Y²]/2 for a common normalized even bump around every source centre. Enforce the *same original J2=0 condition* at each lambda by mu(lambda,eps)=mu0(lambda)+mu1(lambda)eps+O(eps²). The original finite pole weight is `cosh(8x/t)*cos(16x)*cos(cx)` and the exact selected determinant/profile orientation is `P_two*K_half-P_half*K_two`.

Independent local SymPy exact symbolic jets give:
```text
[eps^0 u^0] K = 0
[eps^0 u^2] K = 0
[eps^1 u^0] K = 120/13
[eps^1 u^2] K = 640*(2*pi-sqrt(3))/(39*pi) > 0
```
The pre-existing atomic calculation additionally gives
`[eps^0 u^4] K=5120/351` at a=0,q=4.
Consequently the **formal two-variable expansion** starts
```text
K(0,4;eps,u) =
  (120/13)*eps
 +[640*(2*pi-sqrt(3))/(39*pi)]*eps*u²
 +(5120/351)*u⁴
 + terms of higher order in eps and u.
```
The displayed mixed coefficient is strictly positive because 2*pi>sqrt(3).
No positivity for every finite u or selected compact positive radius follows without a *uniform remainder bound* and an exact source J2 branch. No numerical Gaussian surrogate is being silently identified with the Mathlib normalized bump.

### Exact six-face indexed transport audit (conditional structure, not an analytic theorem)

Three axes determine 8 typed vertices, 12 oriented edges, and 6 square faces:
- Reflection r: source `a -> -a`; apply to the original complex zero carrier WITH multiplicity. A kernel-even observation is not a proof of an analytic zero map.
- Smoothing b: atomic eps=0 -> original even-bump eps>0; preserves each signed centre, history/index and independently solves mu(eps) for J2=0.
- Pole limit p: finite u>0 -> u=0; retains normalized q as a selected coordinate, NOT gamma as a fixed ordinate. A moving q must be tracked when t changes.

Six faces are (r,b) at p=0 and p=1; (r,p) at b=0 and b=1; (b,p) at r=0 and r=1. Algebraic parity r commutes with the even source kernels at these fixed coordinates. The b/p faces are formally compatible for analytic Taylor germs *if* uniform source bump moments and mu branch hold; physical same-zero, finite-t source identification and convergence are OPEN and must not be marked as commuting Lean/Agda theorems. The q=4 moving ordinate and the fixed-physical-gamma chart are different observers and need an explicit change-of-coordinates edge, not an implicit cube equality.

For each vertex keep a tagged source record: analytic ζ-zero/not-a-zero status and multiplicity; physical (beta,gamma,t) and normalized (a,q); exact signed centre weights; mu selection; source pole determinant; original Hnear/Hfar and local slack; zero-observation vs genuine scalar zero vs balanced nonempty cancellation. C3 cyclotomic zeta, a neutral exponent-zero phase, and Riemann ζ(s) are distinct types. Retain signed ternary polarity and residual histories across all 12 maps; a Fourier-zero observer is not faithful on underlying modes.

**Terminal:** `H_n+E_n+S_W<T_W(rho)` for all hypothetical high off-line actual ζ zeros is still OPEN. Neither strictly positive q=4 response nor any of the six square sketches closes the signed aggregate or pays prime-side local slack.

---

## 22 November 2026 — J2-preserving positive-width second-moment jet (new exact local source calculation)

Read-back original source owners: Lean main
`Synthesis/RiemannProjectiveQuarticFourWindowPoleSameObject.lean`
(`quarticFourNormalizedPoleWeight` = cosh(8x/t) cos(16x) cos(cx)),
`Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean`
(signed profile 4G(x)[A1 cos(2x)-A2 cos(x)]), and
`Synthesis/RiemannProjectiveQuarticFourWindowAtomic.lean`
(the J2-null fourth-window family). This avoids confusing on-line pairings
with pole pairings or freezing the wrong mu.

For a normalized symmetric bump Y of small scale, let
`eps=E[Y^2]/2`. Formally
`E[f(c+Y)]=f(c)+eps*f''(c)+O(E[Y^4])`.
For each lambda in {1/2,2/3}, solve the SAME source
`J2=A1*M2-A2*M1=0` through first order via
`mu(lambda,eps)=mu0(lambda)+eps*mu1(lambda)+O(eps^2)`,
with mu0=(13lambda-8)/(144-54lambda). The exact jet is
`mu1=-(partial_eps J2)/(partial_mu J2)` at atomic mu0.
The original high-t *smooth* pole is
`P= B1*A2-B2*A1` with Bc=E_G[cos(16x)cos(cx)],
and `K_lambda(0,4)=4 E_G[(A1cos(2x)-A2cos(x))cos(4x)]`.
The selected source is `P_two*K_half-P_half*K_two`.

SymPy independently checks: atomic P0=3(2-lambda)/4;
atomic K0=3(lambda-2); selected zero constant term;
the moving-mu first-order selected coefficient is EXACTLY `120/13`:

```text
K_selected,high-t,smooth(0,4)
   = (120/13)*eps + O(E[Y^4]+eps^2).
```

For a nondegenerate fixed-shape shrinking even bump Y=R*Z,
eps=(R^2/2)E[Z^2], E[Y^4]=O(R^4):
strict leading coefficient positive, so high-t *smooth* q=4
kernel is positive for sufficiently small R (assuming the
exact smooth J2 root is locally realized). This is not uniform
in arbitrary even bumps lacking bounded fourth-moment
scaling, nor is it yet source-selected positive-R finite-t
Lean acceptance. A separate smooth mu existence/uniqueness
via analytic implicit-function argument, uniform finite-t
error, and actual compact bump normalization remain to be
attached before promotion to the original selected W.

Independent Gaussian *surrogate* numerical quadrature
(with J2 root solved for each lambda) gave K/eps
8.6507901 (sigma=.02), 9.0822512 (sigma=.01),
9.1934151 (sigma=.005), converging toward 120/13.
This checks the symbolic sign independently but the Gaussian
is not the original compact Mathlib bump.
Local SymPy script:
`scripts/check_rh_selected_positive_width_second_moment_20261122.py`.

**Impact:** earlier O(R) smoothing estimates alone lose the
atomic O(t^-4) sign. The new J2-preserving second-moment jet
shows that smooth high-t q=4 can instead have POSITIVE O(R^2)
leading amplitude at fixed small R. However no claim follows
about aggregate actual off-line zeta-zero source terms:
q=4 is only a normalized offset, the full signed source retains
actual multiplicities, other q lanes, far source and local slack.
**P0 missing terminal remains** `H_n+E_n+S_W<T_W(rho)`,
or the actual-zero marked-pair/prime-side local estimate
coupled to the original selected source. No RH/GRH closure.

---

## 22 November 2026 — exact moving q=4 atomic boundary layer (new, local SymPy)

**Reuse original source; no positive-width or actual-zero claim.**
Executable new source regression:
`scripts/check_rh_selected_atomic_q4_boundary_layer_20261122.py`
(committed on draft #1533). With original finite-t atomic pole determinant,
u=pi/t, physical a=beta-1/2, and moving normalized ordinate
q=4+z*u, exact symbolic Taylor algebra yields

```text
K_t,atom(a,4+z*u)
 = (5/1404)*[4096-65536*a^4+1536*pi^2*a^2*z^2-pi^4*z^4]*u^4
   + O(u^5).
```

Coefficients u^0,u^1,u^2,u^3 vanish identically. The z=0
specialization recovers the previously proved
(5120/351)*(1-16*a^4)*u^4. At fixed |a|<1/2, the leading
coefficient is strictly positive exactly when

```text
|z| < (8/pi)*sqrt(12*a^2+sqrt(1+128*a^4)).
```

Because the source q=16*(gamma-t)/t, its moving centre q=4
means gamma=5*t/4, and its *leading-coefficient* ordinate half-width is

```text
|gamma-5*t/4| < (1/2)*sqrt(12*a^2+sqrt(1+128*a^4)).
```

In particular a=0 has limiting half-width 1/2 in gamma.
This is a fixed-physical-width boundary layer with vanishing
kernel amplitude O(t^-4), not a uniform signed-margin estimate.
At z on the root, the leading coefficient is zero and this
calculation supplies **no sign**. The strict leading sign for
each fixed (a,z) strictly inside/outside its boundary holds only
for sufficiently high t, and the result is not uniform up to
|a|=1/2 or the moving z boundary.

The actual selected W has positive bump radius R and non-atomic
mu parameters. No estimate here promotes the atomic sign to W.
The relevant off-ordinate zeros must be actual zeta zeros with
multiplicity and the same t-dependent target selection;
the presence of zeros in the indicated ordinate band is not
proved or assumed. Even if present, this positive local lobe
does not prove failure or success of the aggregate signed payment
H_n+E_n+S_W<T_W(rho). Retain the complete far-source and local
slack. **Missing analytic leaf unchanged:** actual-zero
localized marked-pair/prime-side sign bound plus coupling
to the original finite signed source.

---

# RH R2/G3 ↔ Agda BIDI: reverse-solved exact remaining lemmas (22 November 2026)

## 22 November 2026 — exact original selected-atom sign bifurcation and marked-pair BIDI

### Source-first geometry, NOT a same-object positive-width witness

New original-source mathematical test is in
`scripts/check_rh_selected_finite_t_atomic_sign_20261122.py`
(commits `964db866` / `ed54cef3`; readback blob
`af78e6365b55b194bc23d6dd5efb14ad979f580b`).
Local SymPy **1.14.0** and Python byte-identical Git blob both checked.
Original Lean `main` sources reread:

- `Synthesis/RiemannProjectiveQuarticFourWindowAtomic.lean`
  blob `f2f49ccb889e948a73a6724ce9ce1a59e36a24c1`:
  exact `μ_0(λ)=(13λ−8)/(144−54λ)`, J2=0 and signed J4.
- `Synthesis/RiemannProjectiveQuarticFourWindowAtomicPoleSign.lean`
  blob `64584ceecb34770af0bb547249cd904d4d93706e`:
  high-`t` `P∞(λ)=3(2−λ)/4` and exact **finite-`t`** atomic
  pole determinant.
- `Synthesis/RiemannProjectiveQuarticFourWindowPoleSameObject.lean`
  blob `60cc239d3968e25b8a42cebc18bf4744907facd3`:
  literal normalized pole weight
  `cosh(8v/t)cos(16v)cos(cv)` at c=1,2 and exact
  determinant `P_t=B1 A2−B2 A1`.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleTarget.lean`
  blob `16110e433efd16379c6b93bdc13420036b1d6411`
  and `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean`
  blob `4d0437ffb058c7e8b6961521a611608b1494ba3f`:
  the **source-defined** signed profile is
  `P_{2/3} P_{G,1/2} − P_{1/2}P_{G,2/3}`,
  with `P_G(v)=4G(v)(A1 cos(2v)−A2 cos v)`.
  The exact Lean selected W uses **positive** bump radius `R>0`;
  these calculations concern its **R→0 atomic source model** only.

**A previously unrecorded global identity for the high-`t` atomic BASE.**
At `λ=1/2,2/3`, `μ_0(1/2)=−1/78`,
`μ_0(2/3)=1/162`, atomic centres `0,π/3,π/2,π`,
weights `(1,−1,λ,μ_0)`,
`A1=1/2−μ_0`, `A2=3/2−λ+μ_0`.
With `α` as **independently normalized horizontal** displacement,
the *high-pole-limit atomic* signed Fourier/cosh kernel is exactly
```text
K∞(α,q)
  = (160/351)cos(πq/2)cosh(πα/2)
    −(40/351)cos(πq)cosh(πα)−40/117.
K∞(0,q) = −(80/351)(1−cos(πq/2))² <= 0,
equality precisely q in 4*Z.
```
Thus the entire BASE atom is nonpositive—not merely integer samples.
Nevertheless, put `h=cosh(πα/2)>1`,
`c=cos(πq/2)`, and `c*=h/(2h²−1)∈(0,1)`.
The sign function is a *concave quadratic* in c,
with exact values
```text
K∞(α,4k)=−(80/351)(h−1)² < 0
K∞(α,q with c=c*)=
    (160/351)(h²−1)²/(2h²−1) > 0.
```
Both horizontal `±α` sides have the **same** sign.
The `α>0` positive lobe is not a finite-`t` selected W or an
actual-ζ-zero witness: when physical `a=β−1/2` is fixed and
`t→∞`, `α=16a/t→0`.

**New exact FINITE-`t` atomic result; retains source pole correction.**
Use `u=π/t`, `a=β−1/2`, physical normalized
`α=16a/t`, and
```text
h1=cosh(8u/3), h2=cosh(4u), h3=cosh(8u)
B1(λ)=1+h1/4−μ_0(λ)h3
B2(λ)=1−h1/4−λh2+μ_0(λ)h3
P_t(λ)=B1(λ)(3/2−λ+μ_0(λ))
        −B2(λ)(1/2−μ_0(λ)).
```
Insert `P_t(2/3),P_t(1/2)` into the **same**
atomic four-centre signed profile and cosh/cos Fourier response.
SymPy exact Taylor coefficient collection gives
```text
K_{t,atom}(a,4)
  = [5120/351*(1−16a^4)]*(π/t)^4 + O(t^−6)
K_{t,atom}(a,1) = −80/351 + O(t^−2).
K_{t,atom}(a,0) = −81920/351*a^4*(π/t)^4+O(t^−6).
```
In particular, **for every fixed** `|a|<1/2`,
there is a sufficiently large `t` with
`K_{t,atom}(a,4)>0` but `K_{t,atom}(a,1)<0`.
This is a mathematical asymptotic existence conclusion
from an **exact strictly positive fourth-order coefficient**;
it is NOT a claim of uniformly positive `q=4` over all `t≥200`
or uniformity in `a` up to `±1/2`.
At `a=1/4`, the exact `(π/t)^4` coefficient is
`1600/117`. Numerically evaluated **untruncated**
source pole cosh formula at `t=200,400,1000,10000`
and `a=0,1/16,1/4,49/100`: **16/16**
positive `q=4` / negative `q=1` pairs passed
at 55-digit precision; numerical signs are
**stress tests**, not certified interval enclosures.

**Why this matters to P0:** The original signed
`literalOffOrdSource(σ)` equals
`mult(σ)/(t/16)^2*K_W((β−1/2)/(t/16),
(γ−t)/(t/16))`, with actual zero multiplicity.
The atomic sign-change test prohibits replacing the
signed literal sum by a *universal atom-level
pointwise nonpositive assertion* or using the
`α=0` square as its full kernel.
It does **not** say that any actual ζ-zero
occupies a favourable or adverse toy offset.
Since the source **positive** atomic q=4
margin is `O(t^-4)`, an undifferentiated
fixed-width smoothing error `O(R)`
cannot certify that sign for arbitrarily
large t (for fixed R>0, an upper error
bound of size `C R` eventually exceeds
the `t^-4` margin). A sharper
moment-sensitive smoothing comparison or
a different **signed aggregate** argument
is required if this atomic sign is used.
This is a *limitation of that bounding
method*, not a no-go for all positive-R W.

### Original Agda marked-pair producer recovered in BIDI audit

Additional exact Agda `master` source reread:
`DASHI/Analysis/RiemannQuarticSignedPoleBidiMarkedFourthExact.agda`
blob `703d721bfd3625e31b1cf74f15d3efdb060e99ad`,
which records a **PAID**
target/reflection fourth-angular reconstruction:
```text
P2(x,d)=x²−d², P4(x,d)=x⁴−6x²d²+d⁴
P4(x,d)=[P4(x−A,d)+P4(x+A,d)]/2
       −3 A² [P2(x−A,d)+P2(x+A,d)]
       +5 A⁴.
```
Source status already has the 0/2/4 even-marked
operator **PAID**, but the localized
one-centre marked-pair producer, prime-side
sign/estimate, target-centred fourth angular
bias and coupling to far source are **OPEN**.
`RiemannQuarticSignedPoleFrontierExact.agda`
blob `ad96304383e60526bbbede5e12ddf7d0799412f7`
already owns the historical G1/G3 carrier and
compiled fourth-Lipschitz/band; do not rebuild it.

Exact SymPy BIDI identity PASS. Finite *synthetic*
countermodels have **equal M0=4 and M2=4**
but different `M4=4` versus `M4=8`:
```text
d=(-1,-1,1,1)    => M4=4
d=(-√2,0,0,√2)   => M4=8.
```
The chosen fourth-moment comparison to
`6` has opposite signs. These are **not**
actual ζ-zero configurations; they prove only
that count/second moment cannot determine the
fourth marked quantity from those inputs
alone, and confirm why the existing Agda
fourth-marked producer is not discharged by
the RvM count bound.

### Exact updated proof-search frontier — no extra API

1. **Main Lean R2 signed terminal:**
   for every hypothetical high off-line
   actual ζ `ρ`, preserve original positive-width
   `W`, `t/16`, multiplicities,
   `H_n`, `E_n`, `S_W` and
   `T_W(ρ)`. **OPEN:** prove a strict
   `H_n+E_n+S_W<T_W(ρ)` for some
   true finite half-open window, or the
   sufficient source-sharpened inequality
   `B_n^sharp+S_W≤T_W(ρ)−ε`.
   The atomic sign algebra does NOT produce
   this certificate.
2. **Existing BIDI marked-pair alternative:**
   use the already-proved 0/2/4 even-marked
   identity to translate the remaining
   fourth-order target into an **actual ζ**
   localized marked-pair/prime-side
   quantitative signed estimate, retaining
   actual `μ` background and far coupling.
   This is a genuine **analytic leaf**, not
   another abstract marked-fourth lemma.
3. **Agda original independent high route:**
   the full literal balance-free
   `literalNear + far + Γ < ClusterResponse`
   for each high off-line case, with
   downstream balance attachment and
   low/located source. No presumed Lean
   `W` ⇔ Agda `G2` equality without
   a genuine same-zero/test/scalar weld.
4. **Source trust**: exact Git blob and SymPy
   assertions passed; **no** Agda or Lean
   kernel, no external all-character kernel
   acceptance and no RH/GRH theorem.

---

**Controlling roadmap**: `Docs/roadmaps/AlpogeGRHGeometricTransport20261121.md`.
**Native detailed owner**: `Docs/roadmaps/ClayRHR2ExplicitA160SelectedWRemainingLemmas20261117.md`.
**Mathematical regression**: `scripts/check_rh_bidi_reverse_terminal_20261122.py`.
**Execution policy**: local SymPy 1.14; **no Lean/Agda kernel or GitHub CI run**.

The source-first audit was run in both directions: (1) original terminal → literal necessary scalar inequality → genuine original zero producers; (2) original selected-W/source machinery and Agda producer ports → their actual consumers. It is a dependency audit, not a new RH/GRH proof or an assertion that two response functions with similar names are identical.

## End A — Lean actual selected-W, exactly reverse-solved

Original owners on `chboishabba/dashi_lean4/main`:

- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierMass.lean` (blob `f120fe4f8dcf9c01c81c7856986cfec693921a95`): `completedSignedResidual_eq_jointPairSource` and the source-derived constant-density origin/mu-variation factorization.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal.lean` (blob `fece9d70499d6e324a849ba4bf7c62870ed3d82b`): `canonicalSignedHighResidual_eq_completed_sub_localHalf`, `canonicalLocalBudgetSlack_nonneg` and **`postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack`**. The full post-sixth endpoint is **not** the weaker G3 completed residual inequality.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleConeDecomposition.lean` (blob `2fb66d2e7c4345673e1dda82e67823bf2d7e0481`): the same literal off-ordinate finite source, cone/good/far partition, exact sharpened budget, `UniformSharpenedSignedCompensationGap`, original old→sharpened implication, and cofinal tsum. Existing sharpened source was missed by the prior roadmap and MUST be reused.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleAbel.lean` (blob `556190b96b85b44ffdb5dbeb3b0b1d28a4f8d0e9`): `centeredZeroFinset t n` means **exactly** `t-n < Im ρ ≤ t+n`, and its increasing cofinality is theorem-written.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean` (blob `4d0437ffb058c7e8b6961521a611608b1494ba3f`): literal same-selected-W off-ordinate term ↔ original weighted cosh/cos kernel with multiplicity and `t/16` scaling; quartic source geometry and adverse phases.

For fixed true selected `W : QuarticFourSignedPolePair t`, target `ρ : Zeros` with `Im ρ=t` and `heightOf ρ ≠ 0`, write

```text
H  := ∑' σ : (SameOrd t)^c, W.signedLiteralPairSourceTerm σ
I  := ∫ τ, W.signedOrdinateTest τ * Zeta23.mu τ
d  := W.combinedZeroHeightDefect ρ
S  := W.canonicalLocalBudgetSlack (quarticSignedPoleCanonicalV4Error CV t) ≥ 0
T  := 4*d + I
Hn := W.literalOffOrdExactAt n  -- original (t-n,t+n] finset
```

Original Lean has `W.completedSignedResidual = (H-I)/2`, and the post-sixth endpoint is **exactly**
```text
W.PostSixthCanonicalSignedHighCut ρ EV
    ↔ (H-I)/2 + S/2 < 2*d
    ↔ H + S < T.
```

This scalar equivalence was tested with SymPy symbolically and **108/108** exact substitutions. **Counterexample to lost slack**: `H=3,I=0,d=1,S=2` has `(H-I)/2<2d` but `(H-I)/2+S/2 ≥2d`. So the earlier `UniformSignedCompensationGap ρ` or the already-owned sharper `UniformSharpenedSignedCompensationGap ρ` is **not automatically enough for the final post-sixth inequality** unless its margin also absorbs `S`. Do not assert that G3's completed-only compiler proves the actual terminal.

### BIDI finite signed certificate: an exact alternative to a stronger global gap

Suppose the already source-grounded absolute two-sided tail certificate supplies `E_n≥0`, `|H-Hn|≤E_n` for all `n≥ceil(t+7)`, and `E_n→0` for each fixed `t,W`. The existing R2 roadmap supplies the actual-ζ count donor and explicit bound
```text
En=5*C_N*(t/16)^2*Dstar(R)*[
 log(2*n)/n^4 + log(2*n)/(3*n^3) + 1/(9*n^3)]
```
with original multiplicity and negative-height conjugation. `C_N` exists by original Lean theorem; `Dstar(R)` is symbolic finite if the original fixed-width witness is paid, not presently an effective decimal constant.

Then **exact mathematical equivalence at fixed `t,W,ρ`**:
```text
H+S<T
  ↔ ∃ n≥ceil(t+7), Hn+En+S<T.
```
Forward: set `g=T-H-S>0`; use `En→0` to find `En<g/2`, then `Hn+En+S≤H+2En+S<T`. Backward: `H≤Hn+En`. This is a strict-sign, **same-zero actual-source** finite certificate with all original sign information retained. It is an equivalence **conditional on the cited analytic tail bound**, NOT an algorithm that enumerates all actual zeros rigorously or an unconditional signed inequality.

Another sufficient (but **not necessary**) old-to-new route is the already-owned sharpened budget `Bn=W.literalSharpenedJointBudgetAt η n`, with `Hn≤Bn`: prove eventually `Bn+S≤T-ε` for some `ε>0`; the cofinal limit gives `H+S<T`. The bare `Bn≤T-ε` only proves the completed G3 inequality and may miss `S`.

Exact finite signed negative controls in SymPy:
- cone exact source `x=max(x,0)-max(-x,0)`; the source's `literalConeGainAt` retains `max(-x,0)`. Existing `literalSharpenedJointBudgetAt_le_jointBudgetAt` explicitly states sharpened ≤ unsharpened; **the reverse implication is false**.
- good-lane signed quartic plus remainder: `p+r ≤ p+|r|` for `p≤0` but converse can be strict. Even the sharpened budget may lose negative good remainder.
- original selected atomic `μ(λ)=(13λ-8)/(144-54λ)` gives `μ(1/2)=-1/78` and `μ(2/3)=1/162`; exact `J₂=0`, negative `J₄`, and selected high-`t` atomic kernel `K(0,1)=-80/351`, `K(0,2)=-320/351`, `K(0,4)=0`. These are original **atomic-limit** signals, NOT a smoothed selected W nor actual ζ-zero observations. Absolute values destroy legitimately negative far-source contributions.
- finite scalar compensation ε per `(t,W,ρ)` does NOT provide a global ε across those parameters. `ε_m=1/(m+1)>0` has infimum zero.

## End B — Agda preferred RH consumer and its BIDI producers

Original `chboishabba/dashi_agda/master` files **actually read**, not inferred from GitHub search counts:

- `DASHI/Analysis/RiemannG2ClayTerminalBishopLocatedExact.agda` (blob `a3b647d20edb8bdd4716bd7b961587af1c7f1406`): preferred low-side terminal requires same original Bishop-analytic carrier, located height split, published same-substrate low criticality, Bishop half-line characterization, and **high producer**. Its status says required inputs are not jointly inhabited.
- `DASHI/Analysis/RiemannG2UniformCertifiedHighOffLineProducerExact.agda` (blob `ac935ae2f2a8f86cb8777e6a670d724a05e2c2a0`): for **every high off-line zero** one same-case certified Off core, same-taper Gamma core, original representation attachments and completion. A single finite certificate is not the uniform high theorem.
- `DASHI/Analysis/RiemannG2UniformLiteralPhaseHighProducerExact.agda` (blob `4b49f6a00223881e933d230fdff747c7133beefa`): an even shorter alternative **per-zero** consumer: balance-free context + literal near model + `literalNear + far + Gamma < ClusterResponse`; its final balance is a **separate downstream attachment** and cannot be used to prove the independent analytic margin.
- `DASHI/Analysis/RiemannG2ZeroSideHMBypassBidiExact.agda` (blob `477a1e9adc63d8067381fc50cd8e467905393efe`): `H_X` → `H_T` and literal target-window+same-object attachment → `H_W` already bypass the historical `H_M` detour. The window same-object weld and finite signed near evaluation remain work.
- `DASHI/Analysis/RiemannG2HASingleSourceProducerBidiExact.agda` (blob `401be49e5e8d3b7580b9bc9f0f1e47c2ba3df351`): six math coordinates of `H_A` are projections of **one dependent source-native `SourceNativePhiHatModulation` object and indexed proof**; actual producer recovery/provenance remain open, not six new infrastructures.
- `DASHI/Analysis/RiemannG2ExistingScalarDonorInventoryExact.agda` (blob `911027c04517abbd984e4f226b3f03c93603bfb2`) and `RiemannG2ScalarDonorToPostBalanceBidiExact.agda` (blob `62b587249ac569a7c8d48c5afafe67c2dccb82a1`): reuse actual Riemann–Siegel/explicit-formula/reflection candidates but **none currently inhabits** the precise target-centred cancellation donor; downstream balance break and strict comparison are distinct.
- `DASHI/Analysis/RiemannG2FinalCutIntrospectionExact.agda` (blob `d3f78c8e973c3fe89e714354471f87d77277d679`): actual high G2 scalar leaf and finite-near same-object path remain fail-closed; no representation, balance or visualization can pay the actual strict margin.

**Crucial interoperability non-equivalence:** the Lean selected `W` signed-pole/zero-weighted `H+S<T` theorem and the Agda literal target-window `literalNear+far+Gamma<ClusterResponse` are **different stated consumers**. Their correspondence is not established by both using ζ, cosh, Fourier or the word “margin”. To transport a Lean finite signed certificate into Agda, the minimum independent **same-object identification** must prove (a) the exact actual zero/ordinate/multiplicity correspondence; (b) the same physical test/taper/window and normalization; (c) the exact Lean full terminal residual, local slack and source target equal the Agda final scalar under a common ordered-real semantics; (d) the per-high-off-line quantifiers and the separately owned balance attachment. No current examined source provides that entire weld. Alternatively, work **directly in the Agda literal consumer** without forcing the Lean quartic witness to be its producer.

## Exactly remaining theorem leaves, by owner

| Gate | Exact target | Status |
|---|---|---|
| R2-F0 | `UniformQuarticFourPoleDeterminantCompilerTarget`, from the explicit t-uniform radius `η₀/[22(83/30)19cosh1]` | source mathematics/SymPy PASS; native proof term still **OPEN** |
| R2-F1 | Source selected `W` with uniform quantitative band, signed sixth moment, local slack, literal zero carrier for every target `t,ρ` | conditional witness/consumers exist; uniform per-zero strong property **OPEN** |
| R2-F2 | Actual selected `H_n` **and** source `E_n` in the correct half-open window with effective error certificate | original analytic count/summability donors PAID; exact finite signed values and effective (b_j) **OPEN** |
| R2-S0 | **Full** `H_n+E_n+S_W<T_W(ρ)` for at least one admissible (n) per target, or equivalently the infinite `H+S<T` | **OPEN; strict-sign mathematical leaf**, not proved by absolute tail |
| R2-S1 | Alternative eventually **sharpened** budget `B_n^{sharp}+S_W≤T_W(ρ)-ε` with `ε>0` (per fixed target) | existing sharper cone/good/far algebra PAID; signed inequality **OPEN** |
| Agda-A0 | Recover actual `H_A` single dependent source with proven original function/phase/Weil action and provenance | conditional compiler PAID; concrete source producer/receipt **OPEN** |
| Agda-A1 | Same literal target-window attachment, finite signed-near payment or direct balance-free cluster margin, same-case sharp Gamma and final independent balance | conditional compilers PAID, analytic payment **OPEN** |
| Agda-A2 | One `UniformLiteralPhaseHighProducer` or `UniformCertifiedHighOffLineProducer` **for every high off-line zero**, plus Bishop same-substrate low/located consumers | **OPEN; one finite numerical case insufficient** |
| Cross-T | If claiming Lean-W→Agda-G2 reuse, prove zero/weight/scalar/quantifier identity (not name or generic ζ equivalence) | **OPEN; optional if using independent routes** |
| External-E | Independently run pinned original all-character Lean v4.33.1 kernel and `#print axioms`; compatible root trust admission | **OPEN here; source declarations not proof receipts** |

## Local audit acceptance and attribution

Local SymPy 1.14.0 run on `/mnt/data/check_rh_bidi_reverse_terminal_20261122.py`; its **exact Git blob** agrees with the committed GitHub file `scripts/check_rh_bidi_reverse_terminal_20261122.py`, blob `6eb3222e13d178ccc855f6ae24f1641221bb79d8`. `py_compile` PASS. **108/108 exact terminal substitutions**, sharpened/unsharpened cone counterexamples, true original rational atomic sign geometry, fixed-varying-`ε` no-go, and finite-tail BIDI examples PASS. The earlier existing `rh_uniform_source_audit_20261122.py` was rerun locally: original **256 determinant corners and 12,010 pole-weight derivative values** plus symbolic `t`-varying log-tail PASS. The independently sourced fourth-derivative/zero count is a theorem claim in existing Lean source (not locally kernel replayed). No direct empirical actual-zero numerical census, theorem of RH/GRH or peer-review implied.

**High-alpha next**: attack R2-S0 via **one literal same-source finite signed-near + certified physical tail** and compare it with the *full* terminal `T-S` (or prove R2-S1 via the existing sharpened cone budget), not the weaker `T`. In parallel: R2-F0 original uniform determinant local SymPy math → compatible Lean kernel only when explicitly wanted; Agda-A1 may work independently, and external-E trust is separately gated. Update these two existing roadmaps with every new mathematical receipt.


---

## 23 Nov 2026 — R2-N0 source-original fourth-primitive RvM-only no-go; actual ζ test

**P0 authority remains the same:** selected original `QuarticFourSignedPolePair W(t)`, full strict terminal `H_W+S_W<4d_W(rho)+I_W`, never just `H_W<4d+I`. Existing Lean source owners `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal.lean` (`outerSymmetricDiscrepancyFourthPrimitive_eq_physical`, `OuterFourthPrimitiveUniformBound`, `postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack`); `Synthesis/RiemannZetaMuZeroCountOneSided.lean` (actual RvM arbitrary-endpoint counts); `...NMu.lean` (explicit ordinate/horizontal separation), `...JointHorizontalJet.lean` (exact original per-zero combined kernel). Reuse them; no new representation.

Set `r=t/16`, `eta=1/(pi+1)`, `D_t(s)=zetaMuCumulativeDiscrepancy(t-s,t+s)` (multiplicity-weighted actual ordinate count minus exact `mu` integral), and write the ORIGINAL physical fourth primitive

```
P4(t,Q)= ∫_{r eta}^{rQ} ((rQ-s)^3/6) D_t(s) ds .
```

**Exact RvM-only upper bound:** for a FIXED `eta<Q<16`, sufficiently large `t` with `t-rQ >= max(T0,4)`, the original RvM interval theorem gives `|D_t(s)| <= C(log(t-s+3)+log(t+s+4)) <= 2 C log(t+rQ+4)` on `[r eta,rQ]`. Therefore

```
|P4(t,Q)| <= [C/12] r^4 (Q-eta)^4 log(t+rQ+4).
```

The change `P4_normalized=P4_physical` IS theorem-bearing and pays the **coordinate** factor, but the count estimate still gives only `O(t^4 log t)` on a fixed normalized Q. **No height-uniform `OuterFourthPrimitiveUniformBound B` follows** from this count estimate.

**Strong single-global countermodel to RvM-only derivation:** append synthetic ordinates `gamma_n=(17/16)*4^n` for `n>=4` to an abstract positive-ordinate counting configuration, plus negative conjugates (all at beta=1/2 if assigning physical complex coordinates). Across any interval `(A,B]`, the perturbation changes the count by at most `1+log_4(max(B,1))`, so preserves the class `O(log B)` of RvM discrepancy estimates after enlarging its constant. At `t_n=4^n`, `Q=4`, the physical source window `[3t_n/4,5t_n/4]` contains exactly the *one new* ordinate `gamma_n=t_n+r_n`, `r_n=t_n/16` (`eta<1<4`). Exact quartic cap/Fubini yields

```
Delta P4(t_n,4)
  = ∫_{r_n}^{4r_n} ((4r_n-s)^3/6) ds
  = (3r_n)^4/24
  = (27/8) r_n^4  -> +infinity .
```

This is a **single global count-sequence** negative control, not a family of independently chosen one-height perturbations, and absolutely **not** a new ζ zero. It proves the logical *non-implication* of uniform fourth-primitive control from bare RvM count bounds (even with conjugation and critical-line coordinates), not failure of any stronger actual ζ analytic theorem. Extra zeta-specific cancellation or a bounded/quartic-renormalized primitive source remains necessary.

**Actual ζ numerical BIDI:** independent `mpmath.zetazero` and `nzeros` at `t=200`, and ORIGINAL `mu(x)=[Re ψ(1/4+ix/2)-log(pi)]/(2 pi)`; `mu` primitive computed from continuous-branch `Im logGamma`, checked against independent numerical digamma integration (three intervals). At `Q=4`, 56 numerical zeros in `(150,250]`, direct original `P4=9132.92213389`; quartic-cap/µ crosscheck `9132.92213388`. At `Q=8`, 109 zeros in `(100,300]`, direct `P4=83561.24506020`; cap/µ crosscheck `83561.24506015`. Scaling by `r^4`: `0.37408449` and `3.42266860`. Original `D_t(rq)` changes sign in numerical windows (e.g., q=1 negative, q=2 positive), so no one-sided signed estimate is being inferred. These are **finite-height numerical checks**, not certified zero isolation nor a uniform theorem.

**Executed and committed source:** `scripts/check_rh_p0_rvm_fourth_20261123.py`; exact local Git blob SHA `cffdf1f74178af2a9738b3ebd2e6405debdadcf7` matches GitHub readback. SymPy exact source kernels, two independent real actual-zero evaluations and one-global-countermodel checks PASS. Dependencies SymPy/mpmath/NumPy/SciPy. No Lean/Agda kernel, GitHub CI, actual-W analytic action, all-character Dirichlet theorem admission, or strict signed RH/GRH inequality has been proved.

**Next exact remaining P0:** exploit original `signedLiteralPairSourceTerm_eq_normalizedPairKernel` and `signedNormalizedPairKernel_eq_jointJet` with *both* horizontal `alpha=16(beta-1/2)/t` and ordinate `q=(gamma-t)/(t/16)`, retain multiplicity, original `W(t)`, centered µ integral and `S_W>=0`. Needed is a genuinely independent signed fourth-order correlation/primitive estimate below `2d_W(rho)` (with full slack), or the previously established finite signed `H_n+E_n+S_W<T_W(rho)` certificate for every hypothetical off-line rho. Bare count, selected q-notch, finite model C2^7, RvM absolute tail or a recut of `H-I=2D` cannot pay this. R2-S0 remains OPEN; no RH or GRH proof.


---

## 23 Nov — R2-N1/H1 actual source annular signed-zero reverse-solve packet

The new [original actual-zero source and full signed-Gamma BIDI report](RHOriginalActualZeroAngularAnnuliBidiP020261123.md) supersedes attempts to infer negative zero-minus-Gamma source from negative `K_W` alone. Same original Lean owners: `...JointHorizontalJet.signedLiteralPairSourceTerm_eq_normalizedPairKernel`, `...QuantitativeBand` mass/support, `...FourthOrderQuotient.completedSignedResidual_eq_jointPairSource` (ONE HALF!), `...FourierTerminal.postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack`, original RvM N−mu.

**New real mathematical work:** for `r=t/16,h=10^-4`, the physical left/right annuli `I_t^\pm` have positive actual zeta zero counts for EVERY sufficiently high t via original RvM and `mu` asymptotic, even without assuming RH; ALL such actual zeros have `|alpha|≤|q|/3`, angular `P4/rho⁴≥7/25`, so original selected `K_W(alpha,q)<0`. However `K_W(alpha,q)-K_W(0,q)≥(731/2400)alpha²q²`, strictly positive on an off-axis annular zero, by original fourth-moment/target floor and a remainder with an explicit **alpha²** factor. Thus genuine horizontal sign is paid but contributes nonnegatively to the original global source: it does NOT itself pay the RH strict inequality.

**New empirical actual-source controls:** executed [script](../../scripts/check_rh_p0_actual_zero_annulus_bidi_20261123.py), exact local/GitHub SHA `38636aa9a69e99069666cfe420ac287da9958d7f`. Numerical high-precision mpmath `zetazero/nzeros` and exact digamma-Gamma `mu` show opposing signed **zero-minus-mu** intervals at t=1e6, and a positive signed bilateral two-annulus sum at t=1e6+2, after conservative selected-W 6th-order remainder. These are numerical inputs and NOT certified root enclosures or a global high-zero theorem. Original Mathlib `unitContDiffBump` numerical witness and original W(t)'s existential R(t) not reconstructed; analytic upper/lower bounds hold uniformly over the selected class.

**Analytic RvM-only test fails at original scale:** selected `|K_W(0,q)|≤135000|q|⁴`, `|K_W'(0,q)|≤540000|q|³`; Stieltjes on the original source `|V_I|≤540000 C_RvM log(2t+4)(h/2)^4/r²=O(h⁴ log t/t²)` cannot reach `d_W(a)=O(a⁴/t⁶)`. Prior fourth primitive R2-N0 remains valid. **Reverse-solved exact terminal** `E_rest<4d_W(rho)−S_W−E_{I^-}−E_{I^+}` still requires a new actual signed source bound over *all* other zeros and mu, with correct multiplicity, original rho and t, horizontal joint kernel, full slack S. R2-S0/S1, independent Agda and compatible original all-character proof admission remain OPEN. No Lean/Agda kernel nor CI. No RH/GRH proof.


### 23 Nov R2-S0 signed full-source terminal reconciliation (same original zero configuration)

Correction to the shorthand `E_rest` language above: **its exact value is known**. The original Lean `...SignedPoleCutset.combinedCluster_eq_offGamma` + `combinedCluster_eq_tsum` and `...SignedPoleFourthOrderQuotient.completedSignedResidual_eq_jointPairSource` yield precisely `H_W-I_W=2D_W(t)`, so `E_rest=2D_W(t)-E_{I^-}-E_{I^+}`. The empirical at-t=1000002 positive bilateral residual must be cancelled outside those annuli IF t is not an actual zero ordinate. A hypothetical target and its reflected mate force `D_W≥2d_W`, so `H_W-I_W+S_W−4d_W=2(D_W−2d_W)+S_W≥0`. This is the SAME original nonnegative obstruction, not a new RH proof. The missing mathematical input is an **INDEPENDENT strict negative upper bound** on the complete original signed source, not an algebraic reconstruction of E_rest or prime invisibility already owned at `<log 2`. Full [§G audit](RHOriginalActualZeroAngularAnnuliBidiP020261123.md) records exact source theorem names/factors. R2-S0/S1 OPEN; no new Lean kernel/CI.


---

## 23 Nov RH P0 construction audit — OLD finite-W no-prime cut, NEW source-compatible finite projection

**Proof ledger:** [RHP0PrimeApertureProjectiveEightInvariantConstruction20261123.md](RHP0PrimeApertureProjectiveEightInvariantConstruction20261123.md); [executed source-specific SymPy/NumPy regression](../../scripts/check_rh_p0_prime_aperture_geometry_20261123.py) exact script blob `c2dff1d56db20aa4a9d9f51e46dcb80b13937255` (local `py_compile` and run PASS). Unconditional abstract proof: the evaluation pair at log2/log3 of smooth even compact test functions on the physical aperture `U=(0.36,1.25)∪(-1.25,-0.36)` is independent modulo ANY FINITE list of continuous integral constraints. Original Lean source supplies all actual 8 weights and `quantitativeSymBump`; no replacement source operator required for the existence proof.

**Exact preserved quantities per original endpoint:** A1 at r, A2 at 2r; M2,M4,M6,M8 of projective 4gB; pole responses `∫g cosh(u/2)cos(tu)cos(c r u)` at c=1,2. M0 vanishes automatically. Therefore signed endpoint pole determinant and target fourth strength stay unchanged in the **extended** test. The original physical quartic factor is `r^-6` (normalised M4), eighth `r^-10`; the new height response's first possible change is degree 10 in physical a, not degree 6. Amplitude small enough depending on t/W preserves strict original high-W local target positivity. Note that the extended detector is **not an inhabitant of the old** `QuarticFourSignedPolePair t` type.

**Numerical source-geometry positive controls:** 8 full-rank 8×22 matrices across 2 source ATOMIC endpoint geometries and t=200,1000,80000,1e6, worst constraint residual 1.735e-18, condition ≈858–1519; two independently usable exact smooth prime port evaluation values (1,0)/(0,1). Atomic normalized A determinant −20/351 and limit pole residuals 9/8 and 1. Original Mathlib-selected W was not numerically instantiated.

**Prohibition / derivative debt:** the old combinedCluster_eq_offGamma rests on original `support<log2`; adding ±log2/±log3 BREAKS that theorem hypothesis, so neither the prime-blind `H-I=2D` nor source original K0/Schwartz/absolute sixth/eighth controls can be imported. `||∂^k hδ||1∼δ^(1−k)` for height-one bumps, hence shrinking supports preserve point prime values but may explode global Fourier tails. Basic Weil prime-2/3 contributions have sign-flexible cos(t log p) phases; the full original signed-projective coefficient/zero-Gamma normalization requires another same-object proof, then a separate independent strict signed arithmetic estimate. RH P0 R2-S0/S1 OPEN; E0 generalised carrier, E1 full Weil prime weld, E2 tail/sixth/eighth constants, E3 strict terminal all OPEN. No Lean/Agda kernel/CI and no RH/GRH claim.


**R2-E4 sign-space split:** signed quartic selected W has `M4=−4T_W` and `K_W(0,q)<0` near q=0; any positive-definite/autocorrelation source has real Fourier response ≥0. Thus the eight moment-preserving prime apertures do **not** turn signed W into a Gram/Weil positivity producer. A separate test with an independent proof is needed. Do not assume RH-equivalent global Weil positivity when trying to prove RH. See `RHP0PrimeApertureProjectiveEightInvariantConstruction20261123.md` §9.

---

## 23 Nov — E0/E1 frozen prime 2/3 actual source and near-resonance boundary

The [source-native E0/E1/E2 P0 max-cut ledger](RHP0FrozenTwoPrimeExactSourceWeldAndCost20261123.md) reconciles prior prime-aperture notes with original Lean `Synthesis/RiemannSelectedPrimeSensitiveTwoScale.lean`, whose complete 2/3 sample and 4-channel signed increment were already proven in source. New draft [Lean #116](https://github.com/chboishabba/dashi_lean4/pull/116) proposes **conditional** `QuarticFourFrozenPrimeAperture`: two original-W extended physical detectors, n≥4 zero prime samples, exact frozen two on-line responses, M2/M4/M6/M8, both pole responses, and original 4-channel source identity, plus generic original Weil two-prime coefficient `4 sum_{p=2,3}(log p/√p) cos(t log p)[P_two*g'_half(log p)*B_half -P_half*g'_two(log p)*B_two]`. The affine port formula has no ε² ONLY if the two original A responses are genuinely frozen; ordinary `detectorTwoScale` retains its quadratic term. Explicit lean source not yet compiled or declared accepted.

Exact corridor determinant: −20/351 ± at most 17/60000; old `FourWindowPoleLocalization` permits choosing narrow R for positive poles at each fixed high t. At least one four-port prime gradient nonzero at every t if original smooth A response vectors are nonproportional. But near-double zero cos(t log2)/cos(t log3) phases become arbitrarily close to zero as t→∞, so no uniform gain. Smooth fixture J2 root, T≈2.08, original source pole signals and 16 eight-row fits pass local tests; worst condition ≈9e6 and chosen narrow-bump ||h''||1 triangle bounds very large (not lower bounds). The exact original four-channel equality remains circular as a proof of an independent strict bound.

P0 payoffs NOT asserted: E0 real Lean smooth projected-carrier existence, E1 Lean kernel/axiom check, E2 absolute tail/sixth/eighth and post-sixth margin, E3 independent completed signed arithmetic–zero–Gamma strict high estimate. Original R2-S0/S1 and separate all-χ/Agda proof admission OPEN. [Full code-and-proof receipt](RHP0FrozenTwoPrimeExactSourceWeldAndCost20261123.md). NO CI, NO kernel, RH/GRH OPEN.


### 23 Nov E0 constructive inversion of eight source integrals (no hidden matrix rank)

Strong new geometric result: [full operator and proof §7](RHP0FrozenTwoPrimeExactSourceWeldAndCost20261123.md), [SymPy exact acceptance](../../scripts/check_rh_p0_exact_differential_annihilator_20261123.py), **byte-identical locally executed blob d06af1995d8b4f0e579122a31036e78db74a893e**. The original selected two-radius physical source has eight integral weights `cos(ru),cos(2ru),u^k B_g(u)` k=2,4,6,8 and `cosh(u/2)cos(tu)cos(cru)` c=1,2. Their constant-coefficient even monic annihilator of order52 is `(D²+r²)^9(D²+4r²)^9∏_(c=1,2;σ±)[((D−1/2)²+(t+σcr)²)((D+1/2)²+(t+σcr)²)]`. For every fixed original W and height, a smooth compact even b with 52nd jet=1 at ±logp produces `h=A(D)b` with exact all-eight integral cancellation and exact prescribed prime evaluation1 (other prime0). This is explicit **E0 mathematical existence**; no 8×22 rank assumption, no changes to original J2/J4/6/8 or pole coefficients. E0 Lean inhabitance, absolute high derivatives, full original same-source tensor/Gamma bounds and E3 strict completed RH inequality remain OPEN; `combinedCluster_eq_offGamma` cannot be imported into the new prime-visible carrier. See [draft Lean #116](https://github.com/chboishabba/dashi_lean4/pull/116). NO kernel/CI.


**E0 exact all-physical-strip target stability:** With original fixed W and its r=t/16 normalization, `m_W=inf d_W(a)/a^4>0`, positive fourth-moment limit `T_W/(24r^6)\). Source port variation P_i annihilates M0,2,4,6,8. Define `C_i=(1/(4*10!))∫|P_i(u)||u|^10cosh(|u|/2)du`. The explicit strict `Σ|eps_i| C_i < 64 m_W` implies full `d_extended(a)>0` for all `0<|a|≤1/2`. Exact symbolic factorial/strip gate PASS; [proof §8](RHP0FrozenTwoPrimeExactSourceWeldAndCost20261123.md), test Git blob `40657a85f82df507e73dd4869139cb6ad78fdaea`. This does NOT supply uniform-in-t C_i, full E2 tail or E3 signed global contradiction and does not import the old prime-blind source equality. Lean #116 moment theorem is an uncompiled source proposal.


### 23 Nov E2 precise frozen prime-port theorem status: physical r^-6 and one logarithmic loss

See [source/geometry + all constants](RHP0NormalizedPrimeApertureE2UniformSobolevScale20261123.md). Original order52 even weight annihilator is normalized by A_t(0) to Q_t(D)=Σ_j q_j D^(2j), q0=1, 0≤qj≤binom(26,j)(256/t²)^j for every t≥200 (exact factor proof + Fraction regression). Applying Q_t to fixed-width even **flat-top C∞** b2/b3 gives exact h_p(logp)=1 **for all t** and exact all-eight A1/A2/M2/M4/M6/M8/pole weighted integrals zero, with bounded fixed Sobolev kth norm eventually. Effective finite T_b from b derivatives gives ||h_p||1≤1/4. The original selected W physical strip target floor for t≥32768 is c_* a^4/r^6, c_*=2393451/209715200>1/100. Original source G mass≤83/30 and pole abs<32 give every signed physical port C_i<1/(3000r); amplitudes |ε_i|≤r^-5 across all FOUR ports preserve strict target on full |a|≤1/2, while arithmetic source is same O(r^-6) power. Physical added moment k6<5859.375/r^6, k8<9155.2734375/r^6; raw derivative k8 O(r²) but exact TWO RADIUS cosine product resolves into FOUR sidebands at γ−t=±r,±2r, each of O(1) physical ordinate width. RvM one-unit counts and original µ then bound the FULL **ABSOLUTE** signed source INCREMENT by O(r^-6 logt) (sharper than old O(r^-5 logt)). Strict independent E3 sign/cancellation of remaining log, full E2 original post-sixth/FarExact, concrete T_b evaluation, Lean inhabited carrier/kernel and Agda proof all remain OPEN. Reuse existing original TwoScale/ThreeTap source and PR #116 frozen draft, not a duplicate formula. RH/GRH OPEN.
