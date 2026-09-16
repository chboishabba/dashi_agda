# Yang--Mills BIDI cross-lane closure ledger — 2026-09-16

Status: **live proof-search bookkeeping**, not theorem authority and not a Clay-completion claim.

This sheet supplements `YMRHParetoCoordination.md` and records the current shortest theorem-bearing cut across `dashi_agda` #967 and `dashi_lean4` #7.

## 1. Retained theorem/compiler surface

Lean #7 retains the supplied machine-checked `RequestProject.YangMills.BIDI.*` package as opt-in library `YMBidi`, including localization, arbitrary noncommutative telescope, CMP99 resolvent identity, Cauchy extraction, source calculus, polymer tail compilation, finite->continuum order closure, clustering->vacuum-form-gap measure theory, bounded spectral exclusion, continuum gap transport, end-to-end implication, witnesses and axiom audit.

The supplied worker receipt belongs to the retained source. Current branch integration/welds still require an exact-head Lean receipt before promotion.

Agda #967 already owns the preferred source compilers:

```text
R402 Cauchy extraction
R403 observable-indexed source directions
R404/R405 finite positive summations
R406 noncommutative selected-term scalarization
R407 literal CMP109 four-stage carrier + ordinary bounds
R408 CMP99 resolvent changed-stage compiler + unchanged-stage zero
R409 conditional one-marked whole-product compiler
```

The live source frontier is same-object identity/attachment, not another norm inequality.

## 2. R410 source residual

```text
S0 selected density / actual J_L,J_R / decoupling replay                   LIVE
S1 literal CMP99 defect = actual changed CMP109/R407 factor(s)             LIVE
S2 exact equality of genuinely unchanged factors                           LIVE
S3 R409 product-difference norm = selected R406 scalar term                LIVE
S4 CMP116 positive common-Y / outer majorants on that SAME decomposition   LIVE
```

Do not assume that the source changes exactly one Gate4 stage unless literal replay proves it. R409 is a conditional compiler surface.

## 3. CMP116 source-shaped Row-B route

The generic polymer inputs have been narrowed away.

`LatticeAnimalEntropy` proves the four-dimensional shell-cardinality estimate. Lean #7 `Welds.YMBidiLatticeShell` consumes CMP116 in source volume form

```text
|act(S)| <= A * n^m * exp(-(cmp116BlockRate(kappa1)/M^4) * vol(S))
vol(S) = M^4 n
kappa1 > 5 + 8 log 8
```

and compiles

```text
M^-4 cancellation
 -> block-unit polynomial-marked decay
 -> marked_activity_bound
 -> proved Z^4 entropy
 -> far-shell exponential tail
 -> Cauchy-weighted shell estimate.
```

The surviving mass is

```text
markedRate(cmp116BlockRate(kappa1), lattice4EntropyRate)
  - lattice4EntropyRate,
```

half the original activity/entropy margin.

`Welds.YMCMP116SourceCovariance` then compiles

```text
literal CMP116 source-volume activity majorant
+ source attachment hattach
+ selected source holomorphy
+ physical finite->continuum covariance convergence
---------------------------------------------------
continuum covariance exponential decay.
```

Therefore:

```text
S5 literal differentiated CMP116 activity satisfies source majorant        LIVE
S6 selected physical source coordinates + uniform analytic radii           LIVE
S7 physical finite->continuum covariance convergence                        LIVE
S8 OS/spectral correlation same-object representation                       LIVE
```

Generic `hact`, polymer entropy, Cauchy, marked-polynomial loss and continuum order closure are no longer independent search leaves.

## 4. Finite measure status

R124 is a machine-checked compiler **from** an explicit `BalabanDensityLiteralFiniteMeasureWeld`; it does not construct that physical weld.

```text
M7a0c density -> literal finite-measure equality compiler                 PAID
M7a0p physical density/finite-measure weld inhabitant                      LIVE
M7a1  expectation/L2/null semantics on that SAME measure                   LIVE
```

R205/R206 own the generic finite-measure quotient and selected-IBP -> same-measure symmetry compilers after these physical identities are supplied.

## 5. M7 recut: construct the closed physical form first

Repo archaeology of `YMKatoClosedFormHamiltonianExact` and `BalabanClayMassGapGatePackageExact` narrows M7 again.

The preferred route is **not**:

```text
construct H_a
then separately invent/prove its domain
then separately prove self-adjointness.
```

Instead supply the literal Yang--Mills closed semibounded form

```text
q_a on L2_gauge(mu_a)
+ dense form domain
+ closedness
+ semiboundedness
+ same-object action-variation identification.
```

The existing Kato compiler then returns the associated operator domain and self-adjoint Hamiltonian together.

```text
M7f  literal densely-defined closed semibounded physical YM form q_a        LIVE
M7a  q_a / associated operator = selected physical action variation         LIVE
M7k  Kato form -> associated self-adjoint operator compiler                 PAID compiler
M7c  selected common invariant operator core                                LIVE
```

The Kato interface is theorem/compiler infrastructure; it does not itself inhabit the literal physical form or the common core.

## 6. M9 recut: direct Row-A1 form inequality is the primitive target

The old search target

```text
bMinus <= gap(H_a)
```

is no longer the preferred primitive statement because it presupposes a separately named gap datum.

Lean #7 now provides:

```text
rowA1GapDatumOfDirectFormBound
rowA1PhysicalGapInstanceOfDirectFormBound
```

Given a self-adjoint physical operator with normalized zero vacuum and the direct form inequality

```text
bMinus * ||psi||^2 <= Re <psi, H_a psi>
for psi in D(H_a) cap Omega_a^perp,
```

these constructors produce a genuine `VacuumGapDatum` with gap **exactly `bMinus`**, then the existing Row-A1 inverse/resolvent machinery applies.

Accordingly:

```text
M9c direct form-bound -> VacuumGapDatum/RowA1 instance compiler            SOURCE-WRITTEN
M9p direct physical Row-A1 quadratic-form/coercivity inequality            LIVE
```

On the Kato route, the highest-alpha physical theorem is naturally stated first on the same closed physical form `q_a`, then transported/identified with its associated Hamiltonian through the representation theorem.

## 7. Operator closure normal form

Lean #7 `Welds.YMPhysicalClosureNormalForm` compiles a genuine finite family into the terminal quantitative operator bound.

A `RowA1CutoffFamily` carries a real finite `RowA1PhysicalGapInstance` at every cutoff with the same Row-A1 scalar. It derives

```text
forall n, HasVacuumFormGap H_n Omega_n bMinus.
```

Given the actual vacuum-sector graph limit:

```text
||psi|| <= bMinus^-1 ||H_inf psi||.
```

Given additionally actual equality of YM/OS evolutions on a common core:

```text
||psi|| <= bMinus^-1 ||H_OS psi||.
```

Thus the finite->continuum->same-object **compiler path is paid up to physical inhabitation**.

## 8. Continuum / reconstruction residual

```text
C1 actual physical cutoff family -> vacuum-sector graph limit             LIVE
C2 physical H_inf self-adjoint + normalized zero vacuum instance           LIVE
C3 actual U^YM = U^OS on a common core                                    LIVE
C4 physical spectral/OS correlation representation                         LIVE
```

Generic graph-limit gap transport, common-core generator uniqueness, vacuum-sector resolvent estimates and spectral exclusion are compiler-owned.

## 9. Compressed current wall

```text
SOURCE SAME-OBJECT
  R410: S0--S4
  literal differentiated CMP116 activity -> source majorant
  selected uniform analytic source domain
  physical covariance convergence + OS correlation identification

FINITE PHYSICAL FORM
  physical Balaban density -> literal measure weld
  L2/expectation/null semantics on that same measure
  literal closed semibounded YM form q_a
  q_a = selected physical action variation
  common invariant operator core
  direct Row-A1 coercive floor on that same form/operator

CONTINUUM / RECONSTRUCTION
  actual physical cutoff family -> H_inf graph limit
  physical continuum vacuum/self-adjoint instance
  actual U^YM = U^OS on common core
  physical spectral/OS representation
```

Everything between these inhabitants and the terminal form-gap/resolvent conclusion is now represented by theorem-producing compiler machinery in the active Lean/Agda lanes.

## 10. New Lean #7 continuation commits

```text
e8c4d4ba... RED physical closure normal form
a82dc323... uniform Row-A1 cutoff -> continuum -> YM/OS inverse compiler
b625b14b... RED source-shaped CMP116 activity bridge
0c8da1df... strengthen RED with far-shell theorem
42611747... CMP116 source-volume -> marked far-shell/Cauchy compiler
56287394... RED CMP116-native covariance bridge
227dfc33... recut RED to dedicated source-covariance owner
c83f1a6b... CMP116-native source -> continuum covariance decay
c5ce37e3... RED direct Row-A1 form-bound constructor
784850d4... direct form bound -> VacuumGapDatum / physical Row-A1 instance
ad5d36e4... aggregate axiom-audit sync
```

## 11. Proof-search order

1. **R410 literal source replay** — establish S0--S4 without guessing stage structure.
2. **Literal CMP116 differentiated activity theorem** — establish S5 in the exact source volume/tree form.
3. **Physical measure + closed form** — M7a0p/M7a1/M7f/M7a: construct the literal `L2_gauge(mu_a)` form and same-object action variation.
4. **Direct Row-A1 coercivity + common core** — prove M9p on that exact form/operator and construct the invariant core; let Kato + Lean compilers produce self-adjoint/gap infrastructure.
5. **S6--S8 / C1--C4** — selected analytic uniformity, covariance/OS representation and actual cutoff-to-continuum reconstruction.

## Hard boundary

Do not mark the following complete by introducing another record, receipt, Boolean or generic adapter:

```text
literal CMP99/CMP109 same-object identity
literal differentiated CMP116 source activity estimate
physical density -> measure weld inhabitant
physical L2 expectation semantics
literal closed semibounded Yang--Mills form / action-variation identity
direct Row-A1 coercive lower bound on that same physical object
actual 4D cutoff -> continuum construction
actual YM = OS reconstruction identity
```

If no theorem-strength inhabitant exists, these remain mathematical hypotheses. The current normal forms make the wall smaller and sharper; they do not constitute a Clay completion.
