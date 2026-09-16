# Yang--Mills BIDI cross-lane closure ledger — 2026-09-16

Status: **live proof-search bookkeeping**, not theorem authority and not a Clay-completion claim.

This ledger supplements `YMRHParetoCoordination.md` for the current Lean/Agda cross-lane closure pass. It distinguishes compiler debt from genuinely uninhabited source/physical theorems.

## Current lanes

- `dashi_agda` PR #967 — source producer feeding merged #970.
- `dashi_lean4` PR #7 — retained BIDI/operator theorems plus active backward/closure welds.

## Closure-pass theorem surface

### Retained BIDI package

The supplied machine-checked `RequestProject.YangMills.BIDI.*` tranche is retained on Lean #7 under

`ImportedLeans/aristotle-results/ym-bidi-task-449b959c-20260916/output-final_aristotle/`

and exposed as opt-in Lake library `YMBidi`.

It contains theorem-level implementations of:

```text
R404/R405 localization sums
arbitrary-length noncommutative telescope
four-stage one-marked product collapse
CMP99 second resolvent identity and norm bound
R402 two-source / polarized Cauchy extraction
observable-indexed source calculus
spatial -> temporal exponential transfer
finite -> continuum norm/order closure
Laplace-decay -> no subgap spectral weight -> vacuum form gap
bounded spectral exclusion
cutoff-clustering -> continuum vacuum form gap/resolvent
end-to-end implication and non-vacuity witnesses
axiom audit
```

The worker build/axiom receipt belongs to the retained supplied source. Current Lean branch integration still needs an exact-head Lean receipt before promotion.

### R410 remains same-object source debt

R406 already scalarizes the selected differentiated term as a noncommutative operator-product difference and compiles factorwise ordinary/marked bounds through Round72. R407/R408/R409 supply the four-stage carrier, changed-stage resolvent compiler, unchanged-stage zero compiler, and conditional one-marked whole-product compiler.

The remaining source identities are therefore:

```text
S0 selected density / actual J_L,J_R / decoupling replay
S1 literal CMP99 defect = actual changed CMP109/R407 factor(s)
S2 exact equality of factors that are genuinely unchanged
S3 R409 product-difference norm = selected R406 scalar term
S4 positive CMP116 common-Y / outer majorants on that SAME decomposition
```

Do not add another generic product wrapper. Do not assume exactly one changed stage unless literal source replay proves it.

### Row-B entropy is paid; source-shaped activity compiler is now active

The generic BIDI polymer theorem originally accepted:

```text
hact  generic exponential activity majorant
hcard generic shell-cardinality bound.
```

Both artificial interfaces have now been narrowed.

`LatticeAnimalEntropy` proves the four-dimensional shell-cardinality theorem, so `hcard` is compiler-owned.

Lean #7 `Welds.YMBidiLatticeShell` now also consumes CMP116 in its source-native volume form:

```text
|act(S)|
  <= A * n^m * exp(-(cmp116BlockRate(kappa1)/M^4) * vol(S))
vol(S) = M^4 n
kappa1 > 5 + 8 log 8
```

and compiles:

```text
source volume form
 -> M^-4 cancellation
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

which is half of the original activity/entropy margin.

`Welds.YMCMP116SourceCovariance` then specializes the retained BIDI end-to-end source theorem:

```text
literal CMP116 source-shaped activity hypothesis
+ selected source attachment hattach
+ selected source-domain holomorphy
+ physical finite->continuum covariance convergence
---------------------------------------------------
continuum covariance exponential decay
```

Thus generic polymer `hact`/`hcard` are no longer live proof-search leaves.

The actual theorem still missing is the source/same-object statement that the **literal differentiated CMP116 activity** satisfies the published/source-shaped majorant on the selected decomposition.

### Finite measure is split correctly

`BalabanDensityToLiteralFiniteMeasureRound124Exact` is a machine-checked compiler from an explicit `BalabanDensityLiteralFiniteMeasureWeld` inhabitant. The equality is a field of that record; R124 does not construct the physical weld.

Use:

```text
M7a0c density -> literal finite-measure equality compiler       PAID
M7a0p physical density/finite-measure weld inhabitant           LIVE
M7a1  expectation/L2/null semantics on that SAME measure        LIVE
```

R205/R206 own the generic expectation/null/quotient and same-measure IBP-symmetry compilers once the physical identities are supplied.

### Operator closure normal form is now explicit

Lean #7 `Welds.YMPhysicalClosureNormalForm` adds the missing cross-cutoff compiler.

A `RowA1CutoffFamily` consists of genuine finite `RowA1PhysicalGapInstance`s with the same `SU(N)` and Row-A1 source parameters. It derives:

```text
forall n,
  HasVacuumFormGap H_n Omega_n bMinus
```

with the same `bMinus` at every cutoff.

Given an actual vacuum-sector graph limit, it derives the continuum zero-shift budget

```text
||psi|| <= bMinus^-1 ||H_inf psi||.
```

Given additionally an actual equality of YM/OS evolutions on a common core, it derives

```text
||psi|| <= bMinus^-1 ||H_OS psi||.
```

No gap constant, Hamiltonian, graph limit, or evolution equality is manufactured. Consequently the **operator compiler path is now complete up to physical inhabitation**.

## Current source/correlation residual

```text
S0  selected density / actual J_L,J_R / decoupling replay                 LIVE
S1  CMP99 defect = actual R407 changed factor(s)                           LIVE
S2  exact equality of genuinely unchanged R407 factors                    LIVE
S3  R409 product-difference norm = selected R406 scalar term               LIVE
S4  CMP116 positive majorants on that same decomposition                   LIVE
S5  literal differentiated CMP116 activity satisfies source volume majorant LIVE
S6  selected physical source coordinates + uniform analytic radii          LIVE
S7  physical finite->continuum covariance convergence                       LIVE
S8  OS/spectral correlation same-object representation                      LIVE
```

The generic activity/entropy/Cauchy/continuum-order machinery around S5--S7 is now compiler-owned.

## Current finite physical-operator residual

```text
M7a0c density -> literal finite-measure equality compiler                 PAID
M7a0p physical density/finite-measure weld inhabitant                      LIVE
M7a1  expectation/L2/null semantics on SAME literal measure                LIVE
M7b   literal finite-spacing YM H_a = selected action variation             LIVE
M7c   common invariant dense core + self-adjoint realization                LIVE
M9c   bMinus<=gap -> form-gap/inverse compiler                              SOURCE-WRITTEN
M9p   literal bMinus<=gap(H_a) for SAME physical H_a                        LIVE
M9f   uniform finite Row-A1 family -> continuum -> same-object compiler     SOURCE-WRITTEN
```

R206 symmetry is not self-adjointness; M7c remains genuine.

## Current continuum/operator residual

```text
C1 actual cutoff physical Hamiltonian family -> continuum graph limit      LIVE
C2 physical continuum self-adjoint H_inf / normalized zero vacuum           LIVE
C3 actual U^YM = U^OS on a common core                                     LIVE
C4 physical spectral/OS representation identifying correlations            LIVE
```

Generic compilers are paid:

```text
vacuum-sector form gap -> resolvent bound
uniform finite Row-A1 form gap -> continuum form gap / zero-shift budget
uniform cutoff gap + graph limit -> continuum form gap
same evolution + common core -> equality of unbounded operators
clustering spectral data -> vacuum form gap
```

## Lean #7 focused commits from this continuation

```text
e8c4d4ba...  RED physical closure normal form
a82dc323...  uniform Row-A1 cutoff -> continuum -> YM/OS inverse compiler
b625b14b...  RED source-shaped CMP116 activity bridge
0c8da1df...  strengthen RED with far-shell theorem
42611747...  CMP116 source-volume -> marked far-shell/Cauchy compiler
56287394...  RED CMP116-native continuum covariance weld
227dfc33...  recut RED to dedicated source-covariance owner
c83f1a6b...  CMP116-native source -> continuum covariance decay
a6b49b46...  aggregate physical/source-shaped axiom audit
bc0baf96...  aggregate source-covariance axiom audit
```

Earlier retained-BIDI commits remain listed in Lean #7.

## Compressed current wall

After the new compilers, equation (118) should be read as **inhabitation debt**, not missing formal plumbing:

```text
SOURCE IDENTITIES
  R410 same-object CMP99/CMP109/R406 attachment
  literal differentiated CMP116 activity -> source volume-form majorant
  selected physical source analytic domain / radii
  physical covariance convergence and OS correlation identification

FINITE PHYSICAL OBJECT
  physical Balaban density -> literal finite measure
  same-measure L2 expectation semantics
  literal action-variation Hamiltonian H_a
  common dense core + self-adjoint realization
  bMinus <= gap(H_a) on that same H_a

CONTINUUM / RECONSTRUCTION
  actual physical cutoff family -> graph limit H_inf
  continuum physical self-adjoint/vacuum instance
  actual U^YM = U^OS on common core
  physical spectral/OS representation
```

Everything between these inhabitants and the terminal quantitative gap/resolvent statement is now represented by theorem-producing compilers in the current Lean/Agda lanes.

## Proof-search order

1. **R410 literal source replay** — establish S0--S4, without guessing a one-stage replacement.
2. **Literal CMP116 differentiated activity theorem** — establish S5 in the exact source volume/tree form; the rest of Row B is now theorem output.
3. **M7a0p/M7a1/M7b** — construct the actual finite physical measure semantics and action-variation Hamiltonian.
4. **M7c/M9p** — self-adjoint realization and direct Row-A1 lower quadratic-form/gap theorem on the same operator.
5. **S6--S8 / C1--C4** — selected analytic uniformity, physical covariance/OS representation, and actual continuum reconstruction.

## Hard boundary

Do not mark the following complete by creating another record, receipt, Boolean, or adapter:

```text
literal CMP99/CMP109 same-object identity
literal differentiated CMP116 source activity estimate
physical density -> measure weld inhabitant
physical L2 expectation semantics on that measure
literal self-adjoint finite-spacing YM Hamiltonian
Row-A1 lower bound on that same Hamiltonian
actual 4D physical cutoff -> continuum construction
actual YM = OS reconstruction identity
```

If no theorem-strength inhabitant exists, these remain mathematical hypotheses. The new normal forms make that fact sharper; they do not turn the open physical problem into a completed Clay proof.
