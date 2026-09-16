# Yang--Mills BIDI cross-lane closure ledger — 2026-09-16

Status: **live proof-search bookkeeping**, not theorem authority and not a Clay-completion claim.

This ledger supplements `YMRHParetoCoordination.md` for the current Lean/Agda cross-lane closure pass. It distinguishes repository/compiler debt from genuinely uninhabited source/physical theorems.

## Current lanes

- `dashi_agda` PR #967 — source producer feeding merged #970.
- `dashi_lean4` PR #7 — vacuum/operator backward consumer plus retained BIDI theorem tranche.

## Newly paid / corrected in this closure pass

### BIDI theorem package — RETAINED / theorem-bearing upstream receipt

The supplied machine-checked `RequestProject.YangMills.BIDI.*` tranche is now retained on Lean #7 under

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

The worker's build/axiom receipt belongs to the retained supplied source. The current Lean branch head still requires its own exact-head build receipt before the new Lake/weld integration is called certified.

### M7a finite-measure carrier — NARROWED

`BalabanDensityToLiteralFiniteMeasureRound124Exact` already proves, for a supplied density/finite-measure weld,

```text
BetaDensity.densityAt scale
  -> densityToFiniteMeasure
  = Top.finiteMeasure Y group (cutoffAtScale scale).
```

Therefore the old label

```text
M7a' literal selected Balaban finite measure — wholly unpaid
```

is too coarse.

Use instead:

```text
M7a0 density -> literal finite-measure carrier equality       PAID compiler/theorem
M7a1 expectation/L2/null semantics on that SAME measure      LIVE physical semantics
```

R205 already supplies the generic finite-measure expectation/null/quotient compiler once M7a1 is inhabited.

### Row-B polymer entropy — PAID

The generic BIDI shell theorem accepted both:

```text
hact   exponential activity majorant
hcard  shell cardinality / entropy bound.
```

For the literal four-dimensional lattice, `LatticeAnimalEntropy` proves `hcard`. Lean #7 now contains RED/GREEN `Welds.YMBidiLatticeShell`, which compiles

```text
connected Z^4 lattice shell
 -> lattice4ShellCardBound
 -> far-shell exponential tail
 -> Cauchy-weighted BIDI shell estimate.
```

Thus the live Row-B residual is only the **literal differentiated CMP116 activity majorant / same-object activity identification**. Do not continue listing polymer entropy/cardinality as an independent physical hypothesis.

## Current source/correlation residual

```text
S0  selected density / actual J_L,J_R / decoupling replay             LIVE
S1  CMP99 defect = actual R407 changed factor                          LIVE
S2  exact equality of remaining R407 factors                           LIVE
S3  R409 product-difference norm = selected R406 scalar term            LIVE
S4  CMP116 positive majorants attached to that same decomposition       LIVE
S5  literal differentiated CMP116 activity satisfies source majorant    LIVE
S6  source-domain holomorphy / CMP109 analytic source theorem           LIVE theorem socket
S7  physical finite->continuum covariance convergence                   LIVE
S8  OS/spectral correlation same-object representation                  LIVE
```

Items S1--S3 are the Agda #967 R410 frontier. Existing norm/product inequalities are already compiler-owned and must not be reopened.

## Current finite physical-operator residual

```text
M7a0  density -> literal finite-measure carrier equality               PAID by R124 compiler
M7a1  expectation/L2/null semantics on SAME literal measure            LIVE
M7b   literal finite-spacing YM H_a = selected action variation         LIVE
M7c   common invariant dense core + self-adjoint realization            LIVE
M9c   bMinus<=gap -> form-gap / inverse-budget compiler                 SOURCE-WRITTEN Lean #7
M9p   literal bMinus<=gap(H_a) for SAME physical H_a                    LIVE
```

R206 already compiles the selected discrete IBP equality to symmetry on the same finite-measure pairing once the literal physical pairings/action operator/boundary convention are supplied. Symmetry is not self-adjointness; M7c remains genuine.

## Current continuum/operator residual

```text
C1 actual cutoff physical Hamiltonian family -> continuum graph limit   LIVE
C2 physical continuum self-adjoint H_infinity / normalized zero vacuum  LIVE instance
C3 actual U^YM = U^OS on a common core                                  LIVE
C4 physical spectral/OS representation identifying correlations         LIVE
```

Generic compilers are already paid:

```text
vacuum-sector form gap -> resolvent bound
uniform cutoff gap + graph limit -> continuum form gap
same evolution + common core -> equality of unbounded operators
clustering spectral data -> vacuum form gap
```

## Lean #7 focused commits from this closure pass

```text
2241359b... retain BIDI noncommutative telescope
ccbf3274... retain BIDI localization
3bab9b2d... retain BIDI resolvent defect
762df340... retain BIDI source calculus
4560368f... retain BIDI Cauchy extraction
d57765c0... retain BIDI continuum bridge
9f8f3c7f... retain bounded spectral exclusion
bc230925... retain clustering -> form gap
fd655919... retain generic polymer shell bridge
f2094154... retain BIDI witnesses
fbd18e80... retain BIDI assembly
2b40e14d... retain end-to-end chain
cde73915... retain end-to-end witness
28f5a828... retain BIDI axiom audit
fdb1543b... expose YMBidi opt-in Lake library
afb836c9... RED: lattice shell specialization
6ff69a56... discharge four-dimensional shell entropy hypothesis
794c1ad9... aggregate Welds audit sync
```

## Proof-search order after this pass

1. **R410 source identities**: source-read/identify the actual CMP99 replacement inside the literal CMP109 differentiated entry. Do not guess a single changed stage if the source expression changes more than one factor.
2. **Literal CMP116 activity majorant**: instantiate the already-proved Row-B rate/entropy machinery with the actual differentiated source activities.
3. **M7a1/M7b**: same literal finite measure -> expectation/L2 semantics -> action-variation Hamiltonian.
4. **M7c/M9p**: common core/self-adjoint realization and the Row-A1 lower form-gap inequality on that exact H_a.
5. **S6/S7/S8 + C1--C4**: source analyticity, physical covariance/OS representation, and actual cutoff-to-continuum operator construction.

## Hard boundary

The following must **not** be represented as completed merely by creating another record or adapter:

```text
literal CMP99/CMP109 same-object identity
literal differentiated CMP116 activity estimate
physical Yang--Mills L2 expectation semantics on the selected measure
literal self-adjoint finite-spacing YM Hamiltonian
bMinus lower-bounds that same Hamiltonian's vacuum form
actual 4D physical cutoff -> continuum construction
actual YM = OS evolution/reconstruction identity
```

If no theorem-strength source/repository inhabitant exists, these remain mathematical hypotheses. Closing the bookkeeping around them is not closing the Yang--Mills problem.
