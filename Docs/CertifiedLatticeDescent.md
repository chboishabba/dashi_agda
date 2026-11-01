# Certified lattice descent

`DASHI.Core.CertifiedLatticeDescent` formalises the DASHI analogue of a constrained `argmin`.

The construction is deliberately narrower than TensorFlow Lattice optimisation:

```text
TensorFlow Lattice
  numeric parameters
  -> gradient step
  -> projection into a monotonic feasible region
  -> lower predictive loss

DASHI certified lattice descent
  typed candidate surface
  -> proposed refinement
  -> admissibility witness or explicit rejection
  -> least structural pressure inside a declared search fibre
```

## Structural pressure

The pressure vector keeps six deficits separate:

- receipt deficit,
- contradiction deficit,
- independence deficit,
- temporal deficit,
- authority deficit,
- promotion risk.

`totalPressure` supplies a finite scalar ranking, but the component fields remain available so a lower total cannot erase which gate remains open.

## Lawful refinement

An `AdmissibleRefinement` proves that a proposed transition preserves:

- receipts,
- contradictions,
- authority boundaries,
- promotion gates.

A `RefinementWitness` additionally proves that total pressure does not increase.

Invalid proposals are represented by `ProjectionResult.rejected`; the core does not silently rewrite them into different claims.

## Certified argmin

For source state `s` and search fibre `F`, a `CertifiedArgmin s F` contains:

1. a chosen state `x`,
2. a proof that `x` belongs to `F`,
3. a lawful refinement witness from `s` to `x`,
4. a proof that every admissible competitor in `F` has pressure at least that of `x`.

In mathematical notation:

```text
x* = argmin { pressure(x) | F(x), admissible(s -> x) }
```

This is a least admissible witness in an explicitly bounded fibre. It is not an assertion of continuous gradient descent, convergence, uniqueness, real-world optimality, or promotion authority.

## Governance boundary

`CertifiedDescentReceipt` keeps the following fields false:

- `numericOptimizerImplemented`,
- `globalOptimalityClaimed`,
- `promotionAuthority`.

This preserves the existing boundary in `CandidateFunctionalCore`, where symbolic loss/energy/pressure surfaces do not automatically receive optimisation or minimisation authority.

## Test surface

`DASHI.Core.CertifiedLatticeDescentTests` constructs a singleton search fibre and proves its certified argmin without postulates. This is a smoke-test of the certificate shape, not a claim that a nontrivial search procedure has been implemented.
