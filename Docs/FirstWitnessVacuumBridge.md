# Ternary tensor powers and the first-witness vacuum bridge

## Scope

This formalisation separates three claims that had previously been discussed together:

1. the raw DASHI carrier is an `n`-fold Cartesian power of a ternary alphabet;
2. a unique first decisive witness induces irreversible, commuting constraint operators;
3. a vacuum interpretation requires additional geometric and quantum promotion bridges.

The first two are implemented constructively. The third is represented as explicit open obligations rather than promoted from analogy.

## Ternary product

`DASHI.Foundations.TernaryTensorPower` defines

```text
TPower 0       = Unit
TPower (n + 1) = Trit × TPower n
```

and proves the factorisation isomorphism

```text
TPower (m + n) ≅ TPower m × TPower n.
```

Different blockings therefore alter indexing and coarse-graining, not the underlying state space. The aliases `M3Carrier`, `M6RelationCarrier`, and `M9ClosureCarrier` record intended roles only; they are not claims about cardinality.

## First-witness algebra

`DASHI.Foundations.FirstWitnessConstraintAlgebra` gives each state one key witness. A matching constraint changes `alive` to `dead`; no operator revives a dead state. The module proves:

- constraint idempotence;
- pairwise commutation;
- propositionally zero braid outcome.

The result captures the Euler kill-key invariant: schedule changes death time, not final membership.

A non-zero braid requires leaving at least one hypothesis, for example by introducing contextual keys, state-changing witnesses, overlapping non-idempotent updates, or amplitude-valued operations.

## Vacuum bridge

`DASHI.Physics.Vacuum.FirstWitnessVacuumBridge` models a candidate by its first failing admissibility depth.

- `nothing`: saturated relative to the represented depth tower;
- `just d`: a residue whose first decisive failure occurs at depth `d`.

It proves that saturated candidates survive every represented depth and that depth constraints commute.

This does **not** derive Einstein gravity. The module instead exposes typed obligations for:

- a base manifold and metric carrier;
- an admissible diffeomorphism action;
- locality and finite jet order;
- leading second-order equations;
- valuation-to-metric and residue-to-stress-energy maps;
- microscopic closure and Bianchi compatibility;
- for quantum gravity, a gauge-fixed positive-norm spin-2 fluctuation sector compatible with microscopic unitarity.

No constructor maps saturation alone to an Einstein or quantum-gravity result.

## Interpretation

The proved result is a commutative quotient skeleton. It provides a precise model of path-history erasure under a unique first witness. It can underlie a vacuum formalism, but the geometric and field-theoretic identifications remain separate theorem obligations.
