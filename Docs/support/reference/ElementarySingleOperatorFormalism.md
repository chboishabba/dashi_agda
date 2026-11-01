# Elementary single-operator formalism

## Source result

The intake result is Andrzej Odrzywołek, *All elementary functions from a single binary operator*, arXiv:2603.21852v2.

The binary operation is

```text
eml(x , y) = exp(x) - log(y)
```

with distinguished constant `1`.  The paper gives the grammar

```text
S ::= 1 | variable | eml(S , S)
```

and explicit encodings including

```text
exp(x) = eml(x , 1)
log(x) = eml(1 , eml(eml(1 , x) , 1))
x - y  = eml(log(x) , exp(y)).
```

The identities use complex logarithms and a chosen branch.  They are therefore not imported as unconditional equalities on an arbitrary carrier.

## Formal split

`DASHI.Foundations.ElementarySingleOperator` contains:

1. `ExpLogSubExpr`, the exact `1`/variable/`exp`/`log`/subtraction source kernel;
2. `EMLExpr`, whose only internal node is `emlM`;
3. `compileEML`, the structural compiler;
4. `EMLCompilerLaws`, the explicit branch/domain-sensitive equations;
5. `compileEML-correct`, the machine-checked structural correctness theorem;
6. `ElementaryFrontEnd`, a semantics-preserving lowering seam for a larger scientific-calculator language.

This means the repository proves the combinatorial compiler once, while a concrete complex model must still prove the analytic equations on its admissible domain.

## Ternary constant-free candidate

Version 2 names the candidate

```text
T(x , y , z) = (exp(x) / log(x)) * (log(z) / exp(y))
```

and observes that `T(x , x , x) = 1` where the divisions and logarithms are admissible.  The cited dedicated paper is still described there as “in preparation”; the source does not claim a finished constant-free universality proof.

`DASHI.Foundations.TernaryElementaryOperatorCandidate` therefore records:

- a constant-free ternary tree grammar;
- three child positions indexed by the existing `TriTruth` values `tri-low`, `tri-mid`, and `tri-high`;
- diagonal generation of a unit under an explicit admissibility predicate;
- the exact candidate formula over an abstract exp/log/multiply/divide model;
- `TernaryRepresentsEML`, the remaining translator theorem required to inherit EML universality.

The formal status is deliberately fail-closed: diagonal production of `1` is weaker than functional completeness.  The missing cut is an evaluation-preserving translation of every EML tree into a constant-free ternary tree.

## Focused regression

`DASHI.Foundations.ElementarySingleOperatorRegression` pins the concrete exp/log/sub tree shapes, the diagonal unit tree, and the canonical three-slot `TriTruth` address assignment.
