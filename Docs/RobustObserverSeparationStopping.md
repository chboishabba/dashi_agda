# Robust observer separation and stopping margins

The static observer-refinement stack proves that once a concrete collision has
been split, later exact refinements preserve that strictness.  The quantitative
problem is different: an observer may continue to change numerically under
later approximation, sampling, truncation or scale refinement.

`DASHI.Core.RobustObserverSeparationMarginExact` adds the ordered-rational
version of the Kato-style gap-stability pattern.

Suppose the reference values satisfy

```text
left_0 + m <= right_0
```

and all later correction can move each endpoint toward the other by at most
`epsilon`:

```text
left_future  <= left_0  + epsilon
right_0 - epsilon <= right_future.
```

Then

```text
left_future + (m - 2 epsilon) <= right_future.
```

Therefore

```text
2 epsilon < m
```

implies a strictly positive surviving separator margin.

`ObserverRefinementTailStoppingExact` lifts this from one later approximation
to an arbitrary stage-indexed family covered by one remaining endpoint-tail
bound `E`:

```text
current split margin = m
remaining correction of each endpoint <= E
2 E < m
------------------------------------------
the demonstrated split survives every later covered refinement.
```

This is a stopping certificate only for the split already demonstrated.  It
does not assert that later observers are useless, that the current observer is
separating on the whole carrier, or that the numerical split has semantic or
authority significance.

The generic theorem is intentionally independent of the Yang--Mills carrier.
The source calibration is Tosio Kato, *Perturbation Theory for Linear
Operators*, DOI `10.1007/978-3-642-66282-9`; the local proof is elementary
ordered rational arithmetic.  PR #583's scale-local Cauchy-tail work supplies a
concrete motivating pattern in which a summable future correction can serve as
such an `E`, but no Yang--Mills object is identified with a generic observer.
