# DASHI/Yijing relational operators

`DASHI/Biology/DASHIYijingRelationalOperatorsExact.agda` completes the received Yijing operator layer beneath the broader round-five ternary formalism.

## Four-valued casting

The standard casting values are represented as a finite type:

```text
6 = old/changing yin
7 = young/stable yang
8 = young/stable yin
9 = old/changing yang
```

Each value has three exact projections:

```text
primary polarity
moving-line Boolean
resulting polarity
```

A six-line cast compiles to a primary ternary hexagram, a six-bit moving mask, and a resulting ternary hexagram. The canonical example is checked by definitional equality.

## Trigram decomposition and images

A six-line configuration splits into lower and upper three-line configurations, and recomposition is proved exact.

The eight received binary trigram images are represented:

```text
heaven
earth
thunder
wind / wood
water
fire
mountain
lake / marsh
```

A zero-containing DASHI trigram is typed as extending beyond the received binary eight rather than being silently assigned a classical image.

## Position and correspondence

The six positions are typed separately and mapped to developmental stages:

```text
1 entry
2 inner development
3 lower threshold
4 outer entry
5 governing centre
6 culmination
```

Positions two and five are central. Odd positions have the conventional yang expectation and even positions the conventional yin expectation. Positional correctness is represented as a structural Boolean and explicitly does not entail moral goodness.

Correspondence is the involution:

```text
1 <-> 4
2 <-> 5
3 <-> 6
```

A corresponding pair counts as opposed only when one line is nonzero negative and the other nonzero positive. Two zeros are not falsely classified as opposition.

## Transformation algebra

The module defines and proves involutivity for:

```text
reversal
whole-hexagram sign complement
upper/lower trigram exchange
```

It also defines the later nuclear extraction:

```text
(x1,x2,x3,x4,x5,x6)
  -> (x2,x3,x4,x3,x4,x5).
```

The authority boundary records that nuclear extraction is a formalized later interpretive operator, not something proved to belong to the earliest Zhouyi textual layer.

## Epistemic boundary

The checked casting and relational algebra do not entail external prediction. They provide a finite symbolic and contextual transformation system suitable for associative interpretation and PNF compilation. Historical provenance remains in the attributed round-five source atlases, including Richard Rutt's *Zhouyi: The Book of Changes* with an explicit no-DOI marker.
