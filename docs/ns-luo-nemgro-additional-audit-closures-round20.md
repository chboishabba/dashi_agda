# NEMGRO additional audit closures — Round 20

This supplement closes three further gaps identified in the full NEMGRO manuscript and in the supplied audit roadmap.

## Whole-space Poincaré obstruction

The manuscript uses a global step of the form

```text
||f||_2 <= C ||grad f||_2
```

for a dynamically selected projected gradient. Kernel elimination alone cannot produce this inequality on `R^3`.

For every proposed coefficient `C >= 0`, define

```text
q = C + 1,
epsilon = 1/q.
```

The exact rational development proves

```text
C epsilon + epsilon = 1,
epsilon > 0,
C epsilon < 1.
```

This is the finite algebra of a normalized long-wavelength mode. A whole-space Poincaré estimate requires a genuine spectral gap, mean condition, confinement, frequency restriction or lower-order term.

## Weak non-alignment circularity

The manuscript uses

```text
weak non-alignment -> dissipative closure
```

and later argues

```text
dissipative closure -> automatic weak non-alignment.
```

The Agda countermodel sets both endpoint propositions to the empty type. Both implications are then constructible by empty elimination, while neither endpoint is inhabited. Thus a mutual implication cycle is not a producer.

A second typed boundary separates a long-time averaged predicate from finite-time continuation. The bridge between them must be independently proved; naming a limit as `T -> infinity` cannot by itself rule out blow-up at a finite maximal time.

## Smooth `L2` approximation does not supply uniform `H1` data

For any gradient threshold `M >= 0`, define

```text
q = M + 1,
amplitude = 1/q,
frequency = q^2.
```

The perturbation's gradient amplitude is checked exactly:

```text
frequency * amplitude
  = q^2 * (1/q)
  = q
  = M + 1
  > M.
```

Thus reciprocal-amplitude, high-frequency perturbations can be arbitrarily small at the `L2` level while carrying gradient data above any prescribed threshold. Smooth initial-data convergence in `L2` therefore does not yield a uniform initial `H1` or coupled stability bound.

The manuscript's weak-solution limit would additionally need an independently proved lower-semicontinuity or compactness theorem for its cubic, eigenprojector-dependent stability functional. No such promotion is made here.

## Authority boundary

These are exact obstruction models. They do not prove or disprove every possible corrected coupled-functional argument. They show that the specific global Poincaré, implication-cycle and `L2`-approximation promotions used in the manuscript do not follow from the stated inputs.
