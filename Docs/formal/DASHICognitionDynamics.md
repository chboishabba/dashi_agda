# DASHI cognition dynamics formalisation

This tranche formalises the classical dynamical-systems reading of the attached
DASHI cognition note. It deliberately does **not** promote a quantum-mind
hypothesis.

## Checked module surface

- `DASHI.Cognition.CompressionAttractor`
  - defines compression equivalence as equality after a coarse map;
  - defines an exact finite-settling compression-attractor contract;
  - instantiates it on the existing many-to-one DASHI ternary block;
  - proves a concrete strict-compression witness from two distinct zero-fibre
    microstates.

- `DASHI.Control.DynamicalTernarySignal`
  - implements a dead-zone trend classifier;
  - separates margin state from margin velocity;
  - constructs the literal `Trit × Trit` nine-state control surface;
  - separately constructs the ternary-plus-binary six-state surface.

- `DASHI.Cognition.ResponseKink`
  - formalises facilitation before suppression;
  - includes a concrete `0 -> 1 -> 2 -> 1` recruitment/selection/overload
    witness;
  - does not assert that unmodified GELU is non-monotone.

- `DASHI.Cognition.KepplerAdmissibility`
  - gives different result types to descriptive, parametric, and causal
    Keppler roles;
  - checks examples where a moved boundary or altered state changes the
    ternary admissibility class;
  - keeps substrate claims outside the theorem.

- `DASHI.Cognition.MicrocolumnPhase`
  - defines a finite aligned-ensemble order-parameter proxy;
  - proves below/critical/above threshold witnesses;
  - describes a classical mesoscopic collective state, not literal quantum
    coherence.

- `DASHI.Cognition.CuspCompressionModel`
  - implements the exact classifier comparing `4 * r^3` with `27 * h^2`;
  - proves generically that `r = 3a^2`, `|h| = 2a^3` lies on the fold;
  - verifies `27 = 3^3` and the coefficient balance;
  - stores the scaled potential `4V = x^4 - 2rx^2 - 4hx` and checks its
    derivative magnitudes.

- `DASHI.Cognition.PatternGenerator`
  - represents motifs as compressed outputs of parameterised flows;
  - keeps topology and symmetry explicit;
  - includes exact stripe, lattice, spiral, and tunnel witnesses without
    treating literal stored images as the explanation.

- `DASHI.Cognition.DASHICognitionDynamicsRegression`
  - imports the complete tranche and packages the non-promotion boundary.

## Canonical architecture

The implemented separation is

```text
physical substrate
    !=
mesoscopic dynamics
    !=
ternary semantic quotient
```

and the checked route is

```text
high-dimensional / microstate carrier
    -> many-to-one compression
    -> admissibility margin
    -> state trit x velocity trit
    -> cusp-regime classifier
    -> functionally generated perceptual motif
```

The zero trit is not an accidental exact equality. In the dynamical signal it
is an inclusive dead zone, and in the cusp model it is the repeated-root
boundary.

## Claim boundary

The modules prove finite algebraic, combinatorial, and semiring identities.
They do not prove that a biological cortex instantiates the models, that the
finite coherence count is a complete neural order parameter, that a particular
activation function is empirically correct, or that quantum coherence causes
consciousness. Those are empirical or analytic bridges that require separate
evidence and theorem packages.
