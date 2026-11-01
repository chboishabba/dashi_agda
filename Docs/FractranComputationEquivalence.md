# FRACTRAN computation-equivalence boundary

This bridge formalises the distinction raised by the ELI5 discussion:

```text
same final result
    is weaker than
faithful representation of the same computation
    is weaker than
universal reduction of arbitrary programs
```

The implementation lives in:

- `DASHI/Combinatorics/FractranComputationEquivalence.agda`

## What is closed

- `SameOutcome` is an equivalence relation induced by the existing concrete `FractranCOL.run` evaluator.
- `FractranRepresentation` states the exact obligations for translating a source machine into the existing FRACTRAN carrier:
  - halting is preserved;
  - one-step transitions are preserved;
  - completed runs are preserved.
- `representation-preserves-same-outcome` proves that source-level equality of terminal states transports to FRACTRAN terminal equality.
- `FractranCatalogue` states the proof obligations for indexing many encodings under canonical keys.

## What remains open

No arbitrary-program compiler is constructed here. No claim is made that machine code, source code, FRACTRAN programs, or execution traces become identical merely because they return the same value.

The module does not promote:

- a universal JMD compiler;
- a Monster-group classification theorem;
- a token or reward mechanism;
- a `71`-fold universal proof claim.

Those ideas require separate source-bound definitions and proof witnesses before they can enter a promoted DASHI lane.

## Conceptual reading

James's intuition is represented directly:

```text
same outcome may be sufficient for ordinary use
```

JMD's stronger proposed objective becomes a typed obligation:

```text
source program
  -- encode --> FRACTRAN state

with proofs that halt, step, and run semantics are preserved.
```

Only after those witnesses exist can a canonical catalogue safely identify entries without confusing output equality with computational identity.
