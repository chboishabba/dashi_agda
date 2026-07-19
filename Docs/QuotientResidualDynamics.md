# Quotient-Residual Dynamics

This note records the general mathematical layer behind the tlurey/369 trace receipts.
The trace-specific material remains useful as a source of examples, but the theorem-family is broader:

```text
Public low-dimensional surfaces are lossy quotient projections over richer latent state-spaces.
The useful mathematics is the residual structure left inside the fibres of that quotient.
```

## Core objects

Let `Ω` be a latent state-space and let

```text
q : Ω → S
```

be a public projection into a smaller surface `S`.
The projection induces an equivalence relation:

```text
x ~q y  iff  q x = q y
```

DASHI cares about the fibre residuals:

```text
q⁻¹(s)
```

because those fibres contain distinctions that the public surface cannot see.

## Promoted structural layer

The branch algebra is promotable because it is ordinary quotient/counting structure.

```text
Binary public surface:
  S = {0,1}

Hidden truth-space for two independent claims:
  Ω = {false,true} × {false,true}

Lower bound:
  |Ω| ≥ 4
```

So a public `A/B` debate is generally not equivalent to the hidden truth-space.
Repeated independent refinements generate up to `2ⁿ` hidden assignments.

## Candidate geometry layer

The following are useful coordinate systems, not truth authorities:

```text
Triadic lift:
  {-1,0,+1}

Hexadic refinement:
  Tri × Bool

Nonary sheet:
  Tri × Tri

Factor coordinates:
  prime-exponent lanes for independent residual factors

Dynamical diagnostics:
  fixed-point-like, periodic-like, bifurcation-like, chaos-like

Sheaf-style gluing:
  multiple locally valid projections may fail to glue globally
```

These geometries are candidate-only until admitted by MDL/ZKP gates.

## MDL admission

A coordinate system must pay rent in compression:

```text
L(model) + L(data | model) + penalty(model)
<
L(previous) + L(data | previous)
```

If the extra phase, prime, or dynamical carrier does not reduce total description length after penalty, it is pruned.

## ZKP/public admission

A public claim is admissible only when the witness is reconstructible and safety boundaries remain closed.
The verifier may accept structural claims such as:

```text
this trace contains recursive binary branching
```

while rejecting authority promotions such as:

```text
369 proves reality
chaos proves ontology
private-language resonance proves a public truth
```

## Implemented module

```text
DASHI/Cognition/QuotientResidualDynamics.agda
```

The module contains:

1. projections, non-injective witnesses, and fibre residual witnesses;
2. the binary debate lower-bound receipt;
3. recursive dyadic branch growth via `pow2`;
4. triadic, hexadic, and nonary candidate carriers;
5. residual-pressure diagnostics;
6. transition-geometry diagnostics;
7. prime/factor coordinate candidates;
8. sheaf-style gluing obstruction receipt;
9. MDL and ZKP gates;
10. a capstone `QuotientResidualDynamicsReceipt`.

## Locked statement

```text
Every forced simplification creates fibres.
Every fibre may contain residual truth.
Every residual needs geometry.
Every geometry must pay rent.
Every public claim needs a receipt.
```
