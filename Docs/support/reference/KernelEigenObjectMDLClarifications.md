# Kernel eigen-object and MDL clarifications

This note records three narrow clarifications for the DASHI kernel formalism. It does not strengthen the repository's current theorem claims.

## Biological eigenmode analogy

Kernel-saturated fixed points and low-action periodic orbits correspond to intrinsic eigenmodes of the constrained system, analogous to the recurrent Klüver form constants observed in human visual perception, which arise from neural geometry rather than learned symbolism.

This is an analogy and empirical interpretation boundary, not a theorem identifying DASHI kernel objects with cortical dynamics.

## Diagnostic residual versus monotone action

The inconsistency count `E(s)` is diagnostic only. The monotone used in any stabilisation claim is a separately specified action or description-length functional under an admissible projection rule:

```text
A (K s) <= A s
```

Such monotonicity must be proved or supplied by the selected kernel dynamics; it does not follow merely from sign-threshold updating. Consequently, `E(K s) <= E(s)` is not a default DASHI claim.

## Exact ternary support/sign factorisation

Balanced ternary admits an exact and invertible dependent factorisation into support and gated sign:

```text
Trit  ~=  Sigma Support GatedSign
GatedSign inactive = Unit
GatedSign active   = Sign
```

The executable witness and both round-trip proofs are in `DASHI.Algebra.TritSupportSignFactor`. This establishes an exact carrier isomorphism. It does not by itself prove statistical minimality for every source model; entropy or sufficient-statistic claims require an explicit probability model.
