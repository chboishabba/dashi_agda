# Round 30 concrete addendum — literal Leray and Galerkin field

The initial Round-30 reducer left the finite viscous-plus-quadratic producer as an explicit obligation. This addendum records the concrete tranche that now discharges the algebraic and finite-fold part of that obligation.

## Literal Leray output

For every nonzero retained mode `k`, the repository’s actual projector

```text
P_k v = v - |k|^-2 (k dot v) k
```

now satisfies, by direct exact field algebra,

```text
k dot P_k v = 0,
P_k(P_k v) = P_k v.
```

The proof uses the literal `ModeInverseSquare` law and the existing machine-checked complex additive, scaling and commutative-ring identities. It does not assume a `LerayHermitianCutset` or import projector transversality as a receipt.

## Exhaustive physical output fibre

For the actual retained triad fibre at output mode `k`, every ordered term

```text
-i P_k[(u(p) dot q) u(q)]
```

is proved transverse. Finite additivity then gives

```text
k dot projectedNonlinearity(k) = 0
```

for the literal exhaustive `physicalOutputFiber`, including the repository’s soundness theorem tying every enumerated incidence to its output mode.

## Literal viscous-plus-quadratic coefficient

The concrete coefficient is now defined as

```text
F_N(u)(k)
  = -nu |k|^2 u(k)
    + projectedNonlinearity(k).
```

Input-mode transversality proves the diagonal viscous term transverse; the output-fibre theorem proves the nonlinear term transverse; their sum therefore constructs a literal `TransverseModeCoefficient`.

Mapping these coefficients over the actual retained mode list and transporting the existing nonzero-mode proof constructs a `ReconstructedPhysicalState` directly.

## State-indexed dependent field

A state-indexed system builder supplies the finite system at a dependent state and proves that its integer embedding is the fixed embedding of that carrier. The Round-30 adapter then:

1. maps the literal coefficient over the retained modes;
2. transports only across the exact embedding equality;
3. records, for every returned coefficient, its source mode and equality to the literal formula above;
4. constructs

```text
concretePhysicalGalerkinVectorField :
  ReconstructedPhysicalState F E -> ReconstructedPhysicalState F E.
```

Thus the dependent field is no longer an arbitrary raw right-hand side hidden behind a preservation record.

## Remaining concrete boundary

The only finite-field construction still upstream of this adapter is the state lookup/builder that turns a `ReconstructedPhysicalState` into the repository’s `FiniteComplex3GalerkinSystem` while proving that `velocityAt` is exactly the stored/reconstructed Fourier coefficient. After that same-object lookup is installed, the concrete coefficient field can feed the physical-coordinate and Picard–Lindelöf lane without another Galerkin preservation hypothesis.
