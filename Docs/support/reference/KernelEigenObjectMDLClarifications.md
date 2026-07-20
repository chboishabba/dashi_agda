# Kernel eigen-object and MDL clarifications

This note records narrow clarifications for the DASHI kernel formalism and connects them to existing proved carrier and MDL surfaces. It does not strengthen the repository's physics or biological theorem claims.

## Biological eigenmode analogy

Kernel-saturated fixed points and low-action periodic orbits correspond at the level of mathematical role to intrinsic modes of a constrained system, analogous to the recurrent Klüver form constants observed in human visual perception, which arise from neural geometry rather than learned symbolism.

This is an analogy and empirical interpretation boundary, not a theorem identifying DASHI kernel objects with cortical dynamics. The formal core records fixed points, finite periodic closure, and quotient-stable representatives without importing a cortical model.

## Diagnostic residual versus monotone action

The inconsistency count `E(s)` is diagnostic only. The monotone used in any stabilisation claim is a separately specified action or description-length functional under an admissible projection rule:

```text
A (K s) <= A s
```

Such monotonicity must be proved or supplied by the selected kernel dynamics; it does not follow merely from sign-threshold updating. Consequently, `E(K s) <= E(s)` is not a default DASHI claim.

`DASHI.Core.KernelEigenMDLBridge` reuses the existing `DASHI.MDL.MDLLyapunov` contract rather than defining a parallel action theory. Its `KernelActionSystem` packages a kernel, an existing `MDLFunctional`, and a proof-bearing `MDLLyapunov`; `kernelMDLMonotone` is therefore only a projection of the already supplied `decreases` field.

## Fixed, periodic, and quotient-stable objects

The formal bridge keeps three notions separate:

- `FixedPoint K s`: literal representative equality `K s ≡ s`;
- `PeriodicOrbit K s`: finite positive-period closure under iteration;
- `QuotientStable q K s`: one update preserves the quotient readout, `q (K s) ≡ q s`.

Every literal fixed point is quotient-stable under every quotient map, but quotient stability does not imply literal representative equality. This is the precise form of the earlier statement that a periodic or gauge-changing trajectory may stabilise as one class in `Q`.

## Exact ternary support/sign factorisation

Balanced ternary admits an exact and invertible dependent factorisation into support and gated sign:

```text
Trit  ~=  Sigma Support GatedSign
GatedSign inactive = Unit
GatedSign active   = Sign
```

The executable witness and both round-trip proofs are in `DASHI.Algebra.TritSupportSignFactor`. This establishes an exact carrier isomorphism. It does not by itself prove statistical minimality for every source model; entropy or sufficient-statistic claims require an explicit probability model.

The same module now proves the involution compatibility that links the algebraic and codec readings:

```text
support (inv t) = support t
encode (inv t)  = supportSignInv (encode t)
```

Thus ternary involution preserves the activity mask and reverses only the gated sign. This is the concrete cross-pollination seam between `DASHI.Algebra.Trit`, mask/sign residual coding, and involution-equivariant kernel designs; binary bitplanes remain implementation carriers rather than new semantic primitives.

## Claim boundary

These additions prove finite carrier and equality facts only. They do not establish cortical equivalence, convergence of arbitrary threshold kernels, monotonicity of `E`, Shannon optimality, or a physical interpretation of every kernel eigen-object.
