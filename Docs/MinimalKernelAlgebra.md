# Minimal kernel algebra

This module records the smallest algebraic package needed to move the DASHI ternary kernel from a bare finite set to a checkable algebraic and dynamical object, without identifying balanced ternary with `F3` and without claiming field structure.

## Carrier

The primitive alphabet is `Trit = {neg, zer, pos}`. For a finite index carrier `X`, a state is a function `X → Trit`.

The involution is pointwise sign reversal. The binary activity mask is derived:

- `false` exactly at `zer`
- `true` at `neg` and `pos`

It is therefore an observation of support, not a primitive truth carrier.

The module also proves the exact bijection between a trit and the valid support/sign carrier:

- `inactive`
- `active negative`
- `active positive`

This avoids the invalid fourth state that would arise from treating an unrestricted Boolean mask and sign bit as an ordinary Cartesian product.

## Minimal universal algebra

`MinimalKernelAlgebra Γ S` contains:

- a symmetry action of `Γ` on `S`
- an involution on `S`
- a kernel endomorphism `S → S`
- the involution law
- kernel equivariance under symmetry
- kernel equivariance under involution

No addition, multiplication, linearity, ring, module, or field axioms are assumed.

## Transformation monoid

The named operations generate words over:

- the kernel
- the involution
- symmetry actions

`evaluateWord` interprets such words as endomorphisms of `S`. Operator composition, identity, and associativity are proved pointwise. This is the precise composition algebra in which kernel orbits, fixed points, cycles, and collapse dynamics live.

## Quotient compatibility

The formalisation does not assume a primitive quotient-set construction. Instead it records an equivalence relation and proves that each named operation respects it.

A kernel descends exactly when equivalent representatives are sent to equivalent representatives. `QuotientObservation` supplies the corresponding observable map when a concrete quotient carrier is available.

## RG compatibility

`QuotientRGStep` records one fine-to-coarse square:

```text
fine state --fine kernel--> fine state
    |                            |
coarse grain                 coarse grain
    |                            |
coarse state --coarse kernel-> coarse state
```

The square is required to commute after the stated quotient observation. This is the exact meaning of “commutes up to quotient”; it is not equality of raw representatives unless the observation is the identity.

## Action / MDL extension

The bare kernel algebra does not imply that a mismatch count is monotone. `ActionDescent` is an optional extension carrying an explicit cost order and a proof that kernel application is non-increasing in the selected action or MDL cost.

Thus:

- diagnostic inconsistency may be measured without a descent theorem
- action/MDL is monotone only when `kernelNonIncreasing` is supplied

## Files

- `DASHI/Core/MinimalKernelAlgebra.agda`
- `DASHI/Core/MinimalKernelAlgebraTests.agda`

The test module instantiates the structure on `Trit` with a trivial symmetry action and identity kernel, checks the exact support/sign round trips, evaluates a generated operator word, discharges quotient compatibility, constructs an exact RG square, and supplies an explicit action-descent witness.
