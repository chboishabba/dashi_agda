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

## Base369 ultrametric stability boundary

`DASHI.Core.Base369UltrametricContraction` closes the smallest concrete version of the stability reality check.

The actual carrier is a three-role balanced-ternary state:

- coarse trit
- relational trit
- fine trit

It is embedded into the already proved prefix geometry in `DASHI.Geometry.SSP369Ultrametric`. The resulting discrete ultrametric has distance:

- `3` when the coarse coordinates first disagree
- `2` when the coarse coordinates agree and the relational coordinates first disagree
- `1` when only the fine coordinates disagree
- `0` on equality

The concrete nonconstant kernel is:

```text
K(a , b , c) = (zer , zer , a)
```

It preserves the previous coarse trit as a fine residue while neutralising the two exposed coordinates. The Agda theorem proves:

```text
d(K x, K y) <= pred(d(x, y))
```

for every pair of Base369 states. This is strict one-level prefix contraction for every positive distance. The file also supplies explicit negative and positive examples showing that the kernel changes states, remains nonconstant, and contracts a real distinction.

This theorem certifies this concrete kernel only. It does **not** infer contraction for another production kernel from its name, symmetry, quotient compatibility, MDL intent, or physics interpretation. Any other kernel must inhabit `Base369ContractionCertificate K` with its own proof.

## Files

- `DASHI/Core/MinimalKernelAlgebra.agda`
- `DASHI/Core/MinimalKernelAlgebraTests.agda`
- `DASHI/Core/Base369UltrametricContraction.agda`
- `DASHI/Geometry/SSP369Ultrametric.agda`

The test module instantiates the minimal algebra on `Trit` with a trivial symmetry action and identity kernel, checks the exact support/sign round trips, evaluates a generated operator word, discharges quotient compatibility, constructs an exact RG square, and supplies an explicit action-descent witness. The focused workflow also checks the Base369 ultrametric contraction module with Agda 2.9.
