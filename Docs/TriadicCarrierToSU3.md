# Triadic Carrier To SU(3)-Like Internal Symmetry

This note records the safe bridge from the triadic Dashi carrier to an
`SU(3)`-like internal symmetry candidate. It keeps the claim in the carrier
domain only: ternary counting + structural norms ⇒ symmetry claims, no
dynamical QCD derivation.

## 1. Carrier

The minimal Dashi-side carrier is a 3-component latent state:

`psi = (psi₁, psi₂, psi₃)`

The triadic/3-adic side supplies:

- sector decomposition `psi = (psi₁, psi₂, psi₃)`
- multiscale structured coordinates along each sector
- combinatorial grammar for discrete local carrier updates

It does **not** yet supply:

- complex/linear Hilbert structure
- Hermitian metrics
- determinant-one mixing
- dynamical gauge fields

## 2. Invariants Needed For The Lift

To move from "three sectors" to "`SU(3)`-like internal symmetry", Dashi needs
at least two extra invariant constraints.

### Hermitian quadratic conservation

There must exist a conserved, positive-definite Hermitian quadratic form `H`
on the triadic carrier:

```
H(psi) = psi† G psi
```

with `G` fixed and the admissible internal transformations obeying `U† G U = G`.

### Orientation / volume phase constraint

Internal mixing must also preserve orientated volume:

```
det(U) = 1
```

This lifts generic unitary mixing into special-unitary mixing at the carrier level.

## 3. Admissible Transformations

The correct Dashi-side definition is:

> admissible internal relabellings are exactly the transformations of the
> triplet carrier that preserve the Hermitian quadratic form and satisfy the
> determinant-one condition.

In symbolic form:

`U : psi ↦ U psi`

subject to:

- `U† G U = G`
- `det(U) = 1`

If `G` is reduced to the standard positive form, this is precisely the
`SU(3)`-like carrier-level condition.

## 4. Observable Quotient

The Dashi observable map must then remove gauge-variant carrier data and retain
only invariant composites.

Structural split:

- latent carrier sector: `psi`
- observable sector: gauge-invariant functions of `psi`

This is where the earlier projection/invariance language applies:

> only invariant composites survive the observable quotient.

That is the safe bridge from internal carrier symmetry to singlet observables.

## 5. Theorem-Style Bridge Statement

The strongest safe theorem-style statement is:

### Carrier Lift Statement

Let `X` be a Dashi latent triadic carrier with:

1. a conserved Hermitian quadratic form `H`,
2. admissible internal maps `U : psi ↦ U psi` that satisfy `U† G U = G`, and
3. `det(U) = 1`.

Then the internal symmetry acting on `X` is `SU(3)`-like at the carrier level;
the group of admissible internal transformations reduces to the special-unitary
subgroup that preserves `H`. When the observable map quotients out all
gauge-variant carrier data, only `SU(3)`-singlet composites survive.

## 6. Not Claimed

This note does not claim:

- that ternary counting alone derives the Lie algebra `su(3)`
- that the repo already contains the eight generators of `su(3)`
- that Yang-Mills dynamics have been derived
- that confinement has been proved from this carrier lift alone
- that optical colour and QCD colour are the same formal object

## 7. Safe One-Line Summary

> Triadic Dashi supplies a natural 3-sector latent carrier; conserved
> Hermitian norm plus determinant-one admissible mixing lift that carrier to an
> `SU(3)`-like internal symmetry candidate, and observable quotienting then
> explains why only invariant composites survive.
