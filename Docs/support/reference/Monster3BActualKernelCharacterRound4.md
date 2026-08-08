# Monster 3B actual-kernel character recognition — Round 4

This tranche begins at the promotion boundary left by PR #471.  It does not add
more projector identities on the finite `F3^6 x Fin 90` model.  Its purpose is
to connect the certified Monster `3B` restriction to the actual extraspecial
kernel in the AtlasRep construction of `MN3B`, and to make the remaining
Stone--von Neumann and multiplicity-character obligations exact.

## Actual group computation

The GAP producer

```text
scripts/monster_3b_actual_kernel_structure.g
```

loads the AtlasRep group

```text
3^(1+12):2.Suz.2
```

and computes its 3-core `E = O_3(MN3B)`.  It fails unless all of the following
hold:

```text
|MN3B|       = 2859230155080499200
|E|          = 1594323 = 3^13
exp(E)       = 3
|Z(E)|       = 3
E'           = Z(E)
|E/Z(E)|     = 531441 = 3^12
E/Z(E)       is elementary abelian
Z(E) - {1}   is one conjugacy orbit of size 2.
```

It then aligns that orbit with the unique size-two order-three class of the
CTblLib table `MN3B` and checks that the stored fusion sends the class to
Monster `3B`.

This closes the concrete subgroup-identification seam.  It does not construct
a `196883 x 196883` matrix representation.

## Combined character certificate

The renderer combines the actual-kernel output with the existing exact
restriction of the Monster degree-`196883` character.  It checks that both
computations select the same MN3B class and derives

```text
zeta-sector degree = 65610 = 90 * 729.
```

The generated certificate also checks the extraspecial degree-square identity

```text
3^12 * 1^2 + 2 * 729^2 = 3^13.
```

The generated Agda module is an artifact rather than a committed authority
file.  It is typechecked by the same pinned Agda 2.9 path as the source modules.

## Extraspecial character theorem

`Monster3BExtraspecialCharacterSignatureExact.agda` represents character values
in the formal phase basis `{1,zeta,zeta^2}` and proves the complete nonlinear
signature:

```text
chi_H(1)   = 729
chi_H(z)   = 729 zeta
chi_H(z^2) = 729 zeta^2
chi_H(e)   = 0 for noncentral class type.
```

Its norm numerator is

```text
3 * 729^2 = 3^13,
```

and ninety copies have degree `65610` and zero noncentral trace.

The character-level promotion target is therefore

```text
chi_(W_zeta restricted to E) = 90 chi_(H_zeta).
```

An actual restricted character matching this signature immediately yields all
named character consequences.  The finite Stone--von Neumann theorem is the
mathematical theorem that turns the central-character condition into this
signature; it is not replaced by dimension arithmetic.

`Monster3BFiniteStoneVonNeumannMultiplicityExact.agda` additionally proves on a
literal finite constituent list that once Stone--von Neumann classifies every
selected-central-character irreducible as degree `729`, total degree `65610`
forces exactly `90` constituents.  Thus the multiplicity is derived by natural-
number cancellation rather than stored as a proposed factor.

## Actual multiplicity-space interface

`Monster3BActualMultiplicityIntertwinerExact.agda` requires an actual evaluation
map

```text
ev : H_zeta tensor S_zeta -> W_zeta
```

with a constructive inverse and `E`-equivariance.  From those data it proves
injectivity, surjectivity, and the equivariant isomorphism.  This prevents the
model evaluation map from being silently reused as the Monster intertwiner.

## Projective normalizer action

`Monster3BProjectiveTensorCocycleExact.agda` proves the exact cancellation law
for the inertia action.  If the Heisenberg factor has projective cocycle `c`
and the multiplicity factor has the compensating inverse multiplier, then the
balanced tensor action is genuine on pure tensors.  The missing task is now to
compute the actual cocycle/lift, not to restate why cancellation would work.

## Multiplicity character

`Monster3BMultiplicityCharacterSafeReconstructionExact.agda` blocks the unsafe
formula

```text
chi_S(g) = chi_W(g) / chi_H(g)
```

on classes where `chi_H(g)=0`.  Every class must be recovered either from an
explicit nonzero-trace product equation or from an independent class/restriction
relation.  The terminal target remains an all-class equality

```text
chi_S = chi_12 + chi_78,
```

followed by an actual intertwiner.

## Bounded VOA side result

`MoonshineOrbifoldMasslessStateRemovalExact.agda` formalizes only the chiral
statement

```text
(V_Lambda^+)_1 = 0
((V_Lambda^T)^+)_1 = 0
--------------------------------
(V^natural)_1 = 0,
```

and records the first non-vacuum holomorphic grade as `2`.  It explicitly does
not imply a four-dimensional Yang--Mills Hamiltonian gap.

## Exact remaining frontier

After this tranche the shortest order is:

```text
1. Observe the successful AtlasRep/CTblLib/Agda certificate run.
2. Prove finite Stone--von Neumann uniqueness in the repository representation layer.
3. Apply it to the actual W_zeta restricted to E and obtain 90 H_zeta.
4. Construct S_zeta = Hom_E(H_zeta,W_zeta) and the actual evaluation inverse.
5. Construct the cocycle-correct inertia action on S_zeta.
6. Reconstruct its character on every inertia class.
7. Prove or refute S_zeta = S_12 direct-sum S_78.
8. Only then import genuine normalizer generators and compute kappa_r/Chern restrictions.
```

Further `53/54`, `196608`, `3^8`, `369`, SSP15, or symbolic decompositions remain
lower priority unless they construct an action, intertwiner, differential,
filtration, or class character.

## Sources

- R. W. Barraclough and R. A. Wilson, *The Character Table of a Maximal
  Subgroup of the Monster*, DOI `10.1112/S1461157000001352`.
- R. A. Wilson, P. Walsh, R. A. Parker and S. Linton, *A computer construction
  of the Monster*, DOI `10.1515/jgth.1998.023`.
- Audrey Terras, *Fourier Analysis on Finite Groups and Applications*, DOI
  `10.1017/CBO9780511626265`.
- Scott Carnahan, *51 constructions of the Moonshine module*, DOI
  `10.4310/CNTP.2018.v12.n2.a3`.
- I. M. Isaacs, *Character Theory of Finite Groups*, ISBN
  `978-0-486-68014-9`; no DOI assigned.
- Gregory Karpilovsky, *Projective Representations of Finite Groups*, ISBN
  `978-0-8247-7313-7`; no DOI assigned.

## Validation

```bash
AGDA_JOBS=2 bash scripts/check_monster_3b_actual_kernel_character_round4.sh
```

The checker is fail closed: GAP, CTblLib, AtlasRep, the actual group
computation, class alignment, generated certificate, and pinned Agda 2.9 checks
are mandatory.

<!-- Disposable validation-root change for the PR-associated Round-4 workflow. -->
