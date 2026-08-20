# Monster 3B actual-kernel character recognition — Round 4

This tranche is stacked on the stronger orbifold/local-module work in PR #479.
It deliberately reuses that branch's published FLM weight-two split, typed
weight-one removal, `ActualZetaSectorRecognition`, kernel-character criterion,
and concrete `C3` cocycle cancellation.  Duplicate character, cocycle, and
actual-sector interfaces introduced in the first draft were deleted.
The remaining purpose is actual-group-facing:
```text
AtlasRep MN3B
-> actual extraspecial 3-core
-> centre-to-Monster-3B alignment
-> concrete 729-state scalar-commutant theorem
-> Stone--von Neumann multiplicity forcing
-> actual recognition/evaluation promotion
-> safe inertia-character reconstruction.
```
## Actual AtlasRep group computation
The GAP producer
scripts/monster_3b_actual_kernel_structure.g
uses the documented
AllAtlasGeneratingSetInfos(name)
AtlasGroup(info)
interface.  It tries the admissible names `MN3B`,
`3^(1+12).2.Suz.2`, `3^(1+12):2.Suz.2`, and
`3^1+12.2.Suz.2`, and accepts only a constructible representation of exact
order
2859230155080499200.
It records the exact AtlasRep name and representation selected.  It then
computes `E = O_3(MN3B)` and fails unless all of the following hold:
|E|          = 1594323 = 3^13
exp(E)       = 3
|Z(E)|       = 3
E'           = Z(E)
|E/Z(E)|     = 531441 = 3^12
E/Z(E)       is elementary abelian
Z(E) - {1}   is one MN3B conjugacy orbit of size 2.
Finally, it aligns that orbit with the unique size-two order-three class of the
CTblLib table `MN3B` and checks that the stored fusion sends the class to
Monster `3B`.
This is an actual finite-group computation rather than a structure-string
receipt.  It does not construct a `196883 x 196883` Monster matrix.
## Combined kernel/restriction certificate
The renderer combines the actual-kernel output with the exact CTblLib
restriction of the Monster degree-`196883` character.  It rejects the result
unless both computations select the same MN3B class.  It checks
zeta-sector degree = 65610 = 90 * 729
3^12 * 1^2 + 2 * 729^2 = 3^13.
It emits JSON and a generated Agda module.  The generated module is an artifact,
not a committed authority file, and is passed through the same pinned Agda 2.9
checker as the source modules.
No successful AtlasRep/CTblLib/Agda run is claimed until its workflow output is
observed.
## One kernel-character owner
`Monster3BKernelCharacterCriterionExact.agda` is now the only cyclotomic
character-signature owner.  Character values remain coefficientwise in the
basis `{1,zeta,zeta^2}`.  It proves
chi_H(1)   = 729
chi_H(z)   = 729 zeta
chi_H(z^2) = 729 zeta^2
chi_H(e)   = 0 for noncentral class type
3^12 + 2 * 729^2 = 3^13
3 * 729^2 = 3^13.
It also contains the conjugate `zeta^2` signature and the ninety-fold model
signature.  An `ActualKernelCharacterCertificate` supplies complete actual
class coverage, after which the module derives identity amplitude, central
phase amplitude, and noncentral vanishing.
`Monster3BActualKernelCharacterPromotionExact.agda` combines that single owner
with the actual AtlasRep/CTblLib kernel structure.  It does not define a second
trace type.
## Concrete finite Stone--von Neumann core
`Monster3BFiniteHeisenbergCommutantExact.agda` proves the missing combinatorial
irreducibility mechanism on `X = F3^6`.
1. Trit equality is decidable.
2. Any two distinct six-trit states differ in at least one coordinate.
3. The six coordinate modulations therefore separate every distinct basis
   pair.
4. A matrix commuting with every modulation has zero off-diagonal coefficient.
5. The coordinatewise translation group is simply transitive:
   ```text
   translateBy (difference6 target source) source = target.
   ```
6. A matrix commuting with every translation has a constant diagonal.
Hence
schrodingerCommutantIsScalar
constructs a scalar-commutant certificate for every matrix satisfying the
literal modulation and translation commutation equations.  No abstract
irreducibility receipt is stored in this module.
`Monster3BFiniteStoneVonNeumannMultiplicityExact.agda` then works on a literal
finite list of irreducible constituents already classified by the finite
Stone--von Neumann theorem.  It proves
constituentDegreeSum = 729 * constituentCount
and uses standard-library multiplication cancellation to derive
constituentDegreeSum = 65610
--------------------------------
constituentCount = 90.
Thus `90` is forced after classification rather than supplied as a candidate
factor.
## Actual evaluation from the stronger recognition owner
PR #479 already defines `ActualZetaSectorRecognition ActualSector`, including
an actual/model equivalence, transported translations, modulation exponents,
projectors, Weyl relations, and fixed-point-free standard translations.
`Monster3BActualMultiplicityEvaluationFromRecognitionExact.agda` upgrades that
existing object without introducing another interface.  It constructs
actualEvaluationMap
  = fromModel o evaluateModelTensor
actualEvaluationInverse
  = recoverModelTensor o toModel.
It proves both round trips, injectivity of `toModel`, translation equivariance,
and exact recovery of the Heisenberg and `Fin 90` multiplicity coordinates.
Consequently, once actual recognition is inhabited, the map
F3^6 x Fin 90  <->  W_zeta
is already a constructive translation-equivariant isomorphism.
## Projective normalizer action
The branch reuses
Monster3BNormalizerCocycleCancellationExact.agda
from PR #479.  Its concrete `C3` phase algebra proves that a projective
Heisenberg action and the inverse-projective multiplicity action cancel on pure
tensors, producing an honest tensor action.  The remaining task is to compute
the actual inertia-group lift and its cocycle, not to restate the cancellation
algebra.
## Multiplicity character without illegal division
`Monster3BMultiplicityCharacterSafeReconstructionExact.agda` works over an
arbitrary trace algebra, including cyclotomic character values.  It intentionally
has no division operation.
Each class row must be recovered by either:
an explicit product equation on a nonzero-trace class,
or
an independent class/restriction equation on a zero-trace class.
This blocks the invalid blanket formula
chi_S(g) = chi_W(g) / chi_H(g)
where `chi_H(g)=0`.  The terminal target remains an all-class equality
chi_S = chi_12 + chi_78,
followed by an actual module intertwiner.
## Bounded VOA result inherited from PR #479
`MoonshineOrbifoldMasslessStateRemovalExact.agda` uses typed carriers, not only
dimension numerals.  It proves that the untwisted invariant and retained
twisted weight-one carriers are empty, that their direct sum is empty, and that
a nonconformal weight-two coordinate exists.  Therefore grade two is the first
positive grade in the represented `0/1/2` prefix.
It explicitly does not imply a four-dimensional Yang--Mills Hamiltonian gap.
## Exact remaining frontier
After this tranche the shortest proof-bearing order is:
1. Observe a successful AtlasRep/CTblLib/generated-Agda certificate run.
2. Connect the proved scalar-commutant theorem to the repository's finite
   complex linear-representation layer, yielding irreducibility of H_zeta.
3. Complete the abstract extraspecial uniqueness step: every irreducible with
   central character zeta is isomorphic to H_zeta.
4. Use the actual centre eigenspace and that uniqueness theorem to construct
   ActualZetaSectorRecognition W_zeta, not merely assume it.
5. Reuse the already-derived actual evaluation isomorphism to obtain
   W_zeta restricted to E = H_zeta tensor Fin(90).
6. Compute the actual projective inertia lift/cocycle on the multiplicity
   factor.
7. Reconstruct the multiplicity character on every inertia class.
8. Prove or refute S_zeta = S_12 direct-sum S_78.
9. Import genuine normalizer generators, match defining relations and traces,
   then compute kappa_r/Chern restrictions.
Further `53/54`, `196608`, `3^8`, `369`, SSP15, or symbolic decompositions remain
lower priority unless they construct an action, intertwiner, differential,
filtration, projector, or class character.
## Sources
- R. W. Barraclough and R. A. Wilson, *The Character Table of a Maximal
  Subgroup of the Monster*, DOI `10.1112/S1461157000001352`.
- R. A. Wilson, P. Walsh, R. A. Parker and S. Linton, *A computer construction
  of the Monster*, DOI `10.1515/jgth.1998.023`.
- Audrey Terras, *Fourier Analysis on Finite Groups and Applications*, DOI
  `10.1017/CBO9780511626265`.
- Scott Carnahan, *51 constructions of the Moonshine module*, DOI
  `10.4310/CNTP.2018.v12.n2.a3`.
- Michael P. Tuite, *On the relationship between monstrous Moonshine and the
  uniqueness of the Moonshine module*, DOI `10.1007/BF02099885`.
- I. M. Isaacs, *Character Theory of Finite Groups*, ISBN
  `978-0-486-68014-9`; no DOI assigned.
- Gregory Karpilovsky, *Projective Representations of Finite Groups*, ISBN
  `978-0-8247-7313-7`; no DOI assigned.
- Thomas Breuer and Simon Nickerson, AtlasRep package documentation; no DOI
  asserted.
## Validation
```bash
AGDA_JOBS=2 bash scripts/check_monster_3b_actual_kernel_character_round4.sh
The checker is fail closed: the inherited orbifold/local-module checker, GAP,
CTblLib, AtlasRep, actual kernel computation, class alignment, generated
certificate, and pinned Agda 2.9 checks are mandatory.
This tranche begins at the promotion boundary left by PR #471.  It does not add
more projector identities on the finite `F3^6 x Fin 90` model.  Its purpose is
to connect the certified Monster `3B` restriction to the actual extraspecial
kernel in the AtlasRep construction of `MN3B`, and to make the remaining
Stone--von Neumann and multiplicity-character obligations exact.
## Actual group computation
loads the AtlasRep group
3^(1+12):2.Suz.2
and computes its 3-core `E = O_3(MN3B)`.  It fails unless all of the following
hold:
|MN3B|       = 2859230155080499200
Z(E) - {1}   is one conjugacy orbit of size 2.
It then aligns that orbit with the unique size-two order-three class of the
This closes the concrete subgroup-identification seam.  It does not construct
a `196883 x 196883` matrix representation.
## Combined character certificate
The renderer combines the actual-kernel output with the existing exact
restriction of the Monster degree-`196883` character.  It checks that both
computations select the same MN3B class and derives
zeta-sector degree = 65610 = 90 * 729.
The generated certificate also checks the extraspecial degree-square identity
The generated Agda module is an artifact rather than a committed authority
file.  It is typechecked by the same pinned Agda 2.9 path as the source modules.
## Extraspecial character theorem
`Monster3BExtraspecialCharacterSignatureExact.agda` represents character values
in the formal phase basis `{1,zeta,zeta^2}` and proves the complete nonlinear
signature:
chi_H(e)   = 0 for noncentral class type.
Its norm numerator is
3 * 729^2 = 3^13,
and ninety copies have degree `65610` and zero noncentral trace.
The character-level promotion target is therefore
chi_(W_zeta restricted to E) = 90 chi_(H_zeta).
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
ev : H_zeta tensor S_zeta -> W_zeta
with a constructive inverse and `E`-equivariance.  From those data it proves
injectivity, surjectivity, and the equivariant isomorphism.  This prevents the
model evaluation map from being silently reused as the Monster intertwiner.
`Monster3BProjectiveTensorCocycleExact.agda` proves the exact cancellation law
for the inertia action.  If the Heisenberg factor has projective cocycle `c`
and the multiplicity factor has the compensating inverse multiplier, then the
balanced tensor action is genuine on pure tensors.  The missing task is now to
compute the actual cocycle/lift, not to restate why cancellation would work.
## Multiplicity character
`Monster3BMultiplicityCharacterSafeReconstructionExact.agda` blocks the unsafe
formula
on classes where `chi_H(g)=0`.  Every class must be recovered either from an
explicit nonzero-trace product equation or from an independent class/restriction
relation.  The terminal target remains an all-class equality
followed by an actual intertwiner.
## Bounded VOA side result
`MoonshineOrbifoldMasslessStateRemovalExact.agda` formalizes only the chiral
statement
(V_Lambda^+)_1 = 0
((V_Lambda^T)^+)_1 = 0
(V^natural)_1 = 0,
and records the first non-vacuum holomorphic grade as `2`.  It explicitly does
not imply a four-dimensional Yang--Mills Hamiltonian gap.
After this tranche the shortest order is:
1. Observe the successful AtlasRep/CTblLib/Agda certificate run.
2. Prove finite Stone--von Neumann uniqueness in the repository representation layer.
3. Apply it to the actual W_zeta restricted to E and obtain 90 H_zeta.
4. Construct S_zeta = Hom_E(H_zeta,W_zeta) and the actual evaluation inverse.
5. Construct the cocycle-correct inertia action on S_zeta.
6. Reconstruct its character on every inertia class.
7. Prove or refute S_zeta = S_12 direct-sum S_78.
8. Only then import genuine normalizer generators and compute kappa_r/Chern restrictions.
filtration, or class character.
The checker is fail closed: GAP, CTblLib, AtlasRep, the actual group
computation, class alignment, generated certificate, and pinned Agda 2.9 checks
are mandatory.
<!-- Disposable validation-root change for the PR-associated Round-4 workflow. -->
