module DASHI.Physics.YangMills.BalabanClayP3PrincipalFibreCoordinatesExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact nonlinear background--fluctuation coordinates on a group carrier.
--
-- The coarse field itself is the background index.  The actual fine background
-- is `backgroundFine coarse`, and the fluctuation is the left quotient
-- `backgroundFine(coarseOf U)^{-1} * U`.  Coordinate uniqueness is correctly
-- restricted to the nonlinear fibre constraint; without that premise the usual
-- unconditional `backgroundUnique` statement is false for any transitive group
-- action.
------------------------------------------------------------------------

record ExactGroupCarrier (Carrier : Set) : Set₁ where
  field
    identity : Carrier
    multiply : Carrier → Carrier → Carrier
    inverse : Carrier → Carrier

    associative : ∀ left middle right →
      multiply (multiply left middle) right
      ≡ multiply left (multiply middle right)
    leftIdentity : ∀ value → multiply identity value ≡ value
    rightIdentity : ∀ value → multiply value identity ≡ value
    leftInverse : ∀ value → multiply (inverse value) value ≡ identity
    rightInverse : ∀ value → multiply value (inverse value) ≡ identity

open ExactGroupCarrier public

record PrincipalFibreCoordinateData
    (Coarse Fine Jacobian : Set) : Set₁ where
  field
    group : ExactGroupCarrier Fine
    coarseOf : Fine → Coarse
    backgroundFine : Coarse → Fine
    backgroundIsSection : ∀ coarse →
      coarseOf (backgroundFine coarse) ≡ coarse

    SmallField : Fine → Set
    jacobianOf : Coarse → Fine → Jacobian

open PrincipalFibreCoordinateData public

reconstruct :
  ∀ {Coarse Fine Jacobian} →
  PrincipalFibreCoordinateData Coarse Fine Jacobian →
  Coarse → Fine → Fine
reconstruct dataSet coarse fluctuation =
  multiply (group dataSet) (backgroundFine dataSet coarse) fluctuation

fluctuationOf :
  ∀ {Coarse Fine Jacobian} →
  PrincipalFibreCoordinateData Coarse Fine Jacobian → Fine → Fine
fluctuationOf dataSet field =
  multiply (group dataSet)
    (inverse (group dataSet)
      (backgroundFine dataSet (coarseOf dataSet field)))
    field

FluctuationConstraint :
  ∀ {Coarse Fine Jacobian} →
  PrincipalFibreCoordinateData Coarse Fine Jacobian →
  Coarse → Fine → Set
FluctuationConstraint dataSet coarse fluctuation =
  coarseOf dataSet (reconstruct dataSet coarse fluctuation) ≡ coarse

reconstructs :
  ∀ {Coarse Fine Jacobian}
    (dataSet : PrincipalFibreCoordinateData Coarse Fine Jacobian)
    field →
  reconstruct dataSet (coarseOf dataSet field) (fluctuationOf dataSet field)
  ≡ field
reconstructs dataSet field =
  let
    groupData = group dataSet
    background = backgroundFine dataSet (coarseOf dataSet field)
  in
  trans
    (sym (associative groupData background (inverse groupData background) field))
    (trans
      (cong (λ value → multiply groupData value field)
        (rightInverse groupData background))
      (leftIdentity groupData field))

fluctuationSatisfiesConstraint :
  ∀ {Coarse Fine Jacobian}
    (dataSet : PrincipalFibreCoordinateData Coarse Fine Jacobian)
    field →
  FluctuationConstraint dataSet (coarseOf dataSet field)
    (fluctuationOf dataSet field)
fluctuationSatisfiesConstraint dataSet field =
  cong (coarseOf dataSet) (reconstructs dataSet field)

backgroundUnique :
  ∀ {Coarse Fine Jacobian}
    (dataSet : PrincipalFibreCoordinateData Coarse Fine Jacobian)
    field coarse fluctuation →
  reconstruct dataSet coarse fluctuation ≡ field →
  FluctuationConstraint dataSet coarse fluctuation →
  coarse ≡ coarseOf dataSet field
backgroundUnique dataSet field coarse fluctuation reconstruction constraint =
  trans (sym constraint) (cong (coarseOf dataSet) reconstruction)

fluctuationRecovers :
  ∀ {Coarse Fine Jacobian}
    (dataSet : PrincipalFibreCoordinateData Coarse Fine Jacobian)
    coarse fluctuation →
  FluctuationConstraint dataSet coarse fluctuation →
  fluctuationOf dataSet (reconstruct dataSet coarse fluctuation)
  ≡ fluctuation
fluctuationRecovers dataSet coarse fluctuation constraint =
  let
    groupData = group dataSet
    background = backgroundFine dataSet coarse
    canonicalCancellation :
      multiply groupData (inverse groupData background)
        (multiply groupData background fluctuation)
      ≡ fluctuation
    canonicalCancellation =
      trans
        (sym (associative groupData
          (inverse groupData background) background fluctuation))
        (trans
          (cong (λ value → multiply groupData value fluctuation)
            (leftInverse groupData background))
          (leftIdentity groupData fluctuation))
  in
  subst
    (λ selectedCoarse →
      multiply groupData
        (inverse groupData (backgroundFine dataSet selectedCoarse))
        (reconstruct dataSet coarse fluctuation)
      ≡ fluctuation)
    (sym constraint)
    canonicalCancellation

fluctuationUnique :
  ∀ {Coarse Fine Jacobian}
    (dataSet : PrincipalFibreCoordinateData Coarse Fine Jacobian)
    field coarse fluctuation →
  reconstruct dataSet coarse fluctuation ≡ field →
  FluctuationConstraint dataSet coarse fluctuation →
  fluctuation ≡ fluctuationOf dataSet field
fluctuationUnique dataSet field coarse fluctuation reconstruction constraint =
  trans
    (sym (fluctuationRecovers dataSet coarse fluctuation constraint))
    (cong (fluctuationOf dataSet) reconstruction)

coordinateJacobian :
  ∀ {Coarse Fine Jacobian} →
  PrincipalFibreCoordinateData Coarse Fine Jacobian →
  Fine → Jacobian
coordinateJacobian dataSet field =
  jacobianOf dataSet (coarseOf dataSet field) (fluctuationOf dataSet field)

jacobianExact :
  ∀ {Coarse Fine Jacobian}
    (dataSet : PrincipalFibreCoordinateData Coarse Fine Jacobian)
    field →
  jacobianOf dataSet (coarseOf dataSet field) (fluctuationOf dataSet field)
  ≡ coordinateJacobian dataSet field
jacobianExact dataSet field = refl

p3PrincipalFibreReconstructionLevel : ProofLevel
p3PrincipalFibreReconstructionLevel = machineChecked

p3PrincipalFibreConstraintLevel : ProofLevel
p3PrincipalFibreConstraintLevel = machineChecked

p3PrincipalFibreUniquenessLevel : ProofLevel
p3PrincipalFibreUniquenessLevel = machineChecked

p3PrincipalFibreJacobianIdentificationLevel : ProofLevel
p3PrincipalFibreJacobianIdentificationLevel = machineChecked

-- The remaining physical work is to prove that the literal Balaban block map and
-- selected logarithmic chart satisfy this fibre constraint on one uniform ball,
-- and to evaluate the Haar Jacobian in the shared polymer norm.
p3LiteralWilsonPrincipalFibreInstantiationLevel : ProofLevel
p3LiteralWilsonPrincipalFibreInstantiationLevel = conditional
