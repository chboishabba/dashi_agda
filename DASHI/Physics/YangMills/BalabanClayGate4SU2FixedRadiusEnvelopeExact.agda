module DASHI.Physics.YangMills.BalabanClayGate4SU2FixedRadiusEnvelopeExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4SU2QuadraticChartDefectExact as Quadratic

------------------------------------------------------------------------
-- One fixed-radius envelope for all three SU(2) chart defects.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- The sibling quadratic module reduces Ad-exp, dexp and dexp^-1 to one
-- polynomial in ad_X.  A physical small-field proof should not select three
-- unrelated chart balls.  The record below owns one radius, one ad_X bound and
-- three uniform coefficient budgets.  Once the scalar trigonometric estimates
-- are supplied on that ball, all three operator defects follow by transitivity.
------------------------------------------------------------------------

record SU2FixedRadiusEnvelope
    (Operator Scalar : Set) : Set₁ where
  field
    quadratic : Quadratic.SU2QuadraticChartDefects Operator Scalar

    radius : Scalar
    InsideSelectedRadius : Set
    insideSelectedRadius : InsideSelectedRadius

    adDefectEnvelope dexpDefectEnvelope dexpInverseDefectEnvelope : Scalar

    adCoefficientEnvelope :
      Quadratic.LessEqual (Quadratic.algebra quadratic)
        (Quadratic.coefficientBudget
          (Quadratic.algebra quadratic)
          (Quadratic.adLinearCoefficient quadratic)
          (Quadratic.adQuadraticCoefficient quadratic)
          (Quadratic.adBound quadratic))
        adDefectEnvelope

    dexpCoefficientEnvelope :
      Quadratic.LessEqual (Quadratic.algebra quadratic)
        (Quadratic.coefficientBudget
          (Quadratic.algebra quadratic)
          (Quadratic.dexpLinearCoefficient quadratic)
          (Quadratic.dexpQuadraticCoefficient quadratic)
          (Quadratic.adBound quadratic))
        dexpDefectEnvelope

    dexpInverseCoefficientEnvelope :
      Quadratic.LessEqual (Quadratic.algebra quadratic)
        (Quadratic.coefficientBudget
          (Quadratic.algebra quadratic)
          (Quadratic.dexpInverseLinearCoefficient quadratic)
          (Quadratic.dexpInverseQuadraticCoefficient quadratic)
          (Quadratic.adBound quadratic))
        dexpInverseDefectEnvelope

open SU2FixedRadiusEnvelope public

adMinusIdentityBelowFixedRadiusEnvelope :
  ∀ {Operator Scalar}
    (envelope : SU2FixedRadiusEnvelope Operator Scalar) →
  Quadratic.LessEqual (Quadratic.algebra (quadratic envelope))
    (Quadratic.operatorNorm (Quadratic.algebra (quadratic envelope))
      (Quadratic.adMinusIdentity (quadratic envelope)))
    (adDefectEnvelope envelope)
adMinusIdentityBelowFixedRadiusEnvelope envelope =
  Quadratic.transitive (Quadratic.algebra (quadratic envelope))
    (Quadratic.adMinusIdentityBoundFromQuadratic
      (quadratic envelope))
    (adCoefficientEnvelope envelope)

dexpMinusIdentityBelowFixedRadiusEnvelope :
  ∀ {Operator Scalar}
    (envelope : SU2FixedRadiusEnvelope Operator Scalar) →
  Quadratic.LessEqual (Quadratic.algebra (quadratic envelope))
    (Quadratic.operatorNorm (Quadratic.algebra (quadratic envelope))
      (Quadratic.dexpMinusIdentity (quadratic envelope)))
    (dexpDefectEnvelope envelope)
dexpMinusIdentityBelowFixedRadiusEnvelope envelope =
  Quadratic.transitive (Quadratic.algebra (quadratic envelope))
    (Quadratic.dexpMinusIdentityBoundFromQuadratic
      (quadratic envelope))
    (dexpCoefficientEnvelope envelope)

dexpInverseMinusIdentityBelowFixedRadiusEnvelope :
  ∀ {Operator Scalar}
    (envelope : SU2FixedRadiusEnvelope Operator Scalar) →
  Quadratic.LessEqual (Quadratic.algebra (quadratic envelope))
    (Quadratic.operatorNorm (Quadratic.algebra (quadratic envelope))
      (Quadratic.dexpInverseMinusIdentity (quadratic envelope)))
    (dexpInverseDefectEnvelope envelope)
dexpInverseMinusIdentityBelowFixedRadiusEnvelope envelope =
  Quadratic.transitive (Quadratic.algebra (quadratic envelope))
    (Quadratic.dexpInverseMinusIdentityBoundFromQuadratic
      (quadratic envelope))
    (dexpInverseCoefficientEnvelope envelope)

su2FixedRadiusSharedEnvelopeLevel : ProofLevel
su2FixedRadiusSharedEnvelopeLevel = machineChecked

su2FixedRadiusThreeDefectConsequencesLevel : ProofLevel
su2FixedRadiusThreeDefectConsequencesLevel = machineChecked

physicalSU2ScalarTrigonometricEnvelopeInputsLevel : ProofLevel
physicalSU2ScalarTrigonometricEnvelopeInputsLevel = conditional

physicalSU2RadiusToAdjointNormInputsLevel : ProofLevel
physicalSU2RadiusToAdjointNormInputsLevel = conditional
