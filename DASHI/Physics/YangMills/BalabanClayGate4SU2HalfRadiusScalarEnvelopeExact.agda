module DASHI.Physics.YangMills.BalabanClayGate4SU2HalfRadiusScalarEnvelopeExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Explicit scalar target ledger on the conservative SU(2) half-ball.
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
-- The generic fixed-radius module previously accepted unnamed coefficient
-- envelopes.  This module names the exact scalar functions and the standard
-- Taylor targets on 0 <= theta <= 1/2.  A real-analysis instantiation must prove
-- these displayed inequalities; every downstream chart and Newton constant
-- then refers to this one ledger.
------------------------------------------------------------------------

record OrderedTrigScalar (Scalar : Set) : Set₁ where
  field
    zero one two six twelve twentyFour : Scalar
    add subtract multiply divide absolute : Scalar → Scalar → Scalar
    negate : Scalar → Scalar
    sine cosine : Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

open OrderedTrigScalar public

record SU2HalfRadiusScalarEnvelope (Scalar : Set) : Set₁ where
  field
    scalar : OrderedTrigScalar Scalar

    half oneHalf oneSixth oneTwelfth oneTwentyFourth : Scalar

    halfMeaning :
      half ≡ divide scalar (one scalar) (two scalar)
    oneHalfMeaning :
      oneHalf ≡ divide scalar (one scalar) (two scalar)
    oneSixthMeaning :
      oneSixth ≡ divide scalar (one scalar) (six scalar)
    oneTwelfthMeaning :
      oneTwelfth ≡ divide scalar (one scalar) (twelve scalar)
    oneTwentyFourthMeaning :
      oneTwentyFourth
      ≡ divide scalar (one scalar) (twentyFour scalar)

    InsideHalfBall : Scalar → Set
    insideImpliesNonnegative : ∀ theta → InsideHalfBall theta →
      LessEqual scalar (zero scalar) theta
    insideImpliesBelowHalf : ∀ theta → InsideHalfBall theta →
      LessEqual scalar theta half

    sinc : Scalar → Scalar
    cosc : Scalar → Scalar
    inverseDexpQuadratic : Scalar → Scalar

    sincMeaningAwayFromZero : ∀ theta →
      sinc theta ≡ divide scalar (sine scalar theta) theta

    coscMeaningAwayFromZero : ∀ theta →
      cosc theta
      ≡ divide scalar
          (subtract scalar (one scalar) (cosine scalar theta))
          (multiply scalar theta theta)

    inverseDexpQuadraticMeaningAwayFromZero : ∀ theta →
      inverseDexpQuadratic theta
      ≡ subtract scalar
          (divide scalar (one scalar)
            (multiply scalar theta theta))
          (divide scalar
            (add scalar (one scalar) (cosine scalar theta))
            (multiply scalar (two scalar)
              (multiply scalar theta (sine scalar theta))))

    sincTaylorBound : ∀ theta → InsideHalfBall theta →
      LessEqual scalar
        (absolute scalar
          (subtract scalar (sinc theta) (one scalar)))
        (multiply scalar oneSixth
          (multiply scalar theta theta))

    coscTaylorBound : ∀ theta → InsideHalfBall theta →
      LessEqual scalar
        (absolute scalar
          (subtract scalar (cosc theta) oneHalf))
        (multiply scalar oneTwentyFourth
          (multiply scalar theta theta))

    inverseDexpQuadraticSlack : Scalar
    inverseDexpQuadraticTaylorBound :
      ∀ theta → InsideHalfBall theta →
      LessEqual scalar
        (absolute scalar
          (subtract scalar
            (inverseDexpQuadratic theta) oneTwelfth))
        (multiply scalar inverseDexpQuadraticSlack
          (multiply scalar theta theta))

    adCoefficientLipschitz dexpCoefficientLipschitz
      dexpInverseCoefficientLipschitz : Scalar

    AdCoefficientDifference : Scalar → Scalar → Set
    DexpCoefficientDifference : Scalar → Scalar → Set
    DexpInverseCoefficientDifference : Scalar → Scalar → Set

    adCoefficientDifferenceBound : ∀ left right →
      InsideHalfBall left → InsideHalfBall right →
      AdCoefficientDifference left right

    dexpCoefficientDifferenceBound : ∀ left right →
      InsideHalfBall left → InsideHalfBall right →
      DexpCoefficientDifference left right

    dexpInverseCoefficientDifferenceBound : ∀ left right →
      InsideHalfBall left → InsideHalfBall right →
      DexpInverseCoefficientDifference left right

open SU2HalfRadiusScalarEnvelope public

record SU2HalfRadiusNumericalLedger
    (Scalar : Set) : Set₁ where
  field
    envelope : SU2HalfRadiusScalarEnvelope Scalar

    bracketConstant adRadius : Scalar
    bracketConstantMeaning : bracketConstant ≡ one (scalar envelope)
    adRadiusMeaning : adRadius ≡ half envelope

    adDefectBudget dexpDefectBudget dexpInverseDefectBudget : Scalar

    AdDefectBudgetMeaning DexpDefectBudgetMeaning
      DexpInverseDefectBudgetMeaning : Set

    adDefectBudgetMeaning : AdDefectBudgetMeaning
    dexpDefectBudgetMeaning : DexpDefectBudgetMeaning
    dexpInverseDefectBudgetMeaning : DexpInverseDefectBudgetMeaning

open SU2HalfRadiusNumericalLedger public

sharedHalfRadiusFromNumericalLedger :
  ∀ {Scalar} (ledger : SU2HalfRadiusNumericalLedger Scalar) →
  adRadius ledger ≡ half (envelope ledger)
sharedHalfRadiusFromNumericalLedger ledger = adRadiusMeaning ledger

su2HalfRadiusScalarTargetLevel : ProofLevel
su2HalfRadiusScalarTargetLevel = machineChecked

su2HalfRadiusSingleLedgerLevel : ProofLevel
su2HalfRadiusSingleLedgerLevel = machineChecked

standardSineCosineTaylorEnvelopeSourceLevel : ProofLevel
standardSineCosineTaylorEnvelopeSourceLevel = standardImported

physicalConstructiveRealTrigInstantiationInputsLevel : ProofLevel
physicalConstructiveRealTrigInstantiationInputsLevel = conditional

physicalSU2CoefficientLipschitzInputsLevel : ProofLevel
physicalSU2CoefficientLipschitzInputsLevel = conditional
