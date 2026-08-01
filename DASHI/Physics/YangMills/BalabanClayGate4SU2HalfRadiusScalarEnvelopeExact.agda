module DASHI.Physics.YangMills.BalabanClayGate4SU2HalfRadiusScalarEnvelopeExact where

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
-- Taylor targets on 0 <= theta <= 1/2.  Quotient formulas are used only away
-- from zero; the analytic continuations at zero are recorded separately.
--
-- Scalar identities use an explicit setoid equality.  This is essential for
-- the Bishop regular-sequence real backend, whose mathematical equality is not
-- Agda propositional equality.
------------------------------------------------------------------------

record OrderedTrigScalar (Scalar : Set) : Set₁ where
  field
    zero one two six twelve twentyFour : Scalar
    add subtract multiply divide : Scalar → Scalar → Scalar
    absolute negate : Scalar → Scalar
    sine cosine : Scalar → Scalar

    Equivalent LessEqual : Scalar → Scalar → Set
    Nonzero : Scalar → Set

    equivalentRefl : ∀ value → Equivalent value value
    equivalentSym : ∀ {left right} →
      Equivalent left right → Equivalent right left
    equivalentTrans : ∀ {left middle right} →
      Equivalent left middle → Equivalent middle right →
      Equivalent left right

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    lessEqualResp : ∀ {left left′ right right′} →
      Equivalent left left′ → Equivalent right right′ →
      LessEqual left right → LessEqual left′ right′

open OrderedTrigScalar public

record SU2HalfRadiusScalarEnvelope (Scalar : Set) : Set₁ where
  field
    scalar : OrderedTrigScalar Scalar

    half oneHalf oneSixth oneTwelfth oneTwentyFourth : Scalar

    halfMeaning :
      Equivalent scalar half (divide scalar (one scalar) (two scalar))
    oneHalfMeaning :
      Equivalent scalar oneHalf (divide scalar (one scalar) (two scalar))
    oneSixthMeaning :
      Equivalent scalar oneSixth (divide scalar (one scalar) (six scalar))
    oneTwelfthMeaning :
      Equivalent scalar oneTwelfth
        (divide scalar (one scalar) (twelve scalar))
    oneTwentyFourthMeaning :
      Equivalent scalar oneTwentyFourth
        (divide scalar (one scalar) (twentyFour scalar))

    InsideHalfBall : Scalar → Set
    insideImpliesNonnegative : ∀ theta → InsideHalfBall theta →
      LessEqual scalar (zero scalar) theta
    insideImpliesBelowHalf : ∀ theta → InsideHalfBall theta →
      LessEqual scalar theta half

    sinc : Scalar → Scalar
    cosc : Scalar → Scalar
    inverseDexpQuadratic : Scalar → Scalar

    sincAtZero : Equivalent scalar (sinc (zero scalar)) (one scalar)
    coscAtZero : Equivalent scalar (cosc (zero scalar)) oneHalf
    inverseDexpQuadraticAtZero :
      Equivalent scalar
        (inverseDexpQuadratic (zero scalar)) oneTwelfth

    sincMeaningAwayFromZero : ∀ theta → Nonzero scalar theta →
      Equivalent scalar (sinc theta)
        (divide scalar (sine scalar theta) theta)

    coscMeaningAwayFromZero : ∀ theta → Nonzero scalar theta →
      Equivalent scalar (cosc theta)
        (divide scalar
          (subtract scalar (one scalar) (cosine scalar theta))
          (multiply scalar theta theta))

    inverseDexpQuadraticMeaningAwayFromZero :
      ∀ theta → Nonzero scalar theta →
      Equivalent scalar (inverseDexpQuadratic theta)
        (subtract scalar
          (divide scalar (one scalar)
            (multiply scalar theta theta))
          (divide scalar
            (add scalar (one scalar) (cosine scalar theta))
            (multiply scalar (two scalar)
              (multiply scalar theta (sine scalar theta)))))

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
    bracketConstantMeaning :
      Equivalent (scalar envelope) bracketConstant (one (scalar envelope))
    adRadiusMeaning :
      Equivalent (scalar envelope) adRadius (half envelope)

    adDefectBudget dexpDefectBudget dexpInverseDefectBudget : Scalar

    AdDefectBudgetMeaning DexpDefectBudgetMeaning
      DexpInverseDefectBudgetMeaning : Set

    adDefectBudgetMeaning : AdDefectBudgetMeaning
    dexpDefectBudgetMeaning : DexpDefectBudgetMeaning
    dexpInverseDefectBudgetMeaning : DexpInverseDefectBudgetMeaning

open SU2HalfRadiusNumericalLedger public

sharedHalfRadiusFromNumericalLedger :
  ∀ {Scalar} (ledger : SU2HalfRadiusNumericalLedger Scalar) →
  Equivalent (scalar (envelope ledger))
    (adRadius ledger) (half (envelope ledger))
sharedHalfRadiusFromNumericalLedger ledger = adRadiusMeaning ledger

su2HalfRadiusScalarTargetLevel : ProofLevel
su2HalfRadiusScalarTargetLevel = machineChecked

su2HalfRadiusZeroContinuationLevel : ProofLevel
su2HalfRadiusZeroContinuationLevel = machineChecked

su2HalfRadiusSetoidEqualityLevel : ProofLevel
su2HalfRadiusSetoidEqualityLevel = machineChecked

su2HalfRadiusSingleLedgerLevel : ProofLevel
su2HalfRadiusSingleLedgerLevel = machineChecked

standardSineCosineTaylorEnvelopeSourceLevel : ProofLevel
standardSineCosineTaylorEnvelopeSourceLevel = standardImported

physicalConstructiveRealTrigInstantiationInputsLevel : ProofLevel
physicalConstructiveRealTrigInstantiationInputsLevel = conditional

physicalSU2CoefficientLipschitzInputsLevel : ProofLevel
physicalSU2CoefficientLipschitzInputsLevel = conditional
