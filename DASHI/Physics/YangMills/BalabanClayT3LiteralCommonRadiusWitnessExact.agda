module DASHI.Physics.YangMills.BalabanClayT3LiteralCommonRadiusWitnessExact where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3LiteralBackgroundHessianRemaindersExact as Remainder
import DASHI.Physics.YangMills.BalabanClayT3LiteralFiveRemainderConstantsExact as Constants

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Propagators and Renormalization Transformations for
-- Lattice Gauge Theories. II", Communications in Mathematical Physics 96
-- (1984), 223--250. DOI: 10.1007/BF01240221
-- Relationship: uniform local Green estimates and many-scale restrictions.
--
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355
-- Relationship: background-dependent inverse and random-walk/off-diagonal
-- decay architecture.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- One radius, one five-term constant, one coercivity margin.
------------------------------------------------------------------------

record LiteralCommonRadiusWitness
    (Background State Bound Parameter ChartState Scalar Green : Set) : Set₁ where
  field
    constants : Constants.LiteralFiveRemainderConstantProducer
      Background State Bound Parameter ChartState Scalar

    closure : Remainder.CommonRadiusCoercivityClosure Background State Bound

    sameRemainderData :
      Remainder.remainderData closure ≡ Constants.remainderData constants

    -- The finite scalar certificate.  This is the only place where the chosen
    -- chart radius is compared with the reference Hodge gap.
    canonicalRadiusMakesRemainderBelowHalfLiteral :
      Remainder.LessEqual (Constants.remainderData constants)
        (Remainder.multiply (Constants.remainderData constants)
          (Remainder.totalCoefficient (Constants.remainderData constants))
          (Remainder.radius (Constants.remainderData constants)))
        (Remainder.halfReference closure)

    -- Association and order transport needed to apply the scalar certificate
    -- to every fluctuation norm.
    coefficientRadiusAssociation : ∀ state → Set
    liftCanonicalRadiusBudgetToState : ∀ state →
      Remainder.LessEqual (Constants.remainderData constants)
        (Remainder.multiply (Constants.remainderData constants)
          (Remainder.totalCoefficient (Constants.remainderData constants))
          (Remainder.multiply (Constants.remainderData constants)
            (Remainder.radius (Constants.remainderData constants))
            (Remainder.normSq (Constants.remainderData constants) state)))
        (Remainder.multiply (Constants.remainderData constants)
          (Remainder.halfReference closure)
          (Remainder.normSq (Constants.remainderData constants) state))

    -- Physical inverse and off-diagonal decay.  The inverse norm follows from
    -- coercivity; the decay additionally owns the finite-range/random-walk
    -- decomposition and remains a distinct theorem.
    green : Background → Green
    GreenNormBound OffDiagonalDecayBound : Background → Green → Set

    physicalFluctuationGreenNormBoundLiteral : ∀ background →
      GreenNormBound background (green background)

    physicalFluctuationGreenOffDiagonalDecayLiteral : ∀ background →
      Remainder.BackgroundInRadius (Constants.remainderData constants)
        (Remainder.radius (Constants.remainderData constants)) background →
      OffDiagonalDecayBound background (green background)

open LiteralCommonRadiusWitness public

literalFiveBackgroundRemaindersBelowHalf :
  ∀ {Background State Bound Parameter ChartState Scalar Green}
    (dataSet : LiteralCommonRadiusWitness
      Background State Bound Parameter ChartState Scalar Green)
    background state →
  Remainder.BackgroundInRadius (Constants.remainderData (constants dataSet))
    (Remainder.radius (Constants.remainderData (constants dataSet))) background →
  Remainder.LessEqual (Constants.remainderData (constants dataSet))
    (Remainder.totalRemainder
      (Constants.remainderData (constants dataSet)) background state)
    (Remainder.multiply (Constants.remainderData (constants dataSet))
      (Remainder.halfReference (closure dataSet))
      (Remainder.normSq (Constants.remainderData (constants dataSet)) state))
literalFiveBackgroundRemaindersBelowHalf dataSet background state inRadius =
  Remainder.transitive (Constants.remainderData (constants dataSet))
    (Constants.literalFiveBackgroundRemainderBounds
      (constants dataSet) background state inRadius)
    (liftCanonicalRadiusBudgetToState dataSet state)

physicalSmallFieldFluctuationCoerciveLiteral :
  ∀ {Background State Bound Parameter ChartState Scalar Green}
    (dataSet : LiteralCommonRadiusWitness
      Background State Bound Parameter ChartState Scalar Green)
    background state →
  Remainder.BackgroundInRadius (Remainder.remainderData (closure dataSet))
    (Remainder.radius (Remainder.remainderData (closure dataSet))) background →
  Remainder.LessEqual (closure dataSet)
    (Remainder.multiply (closure dataSet)
      (Remainder.cPhysical (closure dataSet))
      (Remainder.normSq (Remainder.remainderData (closure dataSet)) state))
    (Remainder.physicalEnergy (closure dataSet) background state)
physicalSmallFieldFluctuationCoerciveLiteral dataSet =
  Remainder.physicalSmallFieldFluctuationCoerciveLiteral (closure dataSet)

physicalFluctuationGreenNormBoundLiteralFromRadius =
  physicalFluctuationGreenNormBoundLiteral

physicalFluctuationGreenOffDiagonalDecayLiteralFromRadius =
  physicalFluctuationGreenOffDiagonalDecayLiteral

commonRadiusScalarCertificateReductionLevel : ProofLevel
commonRadiusScalarCertificateReductionLevel = machineChecked

literalFiveRemaindersBelowHalfReductionLevel : ProofLevel
literalFiveRemaindersBelowHalfReductionLevel = machineChecked

physicalSmallFieldCoercivityFromRadiusLevel : ProofLevel
physicalSmallFieldCoercivityFromRadiusLevel = machineChecked

literalCommonRadiusNumericalInputsLevel : ProofLevel
literalCommonRadiusNumericalInputsLevel = conditional

physicalGreenOffDiagonalInputsLevel : ProofLevel
physicalGreenOffDiagonalInputsLevel = conditional
