module DASHI.Physics.YangMills.BalabanSU2AdjointRadiusSquared where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_*R_; oneR)
open import DASHI.Physics.YangMills.BalabanSU2AdjointTransportExact
open import DASHI.Physics.YangMills.BalabanSU2AdjointOrderedReduction

------------------------------------------------------------------------
-- Ordered consequence of the exact quaternion displacement identity.
--
-- The previous module proves
--
--   displacement^2 <= 4 |Im q|^2 |v|^2.
--
-- This module performs the next order-theoretic step: any certified radius
-- bound |Im q|^2 <= r^2 gives the literal squared one-link estimate
--
--   displacement^2 <= 4 r^2 |v|^2.
--
-- No square-root or operator-norm passage is used.  Those are kept as a later
-- adapter because the Hessian estimates can consume this squared form directly.
------------------------------------------------------------------------

fourRadiusTimesVectorR : ℝ → ℝ → ℝ → ℝ → ℝ
fourRadiusTimesVectorR radius x y z =
  fourR *R (squareR radius *R vectorNormSqR x y z)

record SU2AdjointSquaredRadiusOrder (radius : ℝ) : Set₁ where
  field
    orderedSquares : SU2AdjointSquareOrder
    lessEqualTransitive : ∀ {left middle right} →
      LessEqual orderedSquares left middle →
      LessEqual orderedSquares middle right →
      LessEqual orderedSquares left right

    imaginaryNormSqBelowRadiusSq : ∀ b c d →
      LessEqual orderedSquares
        (imaginaryNormSqR b c d)
        (squareR radius)

    fourTimesVectorMonotone : ∀ {left right} x y z →
      LessEqual orderedSquares left right →
      LessEqual orderedSquares
        (fourR *R (left *R vectorNormSqR x y z))
        (fourR *R (right *R vectorNormSqR x y z))

open SU2AdjointSquaredRadiusOrder public

unitQuaternionAdjointDisplacementRadiusSq :
  ∀ {radius}
    (radiusOrder : SU2AdjointSquaredRadiusOrder radius) →
  ∀ a b c d x y z →
  qNormSqR a b c d ≡ oneR →
  LessEqual (orderedSquares radiusOrder)
    (adjointDisplacementSqR a b c d x y z)
    (fourRadiusTimesVectorR radius x y z)
unitQuaternionAdjointDisplacementRadiusSq radiusOrder
  a b c d x y z unit =
  lessEqualTransitive radiusOrder
    (unitQuaternionAdjointDisplacementUpper
      (orderedSquares radiusOrder)
      a b c d x y z unit)
    (fourTimesVectorMonotone radiusOrder x y z
      (imaginaryNormSqBelowRadiusSq radiusOrder b c d))

record SU2ExponentialRadiusMatch (radius : ℝ) : Set₁ where
  field
    radiusOrder : SU2AdjointSquaredRadiusOrder radius

    chartParameter : Set
    expReal expI expJ expK : chartParameter → ℝ
    inChartBall : chartParameter → Set

    exponentialUnitQuaternion : ∀ parameter →
      inChartBall parameter →
      qNormSqR
        (expReal parameter)
        (expI parameter)
        (expJ parameter)
        (expK parameter)
      ≡ oneR

    exponentialImaginarySqBelowRadiusSq : ∀ parameter →
      inChartBall parameter →
      LessEqual (orderedSquares radiusOrder)
        (imaginaryNormSqR
          (expI parameter)
          (expJ parameter)
          (expK parameter))
        (squareR radius)

open SU2ExponentialRadiusMatch public

exponentialAdjointDisplacementRadiusSq :
  ∀ {radius}
    (matching : SU2ExponentialRadiusMatch radius) →
  ∀ parameter x y z →
  inChartBall matching parameter →
  LessEqual (orderedSquares (radiusOrder matching))
    (adjointDisplacementSqR
      (expReal matching parameter)
      (expI matching parameter)
      (expJ matching parameter)
      (expK matching parameter)
      x y z)
    (fourRadiusTimesVectorR radius x y z)
exponentialAdjointDisplacementRadiusSq matching parameter x y z inBall =
  unitQuaternionAdjointDisplacementRadiusSq
    (radiusOrder matching)
    (expReal matching parameter)
    (expI matching parameter)
    (expJ matching parameter)
    (expK matching parameter)
    x y z
    (exponentialUnitQuaternion matching parameter inBall)

su2AdjointSquaredRadiusConsequenceLevel : ProofLevel
su2AdjointSquaredRadiusConsequenceLevel = machineChecked

su2ExponentialImaginaryRadiusMatchLevel : ProofLevel
su2ExponentialImaginaryRadiusMatchLevel = conditional

su2SquaredRadiusToUnsquaredOperatorNormLevel : ProofLevel
su2SquaredRadiusToUnsquaredOperatorNormLevel = conditional
