module DASHI.Physics.YangMills.BalabanSU2AdjointPointwiseRadiusSquared where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_*R_; oneR)
open import DASHI.Physics.YangMills.BalabanSU2AdjointTransportExact
open import DASHI.Physics.YangMills.BalabanSU2AdjointOrderedReduction

------------------------------------------------------------------------
-- Pointwise repair of the radius interface.
--
-- A radius package must not assert ||(b,c,d)||² ≤ r² for every triple of real
-- numbers.  The bound belongs to the selected quaternion/chart point.  This
-- module separates reusable order laws from that pointwise hypothesis.
------------------------------------------------------------------------

fourRadiusTimesVectorPointwiseR : ℝ → ℝ → ℝ → ℝ → ℝ
fourRadiusTimesVectorPointwiseR radius x y z =
  fourR *R (squareR radius *R vectorNormSqR x y z)

record SU2AdjointSquaredRadiusOrderLaws : Set₁ where
  field
    orderedSquares : SU2AdjointSquareOrder
    lessEqualTransitive : ∀ {left middle right} →
      LessEqual orderedSquares left middle →
      LessEqual orderedSquares middle right →
      LessEqual orderedSquares left right

    fourTimesVectorMonotone : ∀ {left right} x y z →
      LessEqual orderedSquares left right →
      LessEqual orderedSquares
        (fourR *R (left *R vectorNormSqR x y z))
        (fourR *R (right *R vectorNormSqR x y z))

open SU2AdjointSquaredRadiusOrderLaws public

unitQuaternionAdjointDisplacementRadiusSqPointwise :
  (laws : SU2AdjointSquaredRadiusOrderLaws) →
  ∀ radius a b c d x y z →
  qNormSqR a b c d ≡ oneR →
  LessEqual (orderedSquares laws)
    (imaginaryNormSqR b c d)
    (squareR radius) →
  LessEqual (orderedSquares laws)
    (adjointDisplacementSqR a b c d x y z)
    (fourRadiusTimesVectorPointwiseR radius x y z)
unitQuaternionAdjointDisplacementRadiusSqPointwise laws
  radius a b c d x y z unit imaginaryBelow =
  lessEqualTransitive laws
    (unitQuaternionAdjointDisplacementUpper
      (orderedSquares laws)
      a b c d x y z unit)
    (fourTimesVectorMonotone laws x y z imaginaryBelow)

record SU2ExponentialPointwiseRadiusMatch (radius : ℝ) : Set₁ where
  field
    radiusOrderLaws : SU2AdjointSquaredRadiusOrderLaws

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
      LessEqual (orderedSquares radiusOrderLaws)
        (imaginaryNormSqR
          (expI parameter)
          (expJ parameter)
          (expK parameter))
        (squareR radius)

open SU2ExponentialPointwiseRadiusMatch public

exponentialAdjointDisplacementRadiusSqPointwise :
  ∀ {radius}
    (matching : SU2ExponentialPointwiseRadiusMatch radius) →
  ∀ parameter x y z →
  inChartBall matching parameter →
  LessEqual (orderedSquares (radiusOrderLaws matching))
    (adjointDisplacementSqR
      (expReal matching parameter)
      (expI matching parameter)
      (expJ matching parameter)
      (expK matching parameter)
      x y z)
    (fourRadiusTimesVectorPointwiseR radius x y z)
exponentialAdjointDisplacementRadiusSqPointwise
  {radius} matching parameter x y z inBall =
  unitQuaternionAdjointDisplacementRadiusSqPointwise
    (radiusOrderLaws matching)
    radius
    (expReal matching parameter)
    (expI matching parameter)
    (expJ matching parameter)
    (expK matching parameter)
    x y z
    (exponentialUnitQuaternion matching parameter inBall)
    (exponentialImaginarySqBelowRadiusSq matching parameter inBall)

su2PointwiseRadiusInterfaceRepairLevel : ProofLevel
su2PointwiseRadiusInterfaceRepairLevel = machineChecked

su2PointwiseExponentialRadiusReductionLevel : ProofLevel
su2PointwiseExponentialRadiusReductionLevel = machineChecked

su2PointwiseExponentialAnalyticInputLevel : ProofLevel
su2PointwiseExponentialAnalyticInputLevel = conditional
