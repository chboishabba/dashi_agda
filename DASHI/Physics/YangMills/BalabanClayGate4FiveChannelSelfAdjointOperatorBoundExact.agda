module DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSelfAdjointOperatorBoundExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4SelfAdjointFormOperatorNormExact as FormNorm

------------------------------------------------------------------------
-- Five-channel form aggregation.
--
-- Bałaban's CMP 109 small-field expansion estimates the remainder after the
-- quadratic normalization.  DASHI records curvature, transport, chart, gauge
-- and constraint channels.  The efficient route is:
--
--   channelwise absolute quadratic-form bounds
--     -> total absolute form bound
--     -> operator norm by self-adjoint Rayleigh characterization.
--
-- This is strictly weaker in inputs than demanding five operator-norm bounds.
------------------------------------------------------------------------

record FiveChannelFormBoundData
    (Operator State Bound : Set) : Set₁ where
  field
    total curvature transport chart gauge constraint : Operator

    formAbsolute : Operator → State → Bound
    epsilonCurvature epsilonTransport epsilonChart
      epsilonGauge epsilonConstraint epsilonTotal : Bound

    add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    UnitState : State → Set

    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (add left right) (add lower upper)

    epsilonTotalMeaning :
      epsilonTotal
      ≡ add epsilonCurvature
          (add epsilonTransport
            (add epsilonChart
              (add epsilonGauge epsilonConstraint)))

    totalFormTriangle : ∀ state → UnitState state →
      LessEqual
        (formAbsolute total state)
        (add (formAbsolute curvature state)
          (add (formAbsolute transport state)
            (add (formAbsolute chart state)
              (add (formAbsolute gauge state)
                (formAbsolute constraint state)))))

    curvatureFormBound : ∀ state → UnitState state →
      LessEqual (formAbsolute curvature state) epsilonCurvature
    transportFormBound : ∀ state → UnitState state →
      LessEqual (formAbsolute transport state) epsilonTransport
    chartFormBound : ∀ state → UnitState state →
      LessEqual (formAbsolute chart state) epsilonChart
    gaugeFormBound : ∀ state → UnitState state →
      LessEqual (formAbsolute gauge state) epsilonGauge
    constraintFormBound : ∀ state → UnitState state →
      LessEqual (formAbsolute constraint state) epsilonConstraint

    TotalRemainderMeaning : Operator → Set
    totalRemainderMeaning : TotalRemainderMeaning total

open FiveChannelFormBoundData public

fiveChannelAbsoluteFormBelowTotal :
  ∀ {Operator State Bound}
    (dataSet : FiveChannelFormBoundData Operator State Bound)
    state →
  UnitState dataSet state →
  LessEqual dataSet
    (formAbsolute dataSet (total dataSet) state)
    (epsilonTotal dataSet)
fiveChannelAbsoluteFormBelowTotal dataSet state unit =
  transitive dataSet
    (totalFormTriangle dataSet state unit)
    (subst
      (λ upper → LessEqual dataSet
        (add dataSet
          (formAbsolute dataSet (curvature dataSet) state)
          (add dataSet
            (formAbsolute dataSet (transport dataSet) state)
            (add dataSet
              (formAbsolute dataSet (chart dataSet) state)
              (add dataSet
                (formAbsolute dataSet (gauge dataSet) state)
                (formAbsolute dataSet (constraint dataSet) state))))
        upper)
      (sym (epsilonTotalMeaning dataSet))
      (addMonotone dataSet
        (curvatureFormBound dataSet state unit)
        (addMonotone dataSet
          (transportFormBound dataSet state unit)
          (addMonotone dataSet
            (chartFormBound dataSet state unit)
            (addMonotone dataSet
              (gaugeFormBound dataSet state unit)
              (constraintFormBound dataSet state unit))))))

record FiveChannelSelfAdjointNormMeaning
    (Operator State Bound : Set) : Set₁ where
  field
    formData : FiveChannelFormBoundData Operator State Bound
    normData : FormNorm.SelfAdjointFormOperatorNormData Operator State Bound

    totalSelfAdjoint :
      FormNorm.SelfAdjoint normData (total formData)

    unitStateMeaning : ∀ state →
      FormNorm.UnitState normData state ≡ UnitState formData state

    formAbsoluteMeaning : ∀ state →
      FormNorm.absolute normData
        (FormNorm.inner normData state
          (FormNorm.apply normData (total formData) state))
      ≡ formAbsolute formData (total formData) state

    orderMeaning : ∀ left right →
      FormNorm.LessEqual normData left right
      ≡ LessEqual formData left right

open FiveChannelSelfAdjointNormMeaning public

fiveChannelSelfAdjointOperatorNormBelowTotal :
  ∀ {Operator State Bound}
    (meaning : FiveChannelSelfAdjointNormMeaning Operator State Bound) →
  FormNorm.LessEqual (normData meaning)
    (FormNorm.operatorNorm (normData meaning) (total (formData meaning)))
    (epsilonTotal (formData meaning))
fiveChannelSelfAdjointOperatorNormBelowTotal meaning =
  FormNorm.selfAdjointFormBoundImpliesOperatorNormBound
    (normData meaning)
    (total (formData meaning))
    (epsilonTotal (formData meaning))
    (totalSelfAdjoint meaning)
    λ state normUnit →
      subst
        (λ lower → FormNorm.LessEqual (normData meaning) lower
          (epsilonTotal (formData meaning)))
        (sym (formAbsoluteMeaning meaning state))
        (subst
          (λ relation → relation
            (formAbsolute (formData meaning)
              (total (formData meaning)) state)
            (epsilonTotal (formData meaning)))
          (sym (orderMeaning meaning
            (formAbsolute (formData meaning)
              (total (formData meaning)) state)
            (epsilonTotal (formData meaning))))
          (fiveChannelAbsoluteFormBelowTotal
            (formData meaning) state
            (subst
              (UnitState (formData meaning))
              (unitStateMeaning meaning state)
              normUnit)))

fiveChannelAbsoluteFormAggregationLevel : ProofLevel
fiveChannelAbsoluteFormAggregationLevel = machineChecked

fiveChannelSelfAdjointOperatorNormLevel : ProofLevel
fiveChannelSelfAdjointOperatorNormLevel = machineChecked

physicalFiveChannelRemainderSplitInputsLevel : ProofLevel
physicalFiveChannelRemainderSplitInputsLevel = conditional

physicalFiveChannelAbsoluteFormBoundsInputsLevel : ProofLevel
physicalFiveChannelAbsoluteFormBoundsInputsLevel = conditional

physicalFiveChannelSelfAdjointnessInputsLevel : ProofLevel
physicalFiveChannelSelfAdjointnessInputsLevel = conditional

physicalFiveChannelNormAndOrderMeaningInputsLevel : ProofLevel
physicalFiveChannelNormAndOrderMeaningInputsLevel = conditional
