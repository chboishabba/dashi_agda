module DASHI.Physics.YangMills.BalabanClayGate4T3FiveChannelSelfAdjointReuseExact where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3PhysicalUniformFluctuationCoercivityExact as T3
import DASHI.Physics.YangMills.BalabanClayGate4SelfAdjointFormOperatorNormExact as FormNorm
import DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSelfAdjointOperatorBoundExact as Five

------------------------------------------------------------------------
-- Literal T3 five-channel instantiation.
--
-- The operator names and epsilon sum are taken directly from the existing T3
-- owner.  No sixth remainder and no new scalar budget are introduced.
------------------------------------------------------------------------

record T3FiveChannelSelfAdjointInputs
    (Scale Volume PatchRegime Background Fluctuation Tangent Bound : Set)
    : Set₁ where
  field
    t3 : T3.SmallFieldFluctuationCoercivityData
      Scale Volume PatchRegime Background Fluctuation Tangent Bound

    scale : Scale
    volume : Volume
    regime : PatchRegime
    background : Background

    formAbsolute :
      (Fluctuation → Fluctuation) → Fluctuation → Bound
    UnitState : Fluctuation → Set

    lessEqualTransitive : ∀ {left middle right} →
      T3.LessEqual t3 left middle →
      T3.LessEqual t3 middle right →
      T3.LessEqual t3 left right

    addBoundMonotone : ∀ {left lower right upper} →
      T3.LessEqual t3 left lower →
      T3.LessEqual t3 right upper →
      T3.LessEqual t3
        (T3.addBound t3 left right)
        (T3.addBound t3 lower upper)

    totalFormTriangle : ∀ fluctuation → UnitState fluctuation →
      T3.LessEqual t3
        (formAbsolute
          (T3.backgroundHessianRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation)
        (T3.addBound t3
          (formAbsolute
            (T3.curvatureRemainder t3
              (T3.makeIndex t3 scale volume regime background))
            fluctuation)
          (T3.addBound t3
            (formAbsolute
              (T3.transportRemainder t3
                (T3.makeIndex t3 scale volume regime background))
              fluctuation)
            (T3.addBound t3
              (formAbsolute
                (T3.chartRemainder t3
                  (T3.makeIndex t3 scale volume regime background))
                fluctuation)
              (T3.addBound t3
                (formAbsolute
                  (T3.gaugeRemainder t3
                    (T3.makeIndex t3 scale volume regime background))
                  fluctuation)
                (formAbsolute
                  (T3.constraintRemainder t3
                    (T3.makeIndex t3 scale volume regime background))
                  fluctuation)))))

    curvatureFormBound : ∀ fluctuation → UnitState fluctuation →
      T3.LessEqual t3
        (formAbsolute
          (T3.curvatureRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation)
        (T3.εCurvature t3)

    transportFormBound : ∀ fluctuation → UnitState fluctuation →
      T3.LessEqual t3
        (formAbsolute
          (T3.transportRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation)
        (T3.εTransport t3)

    chartFormBound : ∀ fluctuation → UnitState fluctuation →
      T3.LessEqual t3
        (formAbsolute
          (T3.chartRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation)
        (T3.εChart t3)

    gaugeFormBound : ∀ fluctuation → UnitState fluctuation →
      T3.LessEqual t3
        (formAbsolute
          (T3.gaugeRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation)
        (T3.εGauge t3)

    constraintFormBound : ∀ fluctuation → UnitState fluctuation →
      T3.LessEqual t3
        (formAbsolute
          (T3.constraintRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation)
        (T3.εConstraint t3)

    normData : FormNorm.SelfAdjointFormOperatorNormData
      (Fluctuation → Fluctuation) Fluctuation Bound

    totalRemainderSelfAdjoint :
      FormNorm.SelfAdjoint normData
        (T3.backgroundHessianRemainder t3
          (T3.makeIndex t3 scale volume regime background))

    unitStateMeaning : ∀ fluctuation →
      FormNorm.UnitState normData fluctuation ≡ UnitState fluctuation

    formAbsoluteMeaning : ∀ fluctuation →
      FormNorm.absolute normData
        (FormNorm.inner normData fluctuation
          (FormNorm.apply normData
            (T3.backgroundHessianRemainder t3
              (T3.makeIndex t3 scale volume regime background))
            fluctuation))
      ≡ formAbsolute
          (T3.backgroundHessianRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation

    orderMeaning : ∀ left right →
      FormNorm.LessEqual normData left right
      ≡ T3.LessEqual t3 left right

open T3FiveChannelSelfAdjointInputs public

asFiveChannelFormBoundData :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3FiveChannelSelfAdjointInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound) →
  Five.FiveChannelFormBoundData
    (Fluctuation → Fluctuation) Fluctuation Bound
asFiveChannelFormBoundData inputs = record
  { total = T3.backgroundHessianRemainder (t3 inputs)
      (T3.makeIndex (t3 inputs)
        (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; curvature = T3.curvatureRemainder (t3 inputs)
      (T3.makeIndex (t3 inputs)
        (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; transport = T3.transportRemainder (t3 inputs)
      (T3.makeIndex (t3 inputs)
        (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; chart = T3.chartRemainder (t3 inputs)
      (T3.makeIndex (t3 inputs)
        (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; gauge = T3.gaugeRemainder (t3 inputs)
      (T3.makeIndex (t3 inputs)
        (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; constraint = T3.constraintRemainder (t3 inputs)
      (T3.makeIndex (t3 inputs)
        (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; formAbsolute = formAbsolute inputs
  ; epsilonCurvature = T3.εCurvature (t3 inputs)
  ; epsilonTransport = T3.εTransport (t3 inputs)
  ; epsilonChart = T3.εChart (t3 inputs)
  ; epsilonGauge = T3.εGauge (t3 inputs)
  ; epsilonConstraint = T3.εConstraint (t3 inputs)
  ; epsilonTotal = T3.εTotal (t3 inputs)
  ; add = T3.addBound (t3 inputs)
  ; LessEqual = T3.LessEqual (t3 inputs)
  ; UnitState = UnitState inputs
  ; transitive = lessEqualTransitive inputs
  ; addMonotone = addBoundMonotone inputs
  ; epsilonTotalMeaning = T3.εTotalSum (t3 inputs)
  ; totalFormTriangle = totalFormTriangle inputs
  ; curvatureFormBound = curvatureFormBound inputs
  ; transportFormBound = transportFormBound inputs
  ; chartFormBound = chartFormBound inputs
  ; gaugeFormBound = gaugeFormBound inputs
  ; constraintFormBound = constraintFormBound inputs
  ; TotalRemainderMeaning = λ operator → operator ≡
      T3.backgroundHessianRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; totalRemainderMeaning = refl
  }

asFiveChannelSelfAdjointNormMeaning :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3FiveChannelSelfAdjointInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound) →
  Five.FiveChannelSelfAdjointNormMeaning
    (Fluctuation → Fluctuation) Fluctuation Bound
asFiveChannelSelfAdjointNormMeaning inputs = record
  { formData = asFiveChannelFormBoundData inputs
  ; normData = normData inputs
  ; totalSelfAdjoint = totalRemainderSelfAdjoint inputs
  ; unitStateMeaning = unitStateMeaning inputs
  ; formAbsoluteMeaning = formAbsoluteMeaning inputs
  ; orderMeaning = orderMeaning inputs
  }

t3FiveChannelOperatorNormBelowEpsilonTotal :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3FiveChannelSelfAdjointInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound) →
  FormNorm.LessEqual (normData inputs)
    (FormNorm.operatorNorm (normData inputs)
      (T3.backgroundHessianRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs) (regime inputs) (background inputs))))
    (T3.εTotal (t3 inputs))
t3FiveChannelOperatorNormBelowEpsilonTotal inputs =
  Five.fiveChannelSelfAdjointOperatorNormBelowTotal
    (asFiveChannelSelfAdjointNormMeaning inputs)

t3FiveChannelLiteralInstantiationLevel : ProofLevel
t3FiveChannelLiteralInstantiationLevel = machineChecked

t3FiveChannelOperatorNormAssemblyLevel : ProofLevel
t3FiveChannelOperatorNormAssemblyLevel = machineChecked

physicalT3FiveChannelFormBoundsInputsLevel : ProofLevel
physicalT3FiveChannelFormBoundsInputsLevel = conditional

physicalT3RemainderSelfAdjointnessInputsLevel : ProofLevel
physicalT3RemainderSelfAdjointnessInputsLevel = conditional

physicalT3FiveChannelNormMeaningInputsLevel : ProofLevel
physicalT3FiveChannelNormMeaningInputsLevel = conditional
