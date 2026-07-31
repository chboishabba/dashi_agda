module DASHI.Physics.YangMills.BalabanClayGate4T3FiveChannelSumReuseExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT3PhysicalUniformFluctuationCoercivityExact as T3
import DASHI.Physics.YangMills.BalabanClayGate4SelfAdjointFormOperatorNormExact as FormNorm
import DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSumSelfAdjointExact as Sum
import DASHI.Physics.YangMills.BalabanClayGate4T3FiveChannelSelfAdjointReuseExact as T3Reuse

------------------------------------------------------------------------
-- T3 instantiation of the derived five-channel sum laws.
--
-- The actual T3 operators are used literally.  Total-remainder
-- self-adjointness and the total form triangle are derived from the physical
-- five-channel split and channelwise self-adjointness rather than requested as
-- independent inputs.
------------------------------------------------------------------------

record T3FiveChannelReducedInputs
    (Scale Volume PatchRegime Background Fluctuation Tangent Bound : Set)
    : Set₁ where
  field
    t3 : T3.SmallFieldFluctuationCoercivityData
      Scale Volume PatchRegime Background Fluctuation Tangent Bound

    scale : Scale
    volume : Volume
    regime : PatchRegime
    background : Background

    sumAlgebra : Sum.OperatorFormSumAlgebra
      (Fluctuation → Fluctuation) Fluctuation Bound

    totalRemainderSplit :
      T3.backgroundHessianRemainder t3
        (T3.makeIndex t3 scale volume regime background)
      ≡ Sum.addOperator sumAlgebra
          (T3.curvatureRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          (Sum.addOperator sumAlgebra
            (T3.transportRemainder t3
              (T3.makeIndex t3 scale volume regime background))
            (Sum.addOperator sumAlgebra
              (T3.chartRemainder t3
                (T3.makeIndex t3 scale volume regime background))
              (Sum.addOperator sumAlgebra
                (T3.gaugeRemainder t3
                  (T3.makeIndex t3 scale volume regime background))
                (T3.constraintRemainder t3
                  (T3.makeIndex t3 scale volume regime background)))))

    curvatureSelfAdjoint :
      Sum.SelfAdjoint sumAlgebra
        (T3.curvatureRemainder t3
          (T3.makeIndex t3 scale volume regime background))
    transportSelfAdjoint :
      Sum.SelfAdjoint sumAlgebra
        (T3.transportRemainder t3
          (T3.makeIndex t3 scale volume regime background))
    chartSelfAdjoint :
      Sum.SelfAdjoint sumAlgebra
        (T3.chartRemainder t3
          (T3.makeIndex t3 scale volume regime background))
    gaugeSelfAdjoint :
      Sum.SelfAdjoint sumAlgebra
        (T3.gaugeRemainder t3
          (T3.makeIndex t3 scale volume regime background))
    constraintSelfAdjoint :
      Sum.SelfAdjoint sumAlgebra
        (T3.constraintRemainder t3
          (T3.makeIndex t3 scale volume regime background))

    UnitState : Fluctuation → Set

    curvatureFormBound : ∀ fluctuation → UnitState fluctuation →
      Sum.LessEqual sumAlgebra
        (Sum.quadraticFormAbsolute sumAlgebra
          (T3.curvatureRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation)
        (T3.εCurvature t3)

    transportFormBound : ∀ fluctuation → UnitState fluctuation →
      Sum.LessEqual sumAlgebra
        (Sum.quadraticFormAbsolute sumAlgebra
          (T3.transportRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation)
        (T3.εTransport t3)

    chartFormBound : ∀ fluctuation → UnitState fluctuation →
      Sum.LessEqual sumAlgebra
        (Sum.quadraticFormAbsolute sumAlgebra
          (T3.chartRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation)
        (T3.εChart t3)

    gaugeFormBound : ∀ fluctuation → UnitState fluctuation →
      Sum.LessEqual sumAlgebra
        (Sum.quadraticFormAbsolute sumAlgebra
          (T3.gaugeRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation)
        (T3.εGauge t3)

    constraintFormBound : ∀ fluctuation → UnitState fluctuation →
      Sum.LessEqual sumAlgebra
        (Sum.quadraticFormAbsolute sumAlgebra
          (T3.constraintRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation)
        (T3.εConstraint t3)

    normData : FormNorm.SelfAdjointFormOperatorNormData
      (Fluctuation → Fluctuation) Fluctuation Bound

    unitStateMeaning : ∀ fluctuation →
      FormNorm.UnitState normData fluctuation ≡ UnitState fluctuation

    formAbsoluteMeaning : ∀ operator fluctuation →
      FormNorm.absolute normData
        (FormNorm.inner normData fluctuation
          (FormNorm.apply normData operator fluctuation))
      ≡ Sum.quadraticFormAbsolute sumAlgebra operator fluctuation

    orderMeaning : ∀ left right →
      FormNorm.LessEqual normData left right
      ≡ Sum.LessEqual sumAlgebra left right

    selfAdjointMeaning : ∀ operator →
      FormNorm.SelfAdjoint normData operator
      ≡ Sum.SelfAdjoint sumAlgebra operator

open T3FiveChannelReducedInputs public

asFiveChannelOperatorSum :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3FiveChannelReducedInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound) →
  Sum.FiveChannelOperatorSum
    (Fluctuation → Fluctuation) Fluctuation Bound
asFiveChannelOperatorSum inputs = record
  { Sum.FiveChannelOperatorSum.algebra = sumAlgebra inputs
  ; Sum.FiveChannelOperatorSum.total =
      T3.backgroundHessianRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; Sum.FiveChannelOperatorSum.curvature =
      T3.curvatureRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; Sum.FiveChannelOperatorSum.transport =
      T3.transportRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; Sum.FiveChannelOperatorSum.chart =
      T3.chartRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; Sum.FiveChannelOperatorSum.gauge =
      T3.gaugeRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; Sum.FiveChannelOperatorSum.constraint =
      T3.constraintRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; Sum.FiveChannelOperatorSum.totalMeaning = totalRemainderSplit inputs
  ; Sum.FiveChannelOperatorSum.curvatureSelfAdjoint =
      curvatureSelfAdjoint inputs
  ; Sum.FiveChannelOperatorSum.transportSelfAdjoint =
      transportSelfAdjoint inputs
  ; Sum.FiveChannelOperatorSum.chartSelfAdjoint = chartSelfAdjoint inputs
  ; Sum.FiveChannelOperatorSum.gaugeSelfAdjoint = gaugeSelfAdjoint inputs
  ; Sum.FiveChannelOperatorSum.constraintSelfAdjoint =
      constraintSelfAdjoint inputs
  }

derivedTotalRemainderSelfAdjoint :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3FiveChannelReducedInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound) →
  FormNorm.SelfAdjoint (normData inputs)
    (T3.backgroundHessianRemainder (t3 inputs)
      (T3.makeIndex (t3 inputs)
        (scale inputs) (volume inputs) (regime inputs) (background inputs)))
derivedTotalRemainderSelfAdjoint inputs =
  subst
    (λ proposition → proposition)
    (sym
      (selfAdjointMeaning inputs
        (T3.backgroundHessianRemainder (t3 inputs)
          (T3.makeIndex (t3 inputs)
            (scale inputs) (volume inputs)
            (regime inputs) (background inputs)))))
    (Sum.totalFiveChannelSelfAdjoint
      (asFiveChannelOperatorSum inputs))

asT3FiveChannelSelfAdjointInputs :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3FiveChannelReducedInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound) →
  T3Reuse.T3FiveChannelSelfAdjointInputs
    Scale Volume PatchRegime Background Fluctuation Tangent Bound
asT3FiveChannelSelfAdjointInputs inputs = record
  { T3Reuse.T3FiveChannelSelfAdjointInputs.t3 = t3 inputs
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.scale = scale inputs
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.volume = volume inputs
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.regime = regime inputs
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.background = background inputs
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.formAbsolute =
      Sum.quadraticFormAbsolute (sumAlgebra inputs)
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.UnitState = UnitState inputs
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.lessEqualTransitive =
      Sum.transitive (sumAlgebra inputs)
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.addBoundMonotone =
      Sum.addMonotone (sumAlgebra inputs)
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.totalFormTriangle =
      λ fluctuation unit →
        Sum.totalFiveChannelFormTriangle
          (asFiveChannelOperatorSum inputs) fluctuation
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.curvatureFormBound =
      curvatureFormBound inputs
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.transportFormBound =
      transportFormBound inputs
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.chartFormBound =
      chartFormBound inputs
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.gaugeFormBound =
      gaugeFormBound inputs
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.constraintFormBound =
      constraintFormBound inputs
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.normData = normData inputs
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.totalRemainderSelfAdjoint =
      derivedTotalRemainderSelfAdjoint inputs
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.unitStateMeaning =
      unitStateMeaning inputs
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.formAbsoluteMeaning =
      formAbsoluteMeaning inputs
        (T3.backgroundHessianRemainder (t3 inputs)
          (T3.makeIndex (t3 inputs)
            (scale inputs) (volume inputs)
            (regime inputs) (background inputs)))
  ; T3Reuse.T3FiveChannelSelfAdjointInputs.orderMeaning =
      orderMeaning inputs
  }

t3FiveChannelOperatorNormFromReducedInputs :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3FiveChannelReducedInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound) →
  FormNorm.LessEqual (normData inputs)
    (FormNorm.operatorNorm (normData inputs)
      (T3.backgroundHessianRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs)
          (regime inputs) (background inputs))))
    (T3.εTotal (t3 inputs))
t3FiveChannelOperatorNormFromReducedInputs inputs =
  T3Reuse.t3FiveChannelOperatorNormBelowEpsilonTotal
    (asT3FiveChannelSelfAdjointInputs inputs)

t3FiveChannelDerivedSelfAdjointnessLevel : ProofLevel
t3FiveChannelDerivedSelfAdjointnessLevel = machineChecked

t3FiveChannelDerivedFormTriangleLevel : ProofLevel
t3FiveChannelDerivedFormTriangleLevel = machineChecked

t3FiveChannelReducedOperatorNormAssemblyLevel : ProofLevel
t3FiveChannelReducedOperatorNormAssemblyLevel = machineChecked

physicalT3FiveChannelOperatorSplitInputsLevel : ProofLevel
physicalT3FiveChannelOperatorSplitInputsLevel = conditional

physicalT3ChannelSelfAdjointnessInputsLevel : ProofLevel
physicalT3ChannelSelfAdjointnessInputsLevel = conditional

physicalT3FiveAbsoluteFormEstimateInputsLevel : ProofLevel
physicalT3FiveAbsoluteFormEstimateInputsLevel = conditional
