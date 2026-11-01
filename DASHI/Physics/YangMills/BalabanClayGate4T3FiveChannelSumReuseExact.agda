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
-- The actual T3 operators are used literally. Total-remainder self-adjointness
-- and the total form triangle are derived from the physical five-channel split
-- and channelwise self-adjointness.  The sum algebra's Bound addition and order
-- are explicitly identified with T3's rather than assumed definitionally equal.
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

    sumAddBoundMeaning :
      Sum.addBound sumAlgebra ≡ T3.addBound t3

    sumLessEqualMeaning :
      Sum.LessEqual sumAlgebra ≡ T3.LessEqual t3

    t3LessEqualTransitive : ∀ {left middle right} →
      T3.LessEqual t3 left middle →
      T3.LessEqual t3 middle right →
      T3.LessEqual t3 left right

    t3AddBoundMonotone : ∀ {left lower right upper} →
      T3.LessEqual t3 left lower →
      T3.LessEqual t3 right upper →
      T3.LessEqual t3
        (T3.addBound t3 left right)
        (T3.addBound t3 lower upper)

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
      T3.LessEqual t3
        (Sum.quadraticFormAbsolute sumAlgebra
          (T3.curvatureRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation)
        (T3.εCurvature t3)

    transportFormBound : ∀ fluctuation → UnitState fluctuation →
      T3.LessEqual t3
        (Sum.quadraticFormAbsolute sumAlgebra
          (T3.transportRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation)
        (T3.εTransport t3)

    chartFormBound : ∀ fluctuation → UnitState fluctuation →
      T3.LessEqual t3
        (Sum.quadraticFormAbsolute sumAlgebra
          (T3.chartRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation)
        (T3.εChart t3)

    gaugeFormBound : ∀ fluctuation → UnitState fluctuation →
      T3.LessEqual t3
        (Sum.quadraticFormAbsolute sumAlgebra
          (T3.gaugeRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation)
        (T3.εGauge t3)

    constraintFormBound : ∀ fluctuation → UnitState fluctuation →
      T3.LessEqual t3
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
      ≡ T3.LessEqual t3 left right

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
asFiveChannelOperatorSum inputs = let open Sum.FiveChannelOperatorSum in record
  { algebra = sumAlgebra inputs
  ; total =
      T3.backgroundHessianRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; curvature =
      T3.curvatureRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; transport =
      T3.transportRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; chart =
      T3.chartRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; gauge =
      T3.gaugeRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; constraint =
      T3.constraintRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs) (regime inputs) (background inputs))
  ; totalMeaning = totalRemainderSplit inputs
  ; curvatureSelfAdjoint =
      curvatureSelfAdjoint inputs
  ; transportSelfAdjoint =
      transportSelfAdjoint inputs
  ; chartSelfAdjoint = chartSelfAdjoint inputs
  ; gaugeSelfAdjoint = gaugeSelfAdjoint inputs
  ; constraintSelfAdjoint =
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

derivedTotalFormTriangleInT3Order :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3FiveChannelReducedInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound)
    fluctuation →
  T3.LessEqual (t3 inputs)
    (Sum.quadraticFormAbsolute (sumAlgebra inputs)
      (T3.backgroundHessianRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs)
          (regime inputs) (background inputs)))
      fluctuation)
    (T3.addBound (t3 inputs)
      (Sum.quadraticFormAbsolute (sumAlgebra inputs)
        (T3.curvatureRemainder (t3 inputs)
          (T3.makeIndex (t3 inputs)
            (scale inputs) (volume inputs)
            (regime inputs) (background inputs))) fluctuation)
      (T3.addBound (t3 inputs)
        (Sum.quadraticFormAbsolute (sumAlgebra inputs)
          (T3.transportRemainder (t3 inputs)
            (T3.makeIndex (t3 inputs)
              (scale inputs) (volume inputs)
              (regime inputs) (background inputs))) fluctuation)
        (T3.addBound (t3 inputs)
          (Sum.quadraticFormAbsolute (sumAlgebra inputs)
            (T3.chartRemainder (t3 inputs)
              (T3.makeIndex (t3 inputs)
                (scale inputs) (volume inputs)
                (regime inputs) (background inputs))) fluctuation)
          (T3.addBound (t3 inputs)
            (Sum.quadraticFormAbsolute (sumAlgebra inputs)
              (T3.gaugeRemainder (t3 inputs)
                (T3.makeIndex (t3 inputs)
                  (scale inputs) (volume inputs)
                  (regime inputs) (background inputs))) fluctuation)
            (Sum.quadraticFormAbsolute (sumAlgebra inputs)
              (T3.constraintRemainder (t3 inputs)
                (T3.makeIndex (t3 inputs)
                  (scale inputs) (volume inputs)
                  (regime inputs) (background inputs))) fluctuation)))))
derivedTotalFormTriangleInT3Order inputs fluctuation
  rewrite sym (sumAddBoundMeaning inputs)
        | sym (sumLessEqualMeaning inputs) =
  Sum.totalFiveChannelFormTriangle
    (asFiveChannelOperatorSum inputs) fluctuation

asT3FiveChannelSelfAdjointInputs :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3FiveChannelReducedInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound) →
  T3Reuse.T3FiveChannelSelfAdjointInputs
    Scale Volume PatchRegime Background Fluctuation Tangent Bound
asT3FiveChannelSelfAdjointInputs inputs = let open T3Reuse.T3FiveChannelSelfAdjointInputs in record
  { t3 = t3 inputs
  ; scale = scale inputs
  ; volume = volume inputs
  ; regime = regime inputs
  ; background = background inputs
  ; formAbsolute =
      Sum.quadraticFormAbsolute (sumAlgebra inputs)
  ; UnitState = UnitState inputs
  ; lessEqualTransitive =
      t3LessEqualTransitive inputs
  ; addBoundMonotone =
      t3AddBoundMonotone inputs
  ; totalFormTriangle =
      λ fluctuation unit → derivedTotalFormTriangleInT3Order inputs fluctuation
  ; curvatureFormBound =
      curvatureFormBound inputs
  ; transportFormBound =
      transportFormBound inputs
  ; chartFormBound =
      chartFormBound inputs
  ; gaugeFormBound =
      gaugeFormBound inputs
  ; constraintFormBound =
      constraintFormBound inputs
  ; normData = normData inputs
  ; totalRemainderSelfAdjoint =
      derivedTotalRemainderSelfAdjoint inputs
  ; unitStateMeaning =
      unitStateMeaning inputs
  ; formAbsoluteMeaning =
      formAbsoluteMeaning inputs
        (T3.backgroundHessianRemainder (t3 inputs)
          (T3.makeIndex (t3 inputs)
            (scale inputs) (volume inputs)
            (regime inputs) (background inputs)))
  ; orderMeaning =
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

physicalT3SumAlgebraMeaningInputsLevel : ProofLevel
physicalT3SumAlgebraMeaningInputsLevel = conditional
