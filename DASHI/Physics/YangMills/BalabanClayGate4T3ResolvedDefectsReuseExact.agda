module DASHI.Physics.YangMills.BalabanClayGate4T3ResolvedDefectsReuseExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT3PhysicalUniformFluctuationCoercivityExact as T3
import DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSumSelfAdjointExact as Sum
import DASHI.Physics.YangMills.BalabanClayGate4TwoFamilyChannelMajorantExact as Family
import DASHI.Physics.YangMills.BalabanClayGate4TwoFamilyResolvedDefectsAdapterExact as Resolved
import DASHI.Physics.YangMills.BalabanClayGate4T3TwoFamilyChannelReuseExact as T3Reuse

------------------------------------------------------------------------
-- T3 five-channel estimates from component SU(2) and resolvent constants.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics (1995 reprint).
-- DOI: 10.1007/978-3-642-66282-9.
--
-- The existing T3 reuse theorem consumed a two-family majorant.  This adapter
-- constructs that majorant from the resolved Ad/dexp/dexp^-1 and second-
-- resolvent pipelines, then reuses the T3 theorem unchanged.  Therefore the
-- five uniform quadratic-form bounds are downstream consequences of component
-- norm constants and five exact form-identification equalities.
------------------------------------------------------------------------

record T3ResolvedDefectsInputs
    (SU2Operator ResolventOperator
      Scale Volume PatchRegime Background Fluctuation Tangent Bound : Set)
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

    resolved : Resolved.TwoFamilyResolvedDefectsInputs
      SU2Operator ResolventOperator Fluctuation Bound

    orderMeaning :
      Family.LessEqual
        (Resolved.algebra resolved)
      ≡ T3.LessEqual t3

    curvatureFormMeaning : ∀ fluctuation →
      Family.curvatureForm (Resolved.forms resolved) fluctuation
      ≡ Sum.quadraticFormAbsolute sumAlgebra
          (T3.curvatureRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation

    transportFormMeaning : ∀ fluctuation →
      Family.transportForm (Resolved.forms resolved) fluctuation
      ≡ Sum.quadraticFormAbsolute sumAlgebra
          (T3.transportRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation

    chartFormMeaning : ∀ fluctuation →
      Family.chartForm (Resolved.forms resolved) fluctuation
      ≡ Sum.quadraticFormAbsolute sumAlgebra
          (T3.chartRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation

    gaugeFormMeaning : ∀ fluctuation →
      Family.gaugeForm (Resolved.forms resolved) fluctuation
      ≡ Sum.quadraticFormAbsolute sumAlgebra
          (T3.gaugeRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation

    constraintFormMeaning : ∀ fluctuation →
      Family.constraintForm (Resolved.forms resolved) fluctuation
      ≡ Sum.quadraticFormAbsolute sumAlgebra
          (T3.constraintRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation

    curvatureBudgetMeaning :
      Family.curvatureBudget
        (Resolved.asTwoFamilyChannelMajorant resolved)
      ≡ T3.εCurvature t3

    transportBudgetMeaning :
      Family.transportBudget
        (Resolved.asTwoFamilyChannelMajorant resolved)
      ≡ T3.εTransport t3

    chartBudgetMeaning :
      Family.chartBudget
        (Resolved.asTwoFamilyChannelMajorant resolved)
      ≡ T3.εChart t3

    gaugeBudgetMeaning :
      Family.gaugeBudget
        (Resolved.asTwoFamilyChannelMajorant resolved)
      ≡ T3.εGauge t3

    constraintBudgetMeaning :
      Family.constraintBudget
        (Resolved.asTwoFamilyChannelMajorant resolved)
      ≡ T3.εConstraint t3

open T3ResolvedDefectsInputs public

asT3TwoFamilyChannelInputs :
  ∀ {SU2Operator ResolventOperator
      Scale Volume PatchRegime Background Fluctuation Tangent Bound} →
  T3ResolvedDefectsInputs SU2Operator ResolventOperator
    Scale Volume PatchRegime Background Fluctuation Tangent Bound →
  T3Reuse.T3TwoFamilyChannelInputs
    Scale Volume PatchRegime Background Fluctuation Tangent Bound
asT3TwoFamilyChannelInputs inputs = record
  { t3 = t3 inputs
  ; scale = scale inputs
  ; volume = volume inputs
  ; regime = regime inputs
  ; background = background inputs
  ; sumAlgebra = sumAlgebra inputs
  ; family =
      Resolved.asTwoFamilyChannelMajorant (resolved inputs)
  ; UnitState =
      Resolved.UnitState (resolved inputs)
  ; unitStateToFamily =
      λ fluctuation unit → unit
  ; orderMeaning = orderMeaning inputs
  ; curvatureFormMeaning =
      curvatureFormMeaning inputs
  ; transportFormMeaning =
      transportFormMeaning inputs
  ; chartFormMeaning =
      chartFormMeaning inputs
  ; gaugeFormMeaning =
      gaugeFormMeaning inputs
  ; constraintFormMeaning =
      constraintFormMeaning inputs
  ; curvatureBudgetMeaning =
      curvatureBudgetMeaning inputs
  ; transportBudgetMeaning =
      transportBudgetMeaning inputs
  ; chartBudgetMeaning =
      chartBudgetMeaning inputs
  ; gaugeBudgetMeaning =
      gaugeBudgetMeaning inputs
  ; constraintBudgetMeaning =
      constraintBudgetMeaning inputs
  }

curvatureBoundFromResolvedDefects :
  ∀ {SU2Operator ResolventOperator
      Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3ResolvedDefectsInputs SU2Operator ResolventOperator
      Scale Volume PatchRegime Background Fluctuation Tangent Bound)
    fluctuation → Resolved.UnitState (resolved inputs) fluctuation →
  T3.LessEqual (t3 inputs)
    (Sum.quadraticFormAbsolute (sumAlgebra inputs)
      (T3.curvatureRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs)
          (regime inputs) (background inputs))) fluctuation)
    (T3.εCurvature (t3 inputs))
curvatureBoundFromResolvedDefects inputs =
  T3Reuse.curvatureFormBoundFromTwoFamilies
    (asT3TwoFamilyChannelInputs inputs)

transportBoundFromResolvedDefects :
  ∀ {SU2Operator ResolventOperator
      Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3ResolvedDefectsInputs SU2Operator ResolventOperator
      Scale Volume PatchRegime Background Fluctuation Tangent Bound)
    fluctuation → Resolved.UnitState (resolved inputs) fluctuation →
  T3.LessEqual (t3 inputs)
    (Sum.quadraticFormAbsolute (sumAlgebra inputs)
      (T3.transportRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs)
          (regime inputs) (background inputs))) fluctuation)
    (T3.εTransport (t3 inputs))
transportBoundFromResolvedDefects inputs =
  T3Reuse.transportFormBoundFromTwoFamilies
    (asT3TwoFamilyChannelInputs inputs)

chartBoundFromResolvedDefects :
  ∀ {SU2Operator ResolventOperator
      Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3ResolvedDefectsInputs SU2Operator ResolventOperator
      Scale Volume PatchRegime Background Fluctuation Tangent Bound)
    fluctuation → Resolved.UnitState (resolved inputs) fluctuation →
  T3.LessEqual (t3 inputs)
    (Sum.quadraticFormAbsolute (sumAlgebra inputs)
      (T3.chartRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs)
          (regime inputs) (background inputs))) fluctuation)
    (T3.εChart (t3 inputs))
chartBoundFromResolvedDefects inputs =
  T3Reuse.chartFormBoundFromTwoFamilies
    (asT3TwoFamilyChannelInputs inputs)

gaugeBoundFromResolvedDefects :
  ∀ {SU2Operator ResolventOperator
      Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3ResolvedDefectsInputs SU2Operator ResolventOperator
      Scale Volume PatchRegime Background Fluctuation Tangent Bound)
    fluctuation → Resolved.UnitState (resolved inputs) fluctuation →
  T3.LessEqual (t3 inputs)
    (Sum.quadraticFormAbsolute (sumAlgebra inputs)
      (T3.gaugeRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs)
          (regime inputs) (background inputs))) fluctuation)
    (T3.εGauge (t3 inputs))
gaugeBoundFromResolvedDefects inputs =
  T3Reuse.gaugeFormBoundFromTwoFamilies
    (asT3TwoFamilyChannelInputs inputs)

constraintBoundFromResolvedDefects :
  ∀ {SU2Operator ResolventOperator
      Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3ResolvedDefectsInputs SU2Operator ResolventOperator
      Scale Volume PatchRegime Background Fluctuation Tangent Bound)
    fluctuation → Resolved.UnitState (resolved inputs) fluctuation →
  T3.LessEqual (t3 inputs)
    (Sum.quadraticFormAbsolute (sumAlgebra inputs)
      (T3.constraintRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs)
          (regime inputs) (background inputs))) fluctuation)
    (T3.εConstraint (t3 inputs))
constraintBoundFromResolvedDefects inputs =
  T3Reuse.constraintFormBoundFromTwoFamilies
    (asT3TwoFamilyChannelInputs inputs)

t3FiveChannelBoundsFromResolvedDefectsLevel : ProofLevel
t3FiveChannelBoundsFromResolvedDefectsLevel = machineChecked

physicalT3FiveFormIdentificationInputsLevel : ProofLevel
physicalT3FiveFormIdentificationInputsLevel = conditional

physicalT3ResolvedBudgetMeaningInputsLevel : ProofLevel
physicalT3ResolvedBudgetMeaningInputsLevel = conditional
