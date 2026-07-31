module DASHI.Physics.YangMills.BalabanClayGate4T3TwoFamilyChannelReuseExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT3PhysicalUniformFluctuationCoercivityExact as T3
import DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSumSelfAdjointExact as Sum
import DASHI.Physics.YangMills.BalabanClayGate4TwoFamilyChannelMajorantExact as Family

------------------------------------------------------------------------
-- T3 reuse of the two-family five-channel reduction.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics (1995 reprint).
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Once the T3 quadratic forms are identified with the common SU(2) and
-- resolvent majorants, all five channelwise estimates are derived.  This
-- replaces five unrelated analytic inputs by two uniform defect bounds plus
-- explicit coefficient and convention equalities.
------------------------------------------------------------------------

record T3TwoFamilyChannelInputs
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

    family : Family.TwoFamilyChannelMajorant Fluctuation Bound

    UnitState : Fluctuation → Set
    unitStateToFamily : ∀ fluctuation →
      UnitState fluctuation → Family.UnitState family fluctuation

    orderMeaning :
      Family.LessEqual (Family.algebra family)
      ≡ T3.LessEqual t3

    curvatureFormMeaning : ∀ fluctuation →
      Family.curvatureForm (Family.forms family) fluctuation
      ≡ Sum.quadraticFormAbsolute sumAlgebra
          (T3.curvatureRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation

    transportFormMeaning : ∀ fluctuation →
      Family.transportForm (Family.forms family) fluctuation
      ≡ Sum.quadraticFormAbsolute sumAlgebra
          (T3.transportRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation

    chartFormMeaning : ∀ fluctuation →
      Family.chartForm (Family.forms family) fluctuation
      ≡ Sum.quadraticFormAbsolute sumAlgebra
          (T3.chartRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation

    gaugeFormMeaning : ∀ fluctuation →
      Family.gaugeForm (Family.forms family) fluctuation
      ≡ Sum.quadraticFormAbsolute sumAlgebra
          (T3.gaugeRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation

    constraintFormMeaning : ∀ fluctuation →
      Family.constraintForm (Family.forms family) fluctuation
      ≡ Sum.quadraticFormAbsolute sumAlgebra
          (T3.constraintRemainder t3
            (T3.makeIndex t3 scale volume regime background))
          fluctuation

    curvatureBudgetMeaning :
      Family.curvatureBudget family ≡ T3.εCurvature t3
    transportBudgetMeaning :
      Family.transportBudget family ≡ T3.εTransport t3
    chartBudgetMeaning :
      Family.chartBudget family ≡ T3.εChart t3
    gaugeBudgetMeaning :
      Family.gaugeBudget family ≡ T3.εGauge t3
    constraintBudgetMeaning :
      Family.constraintBudget family ≡ T3.εConstraint t3

open T3TwoFamilyChannelInputs public

transportFamilyEstimate :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3TwoFamilyChannelInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound)
    {sourceForm targetForm sourceBudget targetBudget : Bound} →
  Family.LessEqual (Family.algebra (family inputs))
    sourceForm sourceBudget →
  sourceForm ≡ targetForm →
  sourceBudget ≡ targetBudget →
  T3.LessEqual (t3 inputs) targetForm targetBudget
transportFamilyEstimate inputs estimate formMeaning budgetMeaning =
  subst
    (λ upper → T3.LessEqual (t3 inputs) _ upper)
    budgetMeaning
    (subst
      (λ lower → T3.LessEqual (t3 inputs) lower _)
      formMeaning
      (subst
        (λ relation → relation _ _)
        (orderMeaning inputs)
        estimate))

curvatureFormBoundFromTwoFamilies :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3TwoFamilyChannelInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound)
    fluctuation → UnitState inputs fluctuation →
  T3.LessEqual (t3 inputs)
    (Sum.quadraticFormAbsolute (sumAlgebra inputs)
      (T3.curvatureRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs)
          (regime inputs) (background inputs)))
      fluctuation)
    (T3.εCurvature (t3 inputs))
curvatureFormBoundFromTwoFamilies inputs fluctuation unit =
  transportFamilyEstimate inputs
    (Family.curvatureUniformFromSU2Majorant
      (family inputs) fluctuation
      (unitStateToFamily inputs fluctuation unit))
    (curvatureFormMeaning inputs fluctuation)
    (curvatureBudgetMeaning inputs)

transportFormBoundFromTwoFamilies :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3TwoFamilyChannelInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound)
    fluctuation → UnitState inputs fluctuation →
  T3.LessEqual (t3 inputs)
    (Sum.quadraticFormAbsolute (sumAlgebra inputs)
      (T3.transportRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs)
          (regime inputs) (background inputs)))
      fluctuation)
    (T3.εTransport (t3 inputs))
transportFormBoundFromTwoFamilies inputs fluctuation unit =
  transportFamilyEstimate inputs
    (Family.transportUniformFromSU2Majorant
      (family inputs) fluctuation
      (unitStateToFamily inputs fluctuation unit))
    (transportFormMeaning inputs fluctuation)
    (transportBudgetMeaning inputs)

chartFormBoundFromTwoFamilies :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3TwoFamilyChannelInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound)
    fluctuation → UnitState inputs fluctuation →
  T3.LessEqual (t3 inputs)
    (Sum.quadraticFormAbsolute (sumAlgebra inputs)
      (T3.chartRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs)
          (regime inputs) (background inputs)))
      fluctuation)
    (T3.εChart (t3 inputs))
chartFormBoundFromTwoFamilies inputs fluctuation unit =
  transportFamilyEstimate inputs
    (Family.chartUniformFromSU2Majorant
      (family inputs) fluctuation
      (unitStateToFamily inputs fluctuation unit))
    (chartFormMeaning inputs fluctuation)
    (chartBudgetMeaning inputs)

gaugeFormBoundFromTwoFamilies :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3TwoFamilyChannelInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound)
    fluctuation → UnitState inputs fluctuation →
  T3.LessEqual (t3 inputs)
    (Sum.quadraticFormAbsolute (sumAlgebra inputs)
      (T3.gaugeRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs)
          (regime inputs) (background inputs)))
      fluctuation)
    (T3.εGauge (t3 inputs))
gaugeFormBoundFromTwoFamilies inputs fluctuation unit =
  transportFamilyEstimate inputs
    (Family.gaugeUniformFromResolventMajorant
      (family inputs) fluctuation
      (unitStateToFamily inputs fluctuation unit))
    (gaugeFormMeaning inputs fluctuation)
    (gaugeBudgetMeaning inputs)

constraintFormBoundFromTwoFamilies :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound}
    (inputs : T3TwoFamilyChannelInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound)
    fluctuation → UnitState inputs fluctuation →
  T3.LessEqual (t3 inputs)
    (Sum.quadraticFormAbsolute (sumAlgebra inputs)
      (T3.constraintRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs)
          (scale inputs) (volume inputs)
          (regime inputs) (background inputs)))
      fluctuation)
    (T3.εConstraint (t3 inputs))
constraintFormBoundFromTwoFamilies inputs fluctuation unit =
  transportFamilyEstimate inputs
    (Family.constraintUniformFromResolventMajorant
      (family inputs) fluctuation
      (unitStateToFamily inputs fluctuation unit))
    (constraintFormMeaning inputs fluctuation)
    (constraintBudgetMeaning inputs)

t3TwoFamilyFiveEstimateDischargeLevel : ProofLevel
t3TwoFamilyFiveEstimateDischargeLevel = machineChecked

physicalT3SU2FamilyIdentificationInputsLevel : ProofLevel
physicalT3SU2FamilyIdentificationInputsLevel = conditional

physicalT3ResolventFamilyIdentificationInputsLevel : ProofLevel
physicalT3ResolventFamilyIdentificationInputsLevel = conditional
