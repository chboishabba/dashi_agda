module DASHI.Physics.YangMills.BalabanClayGate4TwoFamilyResolvedResolventAdapterExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4TwoFamilyChannelMajorantExact as Family
import DASHI.Physics.YangMills.BalabanClayGate4ResolventDefectPipelineExact as Resolvent
import DASHI.Physics.YangMills.BalabanClayGate4ResolventDefectOnUnitStateExact as UnitResolvent

------------------------------------------------------------------------
-- Two-family majorant with the resolvent estimate derived, not assumed.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics (1995 reprint).
-- DOI: 10.1007/978-3-642-66282-9.
--
-- The original two-family carrier accepted the uniform resolvent defect as a
-- field.  This adapter replaces that field by the exact second-resolvent norm
-- pipeline and the unit-state action theorem.  Gauge and constraint estimates
-- therefore consume one computed defect budget literally.
------------------------------------------------------------------------

record TwoFamilyResolvedResolventInputs
    (Operator Vector Bound : Set) : Set₁ where
  field
    algebra : Family.OrderedScaleAlgebra Bound
    forms : Family.FiveChannelForms Vector Bound

    UnitState : Vector → Set

    su2Defect : Vector → Bound
    su2DefectBudget : Bound

    resolventData :
      UnitResolvent.ResolventDefectOnUnitState Operator Vector Bound

    curvatureCoefficient transportCoefficient chartCoefficient : Bound
    gaugeCoefficient constraintCoefficient : Bound

    curvatureToSU2 : ∀ vector → UnitState vector →
      Family.LessEqual algebra
        (Family.curvatureForm forms vector)
        (Family.multiply algebra curvatureCoefficient (su2Defect vector))

    transportToSU2 : ∀ vector → UnitState vector →
      Family.LessEqual algebra
        (Family.transportForm forms vector)
        (Family.multiply algebra transportCoefficient (su2Defect vector))

    chartToSU2 : ∀ vector → UnitState vector →
      Family.LessEqual algebra
        (Family.chartForm forms vector)
        (Family.multiply algebra chartCoefficient (su2Defect vector))

    gaugeToResolvent : ∀ vector → UnitState vector →
      Family.LessEqual algebra
        (Family.gaugeForm forms vector)
        (Family.multiply algebra gaugeCoefficient
          (UnitResolvent.resolventVectorDefect resolventData vector))

    constraintToResolvent : ∀ vector → UnitState vector →
      Family.LessEqual algebra
        (Family.constraintForm forms vector)
        (Family.multiply algebra constraintCoefficient
          (UnitResolvent.resolventVectorDefect resolventData vector))

    su2DefectUniform : ∀ vector → UnitState vector →
      Family.LessEqual algebra (su2Defect vector) su2DefectBudget

    unitStateMeaning : ∀ vector →
      UnitResolvent.UnitState resolventData vector ≡ UnitState vector

    orderMeaning :
      Resolvent.LessEqual
        (Resolvent.algebra (UnitResolvent.resolvent resolventData))
      ≡ Family.LessEqual algebra

open TwoFamilyResolvedResolventInputs public

resolventDefectUniformInFamilyOrder :
  ∀ {Operator Vector Bound}
    (inputs : TwoFamilyResolvedResolventInputs Operator Vector Bound)
    vector → UnitState inputs vector →
  Family.LessEqual (algebra inputs)
    (UnitResolvent.resolventVectorDefect
      (resolventData inputs) vector)
    (Resolvent.differenceBudget
      (UnitResolvent.resolvent (resolventData inputs)))
resolventDefectUniformInFamilyOrder inputs vector unit =
  subst
    (λ relation → relation
      (UnitResolvent.resolventVectorDefect
        (resolventData inputs) vector)
      (Resolvent.differenceBudget
        (UnitResolvent.resolvent (resolventData inputs))))
    (orderMeaning inputs)
    (UnitResolvent.resolventVectorDefectUniform
      (resolventData inputs) vector
      (subst
        (λ proposition → proposition)
        (sym (unitStateMeaning inputs vector))
        unit))

asTwoFamilyChannelMajorant :
  ∀ {Operator Vector Bound} →
  TwoFamilyResolvedResolventInputs Operator Vector Bound →
  Family.TwoFamilyChannelMajorant Vector Bound
asTwoFamilyChannelMajorant inputs = record
  { algebra = algebra inputs
  ; forms = forms inputs
  ; UnitState = UnitState inputs
  ; su2Defect = su2Defect inputs
  ; resolventDefect =
      UnitResolvent.resolventVectorDefect (resolventData inputs)
  ; su2DefectBudget = su2DefectBudget inputs
  ; resolventDefectBudget =
      Resolvent.differenceBudget
        (UnitResolvent.resolvent (resolventData inputs))
  ; curvatureCoefficient =
      curvatureCoefficient inputs
  ; transportCoefficient =
      transportCoefficient inputs
  ; chartCoefficient = chartCoefficient inputs
  ; gaugeCoefficient = gaugeCoefficient inputs
  ; constraintCoefficient =
      constraintCoefficient inputs
  ; curvatureToSU2 = curvatureToSU2 inputs
  ; transportToSU2 = transportToSU2 inputs
  ; chartToSU2 = chartToSU2 inputs
  ; gaugeToResolvent =
      gaugeToResolvent inputs
  ; constraintToResolvent =
      constraintToResolvent inputs
  ; su2DefectUniform =
      su2DefectUniform inputs
  ; resolventDefectUniform =
      resolventDefectUniformInFamilyOrder inputs
  }

twoFamilyResolvedResolventUniformityLevel : ProofLevel
twoFamilyResolvedResolventUniformityLevel = machineChecked

twoFamilyResolvedResolventAdapterLevel : ProofLevel
twoFamilyResolvedResolventAdapterLevel = machineChecked

physicalGaugeConstraintToResolventFormInputsLevel : ProofLevel
physicalGaugeConstraintToResolventFormInputsLevel = conditional

physicalResolventUnitStateOrderMeaningInputsLevel : ProofLevel
physicalResolventUnitStateOrderMeaningInputsLevel = conditional
