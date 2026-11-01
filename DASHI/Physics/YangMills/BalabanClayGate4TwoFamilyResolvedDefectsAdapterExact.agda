module DASHI.Physics.YangMills.BalabanClayGate4TwoFamilyResolvedDefectsAdapterExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4TwoFamilyChannelMajorantExact as Family
import DASHI.Physics.YangMills.BalabanClayGate4SU2NonlinearityDefectPipelineExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4ResolventDefectPipelineExact as Resolvent
import DASHI.Physics.YangMills.BalabanClayGate4ResolventDefectOnUnitStateExact as UnitResolvent

------------------------------------------------------------------------
-- Fully resolved two-family uniformity adapter.
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
-- The original five-channel reduction required two uniform defect estimates.
-- This adapter derives both:
--
-- * the SU(2) defect from the three operator estimates for Ad-I, dexp-I and
--   dexp^-1-I;
-- * the resolvent defect from the second resolvent identity and unit-state
--   action bound.
--
-- The remaining physical inputs are now only the five form-to-defect
-- identifications and the underlying component norm constants.
------------------------------------------------------------------------

record TwoFamilyResolvedDefectsInputs
    (SU2Operator ResolventOperator Vector Bound : Set) : Set₁ where
  field
    algebra : Family.OrderedScaleAlgebra Bound
    forms : Family.FiveChannelForms Vector Bound
    UnitState : Vector → Set

    su2Data : SU2.SU2NonlinearityDefectData SU2Operator Vector Bound
    resolventData :
      UnitResolvent.ResolventDefectOnUnitState
        ResolventOperator Vector Bound

    curvatureCoefficient transportCoefficient chartCoefficient : Bound
    gaugeCoefficient constraintCoefficient : Bound

    curvatureToSU2 : ∀ vector → UnitState vector →
      Family.LessEqual algebra
        (Family.curvatureForm forms vector)
        (Family.multiply algebra curvatureCoefficient
          (SU2.su2NonlinearityDefect su2Data vector))

    transportToSU2 : ∀ vector → UnitState vector →
      Family.LessEqual algebra
        (Family.transportForm forms vector)
        (Family.multiply algebra transportCoefficient
          (SU2.su2NonlinearityDefect su2Data vector))

    chartToSU2 : ∀ vector → UnitState vector →
      Family.LessEqual algebra
        (Family.chartForm forms vector)
        (Family.multiply algebra chartCoefficient
          (SU2.su2NonlinearityDefect su2Data vector))

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

    su2UnitStateMeaning : ∀ vector →
      SU2.UnitState su2Data vector ≡ UnitState vector

    resolventUnitStateMeaning : ∀ vector →
      UnitResolvent.UnitState resolventData vector ≡ UnitState vector

    su2OrderMeaning :
      SU2.LessEqual (SU2.algebra su2Data)
      ≡ Family.LessEqual algebra

    resolventOrderMeaning :
      Resolvent.LessEqual
        (Resolvent.algebra (UnitResolvent.resolvent resolventData))
      ≡ Family.LessEqual algebra

open TwoFamilyResolvedDefectsInputs public

su2DefectUniformInFamilyOrder :
  ∀ {SU2Operator ResolventOperator Vector Bound}
    (inputs : TwoFamilyResolvedDefectsInputs
      SU2Operator ResolventOperator Vector Bound)
    vector → UnitState inputs vector →
  Family.LessEqual (algebra inputs)
    (SU2.su2NonlinearityDefect (su2Data inputs) vector)
    (SU2.su2NonlinearityBudget (su2Data inputs))
su2DefectUniformInFamilyOrder inputs vector unit =
  subst
    (λ relation → relation
      (SU2.su2NonlinearityDefect (su2Data inputs) vector)
      (SU2.su2NonlinearityBudget (su2Data inputs)))
    (su2OrderMeaning inputs)
    (SU2.su2NonlinearityDefectUniform
      (su2Data inputs) vector
      (subst
        (λ proposition → proposition)
        (sym (su2UnitStateMeaning inputs vector))
        unit))

resolventDefectUniformInFamilyOrder :
  ∀ {SU2Operator ResolventOperator Vector Bound}
    (inputs : TwoFamilyResolvedDefectsInputs
      SU2Operator ResolventOperator Vector Bound)
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
    (resolventOrderMeaning inputs)
    (UnitResolvent.resolventVectorDefectUniform
      (resolventData inputs) vector
      (subst
        (λ proposition → proposition)
        (sym (resolventUnitStateMeaning inputs vector))
        unit))

asTwoFamilyChannelMajorant :
  ∀ {SU2Operator ResolventOperator Vector Bound} →
  TwoFamilyResolvedDefectsInputs
    SU2Operator ResolventOperator Vector Bound →
  Family.TwoFamilyChannelMajorant Vector Bound
asTwoFamilyChannelMajorant inputs = record
  { algebra = algebra inputs
  ; forms = forms inputs
  ; UnitState = UnitState inputs
  ; su2Defect =
      SU2.su2NonlinearityDefect (su2Data inputs)
  ; resolventDefect =
      UnitResolvent.resolventVectorDefect (resolventData inputs)
  ; su2DefectBudget =
      SU2.su2NonlinearityBudget (su2Data inputs)
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
      su2DefectUniformInFamilyOrder inputs
  ; resolventDefectUniform =
      resolventDefectUniformInFamilyOrder inputs
  }

twoFamilySU2UniformityDerivedLevel : ProofLevel
twoFamilySU2UniformityDerivedLevel = machineChecked

twoFamilyResolventUniformityDerivedLevel : ProofLevel
twoFamilyResolventUniformityDerivedLevel = machineChecked

twoFamilyResolvedDefectsAdapterLevel : ProofLevel
twoFamilyResolvedDefectsAdapterLevel = machineChecked

physicalFiveFormsToResolvedDefectsInputsLevel : ProofLevel
physicalFiveFormsToResolvedDefectsInputsLevel = conditional

physicalResolvedDefectOrderConventionInputsLevel : ProofLevel
physicalResolvedDefectOrderConventionInputsLevel = conditional
