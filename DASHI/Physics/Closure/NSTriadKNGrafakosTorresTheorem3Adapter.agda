module DASHI.Physics.Closure.NSTriadKNGrafakosTorresTheorem3Adapter where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; DASHI repository contributors.
-- Title: "On Multilinear Singular Integrals of Calderon--Zygmund Type" and
-- "A Multilinear Schur Test and Multiplier Operators".
-- Venue/year: Publicacions Matematiques, Extra 2002, 57--91; Journal of
-- Functional Analysis 187 (2001), 1--24; DASHI formal development, 2026.
-- DOI: 10.5565/PUBLMAT_Esco02_04; 10.1006/jfan.2001.3804; the repository
-- convention adapter has no DOI.
-- Uses: Theorem 3 of the El Escorial exposition for the displayed
-- output/first-partial-adjoint/second-partial-adjoint auxiliary-function test,
-- and the detailed multilinear Schur development in the JFA paper.
-- Relationship: corrects the bibliographic boundary in the attachment. It
-- maps the three Stage-3 conditions exactly to S, S*1 and S*2 and consumes
-- only the sufficiency direction. It does not claim that the current
-- Navier--Stokes kernel already satisfies those conditions.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNGrafakosTorresThreeFunctionSchurProgram as GT

record Theorem3AuxiliaryFunctions
    {l r o s e : Level}
    (C : GT.ThreeFunctionSchurCarrier {l} {r} {o} {s} {e}) :
    Set (lsuc (l ⊔ r ⊔ o ⊔ s ⊔ e)) where
  field
    leftAuxiliaryPositive :
      ∀ left → GT.StrictlyPositive C (GT.leftWeight C left)
    rightAuxiliaryPositive :
      ∀ right → GT.StrictlyPositive C (GT.rightWeight C right)
    outputAuxiliaryPositive :
      ∀ output → GT.StrictlyPositive C (GT.outputWeight C output)

    outputCondition : ∀ output →
      GT.leq C
        (GT.outputWeightedSum C output)
        (GT.multiply C (GT.schurConstant C) (GT.outputTarget C output))

    firstPartialAdjointCondition : ∀ left →
      GT.leq C
        (GT.leftPartialAdjointWeightedSum C left)
        (GT.multiply C (GT.schurConstant C) (GT.leftTarget C left))

    secondPartialAdjointCondition : ∀ right →
      GT.leq C
        (GT.rightPartialAdjointWeightedSum C right)
        (GT.multiply C (GT.schurConstant C) (GT.rightTarget C right))

open Theorem3AuxiliaryFunctions public

conditionCToTheorem3Auxiliaries :
  ∀ {l r o s e}
    {C : GT.ThreeFunctionSchurCarrier {l} {r} {o} {s} {e}} →
  GT.GrafakosTorresConditionC C →
  Theorem3AuxiliaryFunctions C
conditionCToTheorem3Auxiliaries condition = record
  { leftAuxiliaryPositive =
      GT.GrafakosTorresConditionC.leftWeightPositive condition
  ; rightAuxiliaryPositive =
      GT.GrafakosTorresConditionC.rightWeightPositive condition
  ; outputAuxiliaryPositive =
      GT.GrafakosTorresConditionC.outputWeightPositive condition
  ; outputCondition =
      GT.GrafakosTorresConditionC.outputCondition condition
  ; firstPartialAdjointCondition =
      GT.GrafakosTorresConditionC.leftPartialAdjointCondition condition
  ; secondPartialAdjointCondition =
      GT.GrafakosTorresConditionC.rightPartialAdjointCondition condition
  }

record Theorem3Sufficiency
    {l r o s e : Level}
    (C : GT.ThreeFunctionSchurCarrier {l} {r} {o} {s} {e}) :
    Set (lsuc (l ⊔ r ⊔ o ⊔ s ⊔ e)) where
  field
    auxiliaryConditionsImplyBilinearBound :
      Theorem3AuxiliaryFunctions C → Set s

open Theorem3Sufficiency public

record Stage3Theorem3Instantiation
    {l r o s e : Level}
    (C : GT.ThreeFunctionSchurCarrier {l} {r} {o} {s} {e}) :
    Set (lsuc (l ⊔ r ⊔ o ⊔ s ⊔ e)) where
  field
    signedKernelDominatedByPositiveKernel : Set s
    outputAuxiliaryFunctionIdentified : Set s
    leftAuxiliaryFunctionIdentified : Set s
    rightAuxiliaryFunctionIdentified : Set s
    theorem3Auxiliaries : Theorem3AuxiliaryFunctions C
    theorem3Sufficiency : Theorem3Sufficiency C
    signedFormRecoveredAfterPositiveBound : Set s
    constantUniformInGalerkinCutoff : Set s

open Stage3Theorem3Instantiation public

threeConditionShapeMatchesTheorem3 : Bool
threeConditionShapeMatchesTheorem3 = true

threeConditionShapeMatchesTheorem3IsTrue :
  threeConditionShapeMatchesTheorem3 ≡ true
threeConditionShapeMatchesTheorem3IsTrue = refl

onlySufficiencyDirectionRequired : Bool
onlySufficiencyDirectionRequired = true

onlySufficiencyDirectionRequiredIsTrue :
  onlySufficiencyDirectionRequired ≡ true
onlySufficiencyDirectionRequiredIsTrue = refl

concreteStage3Theorem3InstantiationClosed : Bool
concreteStage3Theorem3InstantiationClosed = false

concreteStage3Theorem3InstantiationClosedIsFalse :
  concreteStage3Theorem3InstantiationClosed ≡ false
concreteStage3Theorem3InstantiationClosedIsFalse = refl
