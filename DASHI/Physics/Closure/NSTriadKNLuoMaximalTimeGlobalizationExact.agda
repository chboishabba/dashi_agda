module DASHI.Physics.Closure.NSTriadKNLuoMaximalTimeGlobalizationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- PURPOSE
-- Close the purely logical maximal-time step. Once canonical analytic inputs
-- give continuation beyond the selected terminal, finite maximality at that
-- same terminal is contradictory. The physical identification of a candidate
-- breakdown time with the selected terminal remains explicit.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalAnalyticInputsExact as Inputs
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalContinuationFromAnalyticInputsExact as Continuation
import DASHI.Physics.Closure.NSTriadKNLuoOfficialLerayHopfAuthorityExact as Authority

record SelectedTerminalMaximality
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (data : PreBudget.OfficialLuoPreBudgetData InitialDatum Solution Time)
    : Set (lsuc (d ⊔ s ⊔ t)) where
  field
    IsFiniteMaximalTime : Set (d ⊔ t)
    selectedTerminalIsFiniteMaximal : IsFiniteMaximalTime
    maximalTimeForbidsContinuation :
      IsFiniteMaximalTime →
      Authority.ContinuesBeyond
        (PreBudget.sourceCarrier data)
        (PreBudget.initial data)
        (PreBudget.terminal data) →
      ⊥

open SelectedTerminalMaximality public

canonicalInputsContradictSelectedMaximalTime :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData InitialDatum Solution Time} →
  Inputs.CanonicalAnalyticInputs data →
  SelectedTerminalMaximality data →
  ⊥
canonicalInputsContradictSelectedMaximalTime inputs maximality =
  maximalTimeForbidsContinuation maximality
    (selectedTerminalIsFiniteMaximal maximality)
    (Continuation.continuation inputs)

record NoSelectedFiniteMaximalBreakdown
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (data : PreBudget.OfficialLuoPreBudgetData InitialDatum Solution Time)
    (inputs : Inputs.CanonicalAnalyticInputs data)
    : Set (lsuc (d ⊔ s ⊔ t)) where
  field
    exclude : SelectedTerminalMaximality data → ⊥

open NoSelectedFiniteMaximalBreakdown public

noSelectedFiniteMaximalBreakdown :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData InitialDatum Solution Time} →
  (inputs : Inputs.CanonicalAnalyticInputs data) →
  NoSelectedFiniteMaximalBreakdown data inputs
noSelectedFiniteMaximalBreakdown inputs = record
  { exclude = canonicalInputsContradictSelectedMaximalTime inputs }

maximalTimeLogicalGlobalizationReducerClosed : Bool
maximalTimeLogicalGlobalizationReducerClosed = true

physicalMaximalTimeIdentificationStillRequired : Bool
physicalMaximalTimeIdentificationStillRequired = true

maximalTimeLogicalGlobalizationReducerClosedIsTrue :
  maximalTimeLogicalGlobalizationReducerClosed ≡ true
maximalTimeLogicalGlobalizationReducerClosedIsTrue = refl

physicalMaximalTimeIdentificationStillRequiredIsTrue :
  physicalMaximalTimeIdentificationStillRequired ≡ true
physicalMaximalTimeIdentificationStillRequiredIsTrue = refl
