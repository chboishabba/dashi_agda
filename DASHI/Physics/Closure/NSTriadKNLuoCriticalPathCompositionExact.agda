module DASHI.Physics.Closure.NSTriadKNLuoCriticalPathCompositionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Compose the exact critical path already present in the repository:
--
--   irreducible physical leaves
--   -> CanonicalAnalyticInputs
--   -> continuation beyond the selected terminal
--   -> contradiction with selected finite maximality.
--
-- Thus no theorem between the physical-leaf package and the maximal-time
-- contradiction remains an independent obligation.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalAnalyticInputsExact as Canonical
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalAnalyticInputsBuilderExact as Builder
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalContinuationFromAnalyticInputsExact as Continuation
import DASHI.Physics.Closure.NSTriadKNLuoMaximalTimeGlobalizationExact as Globalization
import DASHI.Physics.Closure.NSTriadKNLuoOfficialLerayHopfAuthorityExact as Authority

record LuoCriticalPathInputs
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time) : Set (lsuc (d ⊔ s ⊔ t)) where
  field
    physicalLeaves : Builder.CanonicalAnalyticPhysicalLeaves data

open LuoCriticalPathInputs public

criticalPathCanonicalInputs :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  LuoCriticalPathInputs data →
  Canonical.CanonicalAnalyticInputs data
criticalPathCanonicalInputs inputs =
  Builder.canonicalAnalyticInputsFromPhysicalLeaves
    (physicalLeaves inputs)

criticalPathContinuation :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  LuoCriticalPathInputs data →
  Authority.ContinuesBeyond
    (PreBudget.sourceCarrier data)
    (PreBudget.initial data)
    (PreBudget.terminal data)
criticalPathContinuation inputs =
  Continuation.continuation (criticalPathCanonicalInputs inputs)

criticalPathContradictsSelectedFiniteMaximality :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  LuoCriticalPathInputs data →
  Globalization.SelectedTerminalMaximality data →
  ⊥
criticalPathContradictsSelectedFiniteMaximality inputs maximality =
  Globalization.canonicalInputsContradictSelectedMaximalTime
    (criticalPathCanonicalInputs inputs)
    maximality

record CriticalPathReceipt
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time)
    (inputs : LuoCriticalPathInputs data) : Set (lsuc (d ⊔ s ⊔ t)) where
  field
    canonicalInputs : Canonical.CanonicalAnalyticInputs data
    continuation :
      Authority.ContinuesBeyond
        (PreBudget.sourceCarrier data)
        (PreBudget.initial data)
        (PreBudget.terminal data)
    excludeSelectedFiniteMaximality :
      Globalization.SelectedTerminalMaximality data → ⊥

open CriticalPathReceipt public

criticalPathReceipt :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : LuoCriticalPathInputs data) →
  CriticalPathReceipt data inputs
criticalPathReceipt inputs = record
  { canonicalInputs = criticalPathCanonicalInputs inputs
  ; continuation = criticalPathContinuation inputs
  ; excludeSelectedFiniteMaximality =
      criticalPathContradictsSelectedFiniteMaximality inputs
  }

physicalLeavesToContinuationCompositionClosed : Bool
physicalLeavesToContinuationCompositionClosed = true

physicalLeavesToMaximalityContradictionCompositionClosed : Bool
physicalLeavesToMaximalityContradictionCompositionClosed = true

physicalLeavesToContinuationCompositionClosedIsTrue :
  physicalLeavesToContinuationCompositionClosed ≡ true
physicalLeavesToContinuationCompositionClosedIsTrue = refl

physicalLeavesToMaximalityContradictionCompositionClosedIsTrue :
  physicalLeavesToMaximalityContradictionCompositionClosed ≡ true
physicalLeavesToMaximalityContradictionCompositionClosedIsTrue = refl
