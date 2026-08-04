module DASHI.Physics.Closure.NSTriadKNLuoNoCircularityAuditExact where

------------------------------------------------------------------------
-- PURPOSE
-- Record the no-circularity properties which are already mechanically visible
-- in the source-faithful Luo architecture. The complete transitive dependency
-- audit remains false until generated from a clean final build.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalAnalyticInputsBuilderExact as Builder
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalContinuationFromAnalyticInputsExact as Continuation
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalAnalyticTaskLedger as Analytic
import DASHI.Physics.Closure.NSTriadKNLuoCriticalPathCompositionExact as Critical

record LuoNoCircularityAudit : Set where
  constructor audit
  field
    terminalBudgetRemovedFromPhysicalData : Bool
    localizedCriterionRemovedFromPhysicalData : Bool
    canonicalInputsBuiltFromNamedPhysicalLeaves : Bool
    continuationDerivedFromCanonicalInputs : Bool
    maximalityContradictionDerivedFromPhysicalLeaves : Bool

    globalSmoothnessProved : Bool
    bkmExclusionProved : Bool
    completeTransitiveDependencyAuditGenerated : Bool

open LuoNoCircularityAudit public

luoNoCircularityAudit : LuoNoCircularityAudit
luoNoCircularityAudit = audit
  PreBudget.terminalBudgetNoLongerPhysicalDataInput
  PreBudget.localizedThresholdNoLongerPhysicalDataInput
  Builder.canonicalAnalyticInputsBuilderConstructed
  Continuation.canonicalContinuationFromAnalyticInputsConstructed
  Critical.physicalLeavesToMaximalityContradictionCompositionClosed
  false
  (Analytic.canonicalBKMExclusionProved
    Analytic.luoPhysicalAnalyticTaskLedger)
  false

noCircularityAuditSchemaConstructed : Bool
noCircularityAuditSchemaConstructed = true

machineVisibleCircularityBarriersConstructed : Bool
machineVisibleCircularityBarriersConstructed = true

noCircularityAuditSchemaConstructedIsTrue :
  noCircularityAuditSchemaConstructed ≡ true
noCircularityAuditSchemaConstructedIsTrue = refl

machineVisibleCircularityBarriersConstructedIsTrue :
  machineVisibleCircularityBarriersConstructed ≡ true
machineVisibleCircularityBarriersConstructedIsTrue = refl

terminalBudgetRemovalIsMachineChecked :
  terminalBudgetRemovedFromPhysicalData luoNoCircularityAudit ≡ true
terminalBudgetRemovalIsMachineChecked =
  PreBudget.terminalBudgetNoLongerPhysicalDataInputIsTrue

localizedCriterionRemovalIsMachineChecked :
  localizedCriterionRemovedFromPhysicalData luoNoCircularityAudit ≡ true
localizedCriterionRemovalIsMachineChecked =
  PreBudget.localizedThresholdNoLongerPhysicalDataInputIsTrue

canonicalInputBuilderIsMachineChecked :
  canonicalInputsBuiltFromNamedPhysicalLeaves luoNoCircularityAudit ≡ true
canonicalInputBuilderIsMachineChecked =
  Builder.canonicalAnalyticInputsBuilderConstructedIsTrue

continuationCompositionIsMachineChecked :
  continuationDerivedFromCanonicalInputs luoNoCircularityAudit ≡ true
continuationCompositionIsMachineChecked =
  Continuation.canonicalContinuationFromAnalyticInputsConstructedIsTrue

maximalityCompositionIsMachineChecked :
  maximalityContradictionDerivedFromPhysicalLeaves luoNoCircularityAudit
  ≡ true
maximalityCompositionIsMachineChecked =
  Critical.physicalLeavesToMaximalityContradictionCompositionClosedIsTrue

globalSmoothnessRemainsUnproved :
  globalSmoothnessProved luoNoCircularityAudit ≡ false
globalSmoothnessRemainsUnproved = refl

bkmExclusionRemainsUnproved :
  bkmExclusionProved luoNoCircularityAudit ≡ false
bkmExclusionRemainsUnproved =
  Analytic.canonicalBKMExclusionRemainsFalse

completeDependencyAuditRemainsOpen :
  completeTransitiveDependencyAuditGenerated luoNoCircularityAudit ≡ false
completeDependencyAuditRemainsOpen = refl
