module DASHI.Governance.InterventionFeasibilityCutsetExact where

------------------------------------------------------------------------
-- CROSS-POLLINATION CALIBRATION
--
-- Internal producer pollen:
--   * PR #559 distinguishes a cheap necessary-condition falsifier, a
--     constructive resource allocation, and the final physical theorem;
--   * PR #556 / InterventionBundleExact distinguishes outcomes of different
--     policy/support bundles and keeps omitted supports explicit.
--
-- This file transports only the proof architecture.  It does not identify
-- social-policy resources with Navier--Stokes correction budgets and it does
-- not assign invented numerical capacities to housing, treatment, safety or
-- other policy supports.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Governance.InterventionBundleExact as Intervention

------------------------------------------------------------------------
-- Required-support feasibility over an arbitrary existing BundleSystem.
------------------------------------------------------------------------

record RequiredSupportSystem
  (S : Intervention.BundleSystem) : Set₁ where
  constructor requiredSupportSystem
  field
    Required : Intervention.BundleSystem.Feature S → Set

open RequiredSupportSystem public

record SupportComplete
  {S : Intervention.BundleSystem}
  (R : RequiredSupportSystem S)
  (bundle : Intervention.BundleSystem.Bundle S) : Set₁ where
  constructor supportComplete
  field
    everyRequiredSupportPresent :
      (feature : Intervention.BundleSystem.Feature S) →
      Required R feature →
      Intervention.BundleSystem.enabledIn S bundle feature

open SupportComplete public

record MissingRequiredSupport
  {S : Intervention.BundleSystem}
  (R : RequiredSupportSystem S)
  (bundle : Intervention.BundleSystem.Bundle S) : Set₁ where
  constructor missingRequiredSupport
  field
    missingFeature : Intervention.BundleSystem.Feature S
    featureRequired : Required R missingFeature
    featureAbsent :
      Intervention.BundleSystem.enabledIn S bundle missingFeature → ⊥

open MissingRequiredSupport public

missingRequiredSupportFalsifiesCompleteness :
  ∀ {S : Intervention.BundleSystem}
    {R : RequiredSupportSystem S}
    {bundle : Intervention.BundleSystem.Bundle S} →
  MissingRequiredSupport R bundle →
  SupportComplete R bundle →
  ⊥
missingRequiredSupportFalsifiesCompleteness missing complete =
  featureAbsent missing
    (everyRequiredSupportPresent complete
      (missingFeature missing)
      (featureRequired missing))

------------------------------------------------------------------------
-- Allocation and outcome remain later stages.  A missing-support falsifier can
-- stop a proposed completeness proof cheaply; passing the necessary gate does
-- not itself construct an allocation or establish an outcome.
------------------------------------------------------------------------

record AllocationSystem
  {S : Intervention.BundleSystem}
  (R : RequiredSupportSystem S) : Set₁ where
  constructor allocationSystem
  field
    Allocation : Set
    allocatedTo : Allocation → Intervention.BundleSystem.Feature S → Set
    allocationCoversRequired :
      (allocation : Allocation) →
      (feature : Intervention.BundleSystem.Feature S) →
      Required R feature →
      allocatedTo allocation feature

open AllocationSystem public

record BundleAllocation
  {S : Intervention.BundleSystem}
  {R : RequiredSupportSystem S}
  (A : AllocationSystem R)
  (bundle : Intervention.BundleSystem.Bundle S) : Set₁ where
  constructor bundleAllocation
  field
    allocation : Allocation A
    allocationRealized :
      (feature : Intervention.BundleSystem.Feature S) →
      allocatedTo A allocation feature →
      Intervention.BundleSystem.enabledIn S bundle feature

open BundleAllocation public

allocationConstructsSupportCompleteness :
  ∀ {S : Intervention.BundleSystem}
    {R : RequiredSupportSystem S}
    {A : AllocationSystem R}
    {bundle : Intervention.BundleSystem.Bundle S} →
  BundleAllocation A bundle →
  SupportComplete R bundle
allocationConstructsSupportCompleteness allocated =
  supportComplete λ feature required →
    allocationRealized allocated feature
      (allocationCoversRequired _ (allocation allocated) feature required)

------------------------------------------------------------------------
-- Outcome theorem is an explicit extra law, never smuggled into feasibility.
------------------------------------------------------------------------

record FeasibilityOutcomeLaw
  {S : Intervention.BundleSystem}
  (R : RequiredSupportSystem S) : Set₁ where
  constructor feasibilityOutcomeLaw
  field
    DesiredOutcome : Intervention.BundleSystem.OutcomeValue S → Set
    completeBundleHasDesiredOutcome :
      (bundle : Intervention.BundleSystem.Bundle S) →
      SupportComplete R bundle →
      DesiredOutcome (Intervention.BundleSystem.outcomeOf S bundle)

open FeasibilityOutcomeLaw public

allocatedBundleReachesDesiredOutcome :
  ∀ {S : Intervention.BundleSystem}
    {R : RequiredSupportSystem S}
    {A : AllocationSystem R}
    {L : FeasibilityOutcomeLaw R}
    {bundle : Intervention.BundleSystem.Bundle S} →
  BundleAllocation A bundle →
  DesiredOutcome L (Intervention.BundleSystem.outcomeOf S bundle)
allocatedBundleReachesDesiredOutcome {L = L} allocated =
  completeBundleHasDesiredOutcome L _
    (allocationConstructsSupportCompleteness allocated)

------------------------------------------------------------------------
-- Boundary: necessary condition -> constructive allocation -> outcome theorem
-- are three distinct proof stages.
------------------------------------------------------------------------

record InterventionFeasibilityCutsetBoundary : Set where
  constructor interventionFeasibilityCutsetBoundary
  field
    passingNecessaryGateConstructsAllocation : Bool
    passingNecessaryGateEstablishesOutcome : Bool
    missingRequiredSupportCanFalsifyCompleteness : Bool
    allocationCanConstructCompleteness : Bool
    desiredOutcomeNeedsSeparateLaw : Bool
    physicalResourceBudgetIdentifiedWithPolicyCapacity : Bool

canonicalInterventionFeasibilityCutsetBoundary :
  InterventionFeasibilityCutsetBoundary
canonicalInterventionFeasibilityCutsetBoundary =
  interventionFeasibilityCutsetBoundary
    false
    false
    true
    true
    true
    false
