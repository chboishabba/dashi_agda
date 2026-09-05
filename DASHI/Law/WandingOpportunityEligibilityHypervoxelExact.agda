module DASHI.Law.WandingOpportunityEligibilityHypervoxelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Exposure opportunity, statutory eligibility, and actual selection are
-- distinct coordinates.  This prevents geographic deployment effects from
-- being silently re-labelled as officer selection effects.
------------------------------------------------------------------------

data OpportunityState : Set where
  opportunityPresent opportunityAbsent opportunityUnresolved : OpportunityState

data EligibilityState : Set where
  eligible ineligible eligibilityUnresolved : EligibilityState

data SelectionState : Set where
  selected notSelected selectionUnresolved : SelectionState

data GroupState : Set where
  targetGroup comparisonGroup groupUnresolved : GroupState

record OpportunityEligibilityHypervoxel : Set where
  constructor opportunityEligibilityHypervoxel
  field
    personKey : String
    encounterKey : String
    placeKey : String
    timeWindowKey : String
    operationKey : String
    legalScopeKey : String

    physicallyPresent : Bool
    operationActive : Bool
    placeWithinAuthorisedScope : Bool
    personWithinStatutoryScope : Bool

    opportunity : OpportunityState
    eligibility : EligibilityState
    selection : SelectionState
    group : GroupState

    deploymentReference : String
    eligibilityReference : String
    selectionReference : String

open OpportunityEligibilityHypervoxel public

------------------------------------------------------------------------
-- Proof-relevant opportunity / eligibility closures.
------------------------------------------------------------------------

record OpportunityClosure (h : OpportunityEligibilityHypervoxel) : Set where
  constructor opportunityClosure
  field
    presentReceipt : physicallyPresent h ≡ true
    operationReceipt : operationActive h ≡ true
    opportunityClassification : opportunity h ≡ opportunityPresent
    opportunityReference : String

open OpportunityClosure public

record EligibilityClosure (h : OpportunityEligibilityHypervoxel) : Set where
  constructor eligibilityClosure
  field
    opportunityReceipt : OpportunityClosure h
    placeScopeReceipt : placeWithinAuthorisedScope h ≡ true
    personScopeReceipt : personWithinStatutoryScope h ≡ true
    eligibilityClassification : eligibility h ≡ eligible
    closureReference : String

open EligibilityClosure public

record SelectionClosure (h : OpportunityEligibilityHypervoxel) : Set where
  constructor selectionClosure
  field
    eligibilityReceipt : EligibilityClosure h
    selectionClassification : selection h ≡ selected
    selectionClosureReference : String

open SelectionClosure public

------------------------------------------------------------------------
-- Important non-promotions.
------------------------------------------------------------------------

record OpportunityEligibilityBoundary : Set where
  constructor opportunityEligibilityBoundary
  field
    residenceInAreaImpliesExposureOpportunity : Bool
    residenceInAreaImpliesExposureOpportunityIsFalse :
      residenceInAreaImpliesExposureOpportunity ≡ false

    exposureOpportunityImpliesStatutoryEligibility : Bool
    exposureOpportunityImpliesStatutoryEligibilityIsFalse :
      exposureOpportunityImpliesStatutoryEligibility ≡ false

    statutoryEligibilityImpliesActualSelection : Bool
    statutoryEligibilityImpliesActualSelectionIsFalse :
      statutoryEligibilityImpliesActualSelection ≡ false

    deploymentDisparityImpliesConditionalSelectionDisparity : Bool
    deploymentDisparityImpliesConditionalSelectionDisparityIsFalse :
      deploymentDisparityImpliesConditionalSelectionDisparity ≡ false

canonicalOpportunityEligibilityBoundary : OpportunityEligibilityBoundary
canonicalOpportunityEligibilityBoundary =
  opportunityEligibilityBoundary false refl false refl false refl false refl

------------------------------------------------------------------------
-- BIDI consumers.
------------------------------------------------------------------------

data OpportunityConsumer : Set where
  exposureOpportunityClaim eligibilityClaim conditionalSelectionClaim : OpportunityConsumer

data OpportunityProducer : Set where
  presenceOperationReceipt legalScopeReceipt selectedEligibleCrossTab : OpportunityProducer

reverseOpportunityConsumer : OpportunityConsumer → OpportunityProducer
reverseOpportunityConsumer exposureOpportunityClaim = presenceOperationReceipt
reverseOpportunityConsumer eligibilityClaim = legalScopeReceipt
reverseOpportunityConsumer conditionalSelectionClaim = selectedEligibleCrossTab

------------------------------------------------------------------------
-- Canonical contrast: same group and legal eligibility, different opportunity.
-- This witnesses why whole-population denominators can be wrong.
------------------------------------------------------------------------

exposedEligibleNotSelected : OpportunityEligibilityHypervoxel
exposedEligibleNotSelected = opportunityEligibilityHypervoxel
  "person-A" "enc-A" "place-1" "window-1" "op-1" "scope-1"
  true true true true
  opportunityPresent eligible notSelected targetGroup
  "present during active operation"
  "within legal scope"
  "not selected"

notExposedSameGroup : OpportunityEligibilityHypervoxel
notExposedSameGroup = opportunityEligibilityHypervoxel
  "person-B" "enc-B" "place-2" "window-1" "op-1" "scope-1"
  false true true true
  opportunityAbsent eligibilityUnresolved selectionUnresolved targetGroup
  "not physically present in operational exposure zone"
  "eligibility unresolved because no exposure opportunity"
  "selection not reached"

canonicalExposureClosure : OpportunityClosure exposedEligibleNotSelected
canonicalExposureClosure = opportunityClosure refl refl refl "canonical exposure closure"

canonicalEligibilityClosure : EligibilityClosure exposedEligibleNotSelected
canonicalEligibilityClosure = eligibilityClosure canonicalExposureClosure refl refl refl "canonical eligibility closure"
