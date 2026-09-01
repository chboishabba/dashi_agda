module DASHI.Governance.DrugGovernanceFiveProbeOptionConeExact where

open import DASHI.Core.Prelude

import DASHI.Governance.OptionConeCoercionExact as Cone
import DASHI.Governance.DrugGovernanceFiveProbeWorldExact as Five
import DASHI.Governance.ObserverValuationAuthoritySeparationExact as Authority
import DASHI.Governance.HistoryObserverAuthorityOptionConeCapstoneExact as HistoryCapstone

------------------------------------------------------------------------
-- FIVE-PROBE OPTION CONE
--
-- Fine classification coordinates are operational only when they affect a
-- declared reachable option.  Equal positive therapeutic legibility therefore
-- does not imply equal capability/choice geometry.
------------------------------------------------------------------------

data GovernanceOption : Set where
  clinicalAccess
  marketPurchase
  selfDefinitionContest
  historicalRepairClaim
  categoryAuthorityContest
  benefitSharingClaim
  sovereignCeremonialGovernance
  : GovernanceOption

data Available : Five.ProbeWorld → GovernanceOption → Set where
  baseClinical : Available Five.baseExternalWorld clinicalAccess
  baseMarket : Available Five.baseExternalWorld marketPurchase

  subjectClinical : Available Five.subjectAuthoredWorld clinicalAccess
  subjectMarket : Available Five.subjectAuthoredWorld marketPurchase
  subjectContest : Available Five.subjectAuthoredWorld selfDefinitionContest

  historyClinical : Available Five.historyRetainedWorld clinicalAccess
  historyMarket : Available Five.historyRetainedWorld marketPurchase
  historyRepair : Available Five.historyRetainedWorld historicalRepairClaim

  authorityClinical : Available Five.authorityRechartedWorld clinicalAccess
  authorityMarket : Available Five.authorityRechartedWorld marketPurchase
  authorityContest : Available Five.authorityRechartedWorld categoryAuthorityContest

  sharedClinical : Available Five.sharedBenefitWorld clinicalAccess
  sharedMarket : Available Five.sharedBenefitWorld marketPurchase
  sharedBenefit : Available Five.sharedBenefitWorld benefitSharingClaim

  sovereignClinical : Available Five.sovereignWorld clinicalAccess
  sovereignMarket : Available Five.sovereignWorld marketPurchase
  sovereignContest : Available Five.sovereignWorld categoryAuthorityContest
  sovereignBenefit : Available Five.sovereignWorld benefitSharingClaim
  sovereignGovernance : Available Five.sovereignWorld sovereignCeremonialGovernance

reachability : Cone.SafeReachabilitySystem Five.ProbeWorld GovernanceOption
reachability = Cone.safeReachabilitySystem Available

------------------------------------------------------------------------
-- Same coarse surface, different option cones.
------------------------------------------------------------------------

baseLacksSubjectContest : Available Five.baseExternalWorld selfDefinitionContest → ⊥
baseLacksSubjectContest ()

baseLacksHistoryRepair : Available Five.baseExternalWorld historicalRepairClaim → ⊥
baseLacksHistoryRepair ()

baseLacksAuthorityContest : Available Five.baseExternalWorld categoryAuthorityContest → ⊥
baseLacksAuthorityContest ()

baseLacksBenefitSharing : Available Five.baseExternalWorld benefitSharingClaim → ⊥
baseLacksBenefitSharing ()

baseLacksSovereignGovernance : Available Five.baseExternalWorld sovereignCeremonialGovernance → ⊥
baseLacksSovereignGovernance ()

------------------------------------------------------------------------
-- Explicit contraction from the sovereign/community-rich cone to the coarse
-- externally governed positive-therapeutic cone.
------------------------------------------------------------------------

baseIncludedInSovereign :
  (option : GovernanceOption) →
  Available Five.baseExternalWorld option →
  Available Five.sovereignWorld option
baseIncludedInSovereign clinicalAccess baseClinical = sovereignClinical
baseIncludedInSovereign marketPurchase baseMarket = sovereignMarket

sovereignToExternalContracts :
  Cone.StrictSafeReachabilityContraction
    reachability
    Five.sovereignWorld
    Five.baseExternalWorld
sovereignToExternalContracts = Cone.strictSafeReachabilityContraction
  (λ option available → baseIncludedInSovereign option available)
  sovereignCeremonialGovernance
  sovereignGovernance
  baseLacksSovereignGovernance

------------------------------------------------------------------------
-- Material-routing difference also carries an actual extra reachable claim.
------------------------------------------------------------------------

sharedBenefitCarriesExtraOption : Available Five.sharedBenefitWorld benefitSharingClaim
sharedBenefitCarriesExtraOption = sharedBenefit

externalCommercialSurfaceDoesNotCarryBenefitSharing :
  Available Five.baseExternalWorld benefitSharingClaim → ⊥
externalCommercialSurfaceDoesNotCarryBenefitSharing = baseLacksBenefitSharing

------------------------------------------------------------------------
-- Observation/evaluation/authority separation retained: seeing a contraction or
-- valuing an option does not itself issue modification authority.
------------------------------------------------------------------------

authoritySeparationBoundary : Authority.ObserverValuationAuthorityBoundary
authoritySeparationBoundary = Authority.canonicalObserverValuationAuthorityBoundary

historyAuthorityConeBoundary : HistoryCapstone.HistoryObserverAuthorityCapstoneBoundary
historyAuthorityConeBoundary = HistoryCapstone.canonicalHistoryObserverAuthorityCapstoneBoundary

record FiveProbeOptionConeBoundary : Set where
  constructor fiveProbeOptionConeBoundary
  field
    samePositiveLegibilityMeansSameOptionCone : Bool
    samePositiveLegibilityMeansSameOptionConeIsFalse :
      samePositiveLegibilityMeansSameOptionCone ≡ false
    materialProbeCanExposeReachableBenefitSharingDifference : Bool
    materialProbeCanExposeReachableBenefitSharingDifferenceIsTrue :
      materialProbeCanExposeReachableBenefitSharingDifference ≡ true
    sovereigntyProbeCanExposeReachableGovernanceDifference : Bool
    sovereigntyProbeCanExposeReachableGovernanceDifferenceIsTrue :
      sovereigntyProbeCanExposeReachableGovernanceDifference ≡ true
    coneDifferenceSelfIssuesAuthorityToModify : Bool
    coneDifferenceSelfIssuesAuthorityToModifyIsFalse :
      coneDifferenceSelfIssuesAuthorityToModify ≡ false
    optionConeDifferenceAloneProvesHistoricalCause : Bool
    optionConeDifferenceAloneProvesHistoricalCauseIsFalse :
      optionConeDifferenceAloneProvesHistoricalCause ≡ false

canonicalFiveProbeOptionConeBoundary : FiveProbeOptionConeBoundary
canonicalFiveProbeOptionConeBoundary =
  fiveProbeOptionConeBoundary false refl true refl true refl false refl false refl
