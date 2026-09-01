module DASHI.Governance.DrugGovernanceCapabilityFunctioningExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.CapabilityFunctioningNonDescentExact as Capability
import DASHI.Governance.DrugGovernanceFiveProbeOptionConeExact as FiveCone
import DASHI.Governance.DrugGovernanceFiveProbeWorldExact as Five

------------------------------------------------------------------------
-- DRUG GOVERNANCE CAPABILITY / FUNCTIONING NON-DESCENT
--
-- Realized treatment/access behavior and the set of reachable institutional
-- alternatives are separate objects.  A person can display the same realized
-- functioning under a broad or narrow option cone; conversely two people with
-- comparable option availability can realize different choices.
------------------------------------------------------------------------

data GovernanceState : Set where
  broadConeSameTreatment
  narrowConeSameTreatment
  broadConeContestChosen
  : GovernanceState

data RealizedFunctioning : Set where
  receivesTreatment
  contestsCategory
  : RealizedFunctioning

data CapabilityCode : Set where
  broadCapabilityCone
  narrowCapabilityCone
  : CapabilityCode

functioning : GovernanceState → RealizedFunctioning
functioning broadConeSameTreatment = receivesTreatment
functioning narrowConeSameTreatment = receivesTreatment
functioning broadConeContestChosen = contestsCategory

capability : GovernanceState → CapabilityCode
capability broadConeSameTreatment = broadCapabilityCone
capability narrowConeSameTreatment = narrowCapabilityCone
capability broadConeContestChosen = broadCapabilityCone

sameFunctioningDifferentCapability :
  INF.NonFactorabilityWitness functioning capability
sameFunctioningDifferentCapability =
  INF.nonFactorabilityWitness
    broadConeSameTreatment narrowConeSameTreatment refl (λ ())

sameCapabilityDifferentFunctioning :
  INF.NonFactorabilityWitness capability functioning
sameCapabilityDifferentFunctioning =
  INF.nonFactorabilityWitness
    broadConeSameTreatment broadConeContestChosen refl (λ ())

functioningCannotRecoverCapability :
  INF.FactorsThrough functioning capability → ⊥
functioningCannotRecoverCapability =
  INF.witnessRulesOutEveryFlatFactorisation sameFunctioningDifferentCapability

capabilityCannotRecoverFunctioning :
  INF.FactorsThrough capability functioning → ⊥
capabilityCannotRecoverFunctioning =
  INF.witnessRulesOutEveryFlatFactorisation sameCapabilityDifferentFunctioning

------------------------------------------------------------------------
-- Concrete five-probe option-cone consequences.
------------------------------------------------------------------------

sharedBenefitWorldCanReachBenefitSharing :
  FiveCone.Available Five.sharedBenefitWorld FiveCone.benefitSharingClaim
sharedBenefitWorldCanReachBenefitSharing = FiveCone.sharedBenefitCarriesExtraOption

externalWorldCannotReachSovereignGovernance :
  FiveCone.Available Five.baseExternalWorld FiveCone.sovereignCeremonialGovernance → ⊥
externalWorldCannotReachSovereignGovernance = FiveCone.baseLacksSovereignGovernance

sovereignWorldCarriesSovereignGovernance :
  FiveCone.Available Five.sovereignWorld FiveCone.sovereignCeremonialGovernance
sovereignWorldCarriesSovereignGovernance = FiveCone.sovereignGovernance

------------------------------------------------------------------------
-- Cross-pollinated Sen boundary.
------------------------------------------------------------------------

canonicalCapabilityBoundary : Capability.RepairStageBoundary
canonicalCapabilityBoundary = Capability.canonicalRepairStageBoundary

------------------------------------------------------------------------
-- Repair stages remain distinct.
------------------------------------------------------------------------

data IdentifiedDefectPromotesExpandedCapability : Set where

data ExpandedCapabilityPromotesChosenFunctioning : Set where

data SameFunctioningPromotesEqualFreedom : Set where

data SamePositiveTherapeuticSurfacePromotesSameCapabilityCone : Set where

identifiedDefectDoesNotPromoteCapability :
  IdentifiedDefectPromotesExpandedCapability → ⊥
identifiedDefectDoesNotPromoteCapability ()

expandedCapabilityDoesNotPromoteChosenFunctioning :
  ExpandedCapabilityPromotesChosenFunctioning → ⊥
expandedCapabilityDoesNotPromoteChosenFunctioning ()

sameFunctioningDoesNotPromoteEqualFreedom :
  SameFunctioningPromotesEqualFreedom → ⊥
sameFunctioningDoesNotPromoteEqualFreedom ()

sameTherapeuticSurfaceDoesNotPromoteSameCapability :
  SamePositiveTherapeuticSurfacePromotesSameCapabilityCone → ⊥
sameTherapeuticSurfaceDoesNotPromoteSameCapability ()

record DrugGovernanceCapabilityFunctioningBoundary : Set where
  constructor drugGovernanceCapabilityFunctioningBoundary
  field
    sameRealizedTreatmentCanHideDifferentCapabilities : Bool
    sameRealizedTreatmentCanHideDifferentCapabilitiesIsTrue :
      sameRealizedTreatmentCanHideDifferentCapabilities ≡ true
    sameCapabilityCanSupportDifferentFunctionings : Bool
    sameCapabilityCanSupportDifferentFunctioningsIsTrue :
      sameCapabilityCanSupportDifferentFunctionings ≡ true
    capabilityExpansionDeterminesChosenFunctioning : Bool
    capabilityExpansionDeterminesChosenFunctioningIsFalse :
      capabilityExpansionDeterminesChosenFunctioning ≡ false
    positiveLegibilityDeterminesReachableFreedom : Bool
    positiveLegibilityDeterminesReachableFreedomIsFalse :
      positiveLegibilityDeterminesReachableFreedom ≡ false

canonicalDrugGovernanceCapabilityFunctioningBoundary :
  DrugGovernanceCapabilityFunctioningBoundary
canonicalDrugGovernanceCapabilityFunctioningBoundary =
  drugGovernanceCapabilityFunctioningBoundary
    true refl true refl false refl false refl
