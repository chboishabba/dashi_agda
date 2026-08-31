module DASHI.Governance.DrugGovernanceErrorAllocationChillingExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.EpistemicErrorAllocationChillingBridgeExact as Error
import DASHI.Governance.OptionConeCoercionExact as Cone

------------------------------------------------------------------------
-- DRUG CLASSIFICATION ERROR ALLOCATION / CHILLING
--
-- A classification uncertainty/error can be routed toward repair/refinement or
-- toward fault/sanction.  The allocation is an institutional choice, not a
-- theorem extracted from the mere existence of uncertainty.  The finite world
-- below makes the downstream option-cone consequence explicit.
------------------------------------------------------------------------

data ClassificationErrorSurface : Set where
  sameUnresolvedClassification : ClassificationErrorSurface

data DrugErrorAllocation : Set where
  refineClassification
  attributeFaultAndSanction
  : DrugErrorAllocation

data DrugResponseState : Set where
  beforeAllocation
  repairResponse
  faultResponse
  : DrugResponseState

data DrugOption : Set where
  immediateSafetyAccess
  futureHelpSeeking
  categoryContest
  clinicalReassessment
  communitySupport
  : DrugOption

errorSurface : DrugErrorAllocation → ClassificationErrorSurface
errorSurface _ = sameUnresolvedClassification

allocationCode : DrugErrorAllocation → Error.ErrorAllocation
allocationCode refineClassification = Error.repairAsSafetyInformation
allocationCode attributeFaultAndSanction = Error.attributeFaultToSubject

sameErrorSurfaceDifferentAllocation :
  errorSurface refineClassification ≡ errorSurface attributeFaultAndSanction
sameErrorSurfaceDifferentAllocation = refl

allocationDiffers :
  allocationCode refineClassification ≡
  allocationCode attributeFaultAndSanction → ⊥
allocationDiffers ()

errorSurfaceCannotRecoverAllocation :
  INF.FactorsThrough errorSurface allocationCode → ⊥
errorSurfaceCannotRecoverAllocation =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      refineClassification attributeFaultAndSanction refl (λ ()))

------------------------------------------------------------------------
-- Reachable options under repair versus fault allocation.
------------------------------------------------------------------------

data Available : DrugResponseState → DrugOption → Set where
  beforeSafety : Available beforeAllocation immediateSafetyAccess
  beforeHelp : Available beforeAllocation futureHelpSeeking
  beforeContest : Available beforeAllocation categoryContest
  beforeReassess : Available beforeAllocation clinicalReassessment
  beforeCommunity : Available beforeAllocation communitySupport

  repairSafety : Available repairResponse immediateSafetyAccess
  repairHelp : Available repairResponse futureHelpSeeking
  repairContest : Available repairResponse categoryContest
  repairReassess : Available repairResponse clinicalReassessment
  repairCommunity : Available repairResponse communitySupport

  faultSafety : Available faultResponse immediateSafetyAccess
  faultCommunity : Available faultResponse communitySupport

drugReachability : Cone.SafeReachabilitySystem DrugResponseState DrugOption
drugReachability = Cone.safeReachabilitySystem Available

faultIncludedInBefore :
  (option : DrugOption) →
  Available faultResponse option →
  Available beforeAllocation option
faultIncludedInBefore immediateSafetyAccess faultSafety = beforeSafety
faultIncludedInBefore communitySupport faultCommunity = beforeCommunity

faultAllocationContractsHelpSeeking :
  Cone.StrictSafeReachabilityContraction
    drugReachability beforeAllocation faultResponse
faultAllocationContractsHelpSeeking =
  Cone.strictSafeReachabilityContraction
    faultIncludedInBefore
    futureHelpSeeking
    beforeHelp
    (λ ())

repairRetainsFutureHelpSeeking : Available repairResponse futureHelpSeeking
repairRetainsFutureHelpSeeking = repairHelp

repairRetainsCategoryContest : Available repairResponse categoryContest
repairRetainsCategoryContest = repairContest

faultLacksFutureHelpSeeking : Available faultResponse futureHelpSeeking → ⊥
faultLacksFutureHelpSeeking ()

faultLacksCategoryContest : Available faultResponse categoryContest → ⊥
faultLacksCategoryContest ()

------------------------------------------------------------------------
-- Canonical cross-pollination receipts.
------------------------------------------------------------------------

canonicalErrorAllocationBoundary : Error.EpistemicErrorAllocationChillingBoundary
canonicalErrorAllocationBoundary = Error.canonicalEpistemicErrorAllocationChillingBoundary

canonicalGenericChillingWitness :
  Cone.StrictSafeReachabilityContraction
    Cone.demoReachability Cone.beforeResponse Cone.coerciveOutcome
canonicalGenericChillingWitness = Error.chillingContractsFutureHelpSeeking

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data ClassificationErrorPromotesFault : Set where

data SanctionPromotesUnderstanding : Set where

data QuietCompliancePromotesClosure : Set where

data OptionContractionPromotesCausalMotive : Set where

classificationErrorDoesNotPromoteFault : ClassificationErrorPromotesFault → ⊥
classificationErrorDoesNotPromoteFault ()

sanctionDoesNotPromoteUnderstanding : SanctionPromotesUnderstanding → ⊥
sanctionDoesNotPromoteUnderstanding ()

quietComplianceDoesNotPromoteClosure : QuietCompliancePromotesClosure → ⊥
quietComplianceDoesNotPromoteClosure ()

optionContractionDoesNotPromoteCausalMotive : OptionContractionPromotesCausalMotive → ⊥
optionContractionDoesNotPromoteCausalMotive ()

record DrugGovernanceErrorAllocationBoundary : Set where
  constructor drugGovernanceErrorAllocationBoundary
  field
    sameClassificationFailureCanBeAllocatedDifferently : Bool
    sameClassificationFailureCanBeAllocatedDifferentlyIsTrue :
      sameClassificationFailureCanBeAllocatedDifferently ≡ true
    faultAllocationCanContractHelpSeeking : Bool
    faultAllocationCanContractHelpSeekingIsTrue :
      faultAllocationCanContractHelpSeeking ≡ true
    repairCanRetainContestAndReassessment : Bool
    repairCanRetainContestAndReassessmentIsTrue :
      repairCanRetainContestAndReassessment ≡ true
    classificationErrorAutomaticallyAuthorizesFault : Bool
    classificationErrorAutomaticallyAuthorizesFaultIsFalse :
      classificationErrorAutomaticallyAuthorizesFault ≡ false

canonicalDrugGovernanceErrorAllocationBoundary :
  DrugGovernanceErrorAllocationBoundary
canonicalDrugGovernanceErrorAllocationBoundary =
  drugGovernanceErrorAllocationBoundary
    true refl true refl true refl false refl
