module DASHI.Planning.PlanningBIDICapstoneExact where

open import DASHI.Core.Prelude
import DASHI.Planning.AuthorityRelativeReparativeClosureExact as Closure
import DASHI.Planning.IrreversibleActionConsentReopeningGateExact as Irreversible
import DASHI.Planning.SequentialPlanningPolicyBridgeExact as Sequential
import DASHI.Planning.RelationalHistoryFutureConeNonDescentExact as History
import DASHI.Planning.MultiAxisAuthorityFabricExact as Authority
import DASHI.Planning.PNFPlanningGovernanceClaimAdapterExact as PNF
import DASHI.Planning.HarmRepairObligationLedgerExact as Ledger
import DASHI.Planning.NetworkFlowCapacityCongestionExact as Network
import DASHI.Architecture.LiteralBuildingPhysicsAdmissibilityExact as Building
import DASHI.Planning.SourceBoundPlanningCaseAtlasExact as Cases
import DASHI.Planning.NonSubstitutionalReparationExact as Repair
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- BIDI CAPSTONE
--
-- Backward consumers first: a planning branch is not closed merely because a
-- local institutional surface says so.  The following aliases force the ten
-- ranked seams to remain live in one validation/import surface.
------------------------------------------------------------------------

wrongdoerStillCannotCloseLandReturn :
  Closure.ClosureReceipt Closure.wrongdoer Repair.landReturnAxis → ⊥
wrongdoerStillCannotCloseLandReturn = Closure.wrongdoerCannotCertifyLandReturn

newEvidenceStillReopensIrreversibleAction :
  Irreversible.IrreversibleActionGate
    DASHI.Planning.CollectiveTerritorialConsentExact.withdrawableConsent
    Irreversible.materiallyChangedEvidence → ⊥
newEvidenceStillReopensIrreversibleAction =
  Irreversible.materialChangeReopensIrreversibleDecision

robustnessStillCannotClosePlanningByItself :
  Sequential.RobustnessAloneImpliesPlanningTerminalPermission → ⊥
robustnessStillCannotClosePlanningByItself =
  Sequential.robustnessAloneCannotClosePlanning

presentOnlyStillCannotDetermineRelationalFutureCone :
  INF.FactorsThrough History.presentObserver History.futureConeConsumer → ⊥
presentOnlyStillCannotDetermineRelationalFutureCone =
  History.presentOnlyPlanningCannotDetermineFutureCone

statePlanningJurisdictionStillDoesNotCreateHeritageAuthority :
  Authority.CanDecide Authority.stateAuthority Authority.heritageAxis → ⊥
statePlanningJurisdictionStillDoesNotCreateHeritageAuthority =
  Authority.statePlanningPowerDoesNotCreateHeritageAuthority

consultationClaimStillDoesNotPromoteToConsentClaim :
  PNF.ClaimKindPromotionPermission PNF.consultationClaim PNF.consentClaim → ⊥
consultationClaimStillDoesNotPromoteToConsentClaim =
  PNF.consultationCannotAutoPromoteToConsent

compensationStillDoesNotDischargeLandReturnObligation :
  Ledger.ObligationDischarged
    Repair.compensationOnly Ledger.dispossessionHarm Repair.landReturnAxis → ⊥
compensationStillDoesNotDischargeLandReturnObligation =
  Ledger.compensationDoesNotDischargeDispossessionLandReturn

sharedNetworkStillCarriesOverCapacityWitness :
  Network.OverCapacity Network.individualDemandA Network.individualDemandB Network.sharedCapacity
sharedNetworkStillCarriesOverCapacityWitness = Network.canonicalSharedOverCapacity

failedEgressStillBlocksWholeBuildingClosure :
  Building.WholeBuildingAdmissible Building.locallyGoodButEgressFails → ⊥
failedEgressStillBlocksWholeBuildingClosure =
  Building.oneFailedSubsystemBlocksWholeBuildingClosure

livePoliticalCaseStillRequiresRefresh :
  Cases.CaseSource.freshness Cases.trumpIranPalestineLiveSourceBoundary ≡
  Cases.liveRefreshRequired
livePoliticalCaseStillRequiresRefresh = refl
