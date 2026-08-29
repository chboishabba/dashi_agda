module DASHI.Planning.PNFPlanningGovernanceClaimAdapterExact where

open import DASHI.Core.Prelude
import DASHI.Interop.SensibLawResidualLattice as PNF

------------------------------------------------------------------------
-- PNF PLANNING / GOVERNANCE CLAIM ADAPTER
--
-- Real text enters only through a parser/reducer-produced PNFEmissionReceipt.
-- Planning interpretation is indexed separately so no analyst hand-label can
-- masquerade as a parser receipt or formal residual.
------------------------------------------------------------------------

data PlanningClaimKind : Set where
  consultationClaim consentClaim legalApprovalClaim custodialApprovalClaim
  apologyClaim reparativeClosureClaim recommendationAcceptedClaim
  recommendationImplementedClaim declaredVictoryClaim strategicClosureClaim
  recognitionClaim sovereigntySettlementClaim : PlanningClaimKind

record ReceiptedPlanningClaim : Set where
  constructor receiptedPlanningClaim
  field
    kind : PlanningClaimKind
    emission : PNF.PNFEmissionReceipt

open ReceiptedPlanningClaim public

data HandAssignedPNFPermission : Set where
handAssignedPNFIsBlocked : HandAssignedPNFPermission → ⊥
handAssignedPNFIsBlocked ()

data ClaimKindPromotionPermission : PlanningClaimKind → PlanningClaimKind → Set where

consultationCannotAutoPromoteToConsent :
  ClaimKindPromotionPermission consultationClaim consentClaim → ⊥
consultationCannotAutoPromoteToConsent ()

legalApprovalCannotAutoPromoteToCustodialApproval :
  ClaimKindPromotionPermission legalApprovalClaim custodialApprovalClaim → ⊥
legalApprovalCannotAutoPromoteToCustodialApproval ()

apologyCannotAutoPromoteToReparativeClosure :
  ClaimKindPromotionPermission apologyClaim reparativeClosureClaim → ⊥
apologyCannotAutoPromoteToReparativeClosure ()

acceptedCannotAutoPromoteToImplemented :
  ClaimKindPromotionPermission recommendationAcceptedClaim recommendationImplementedClaim → ⊥
acceptedCannotAutoPromoteToImplemented ()

declaredVictoryCannotAutoPromoteToStrategicClosure :
  ClaimKindPromotionPermission declaredVictoryClaim strategicClosureClaim → ⊥
declaredVictoryCannotAutoPromoteToStrategicClosure ()

recognitionCannotAutoPromoteToSovereigntySettlement :
  ClaimKindPromotionPermission recognitionClaim sovereigntySettlementClaim → ⊥
recognitionCannotAutoPromoteToSovereigntySettlement ()
