module DASHI.Planning.PlanningPNFClaimBoundaryExact where

open import DASHI.Core.Prelude
import DASHI.Interop.SensibLawResidualLattice as PNF

------------------------------------------------------------------------
-- PLANNING CLAIM / PNF BOUNDARY
--
-- PNF is the receipted linguistic/claim-comparison layer.  This planning seam
-- deliberately does not hand-assign parser wrappers or residual classes.
-- Instead it records the semantic promotions that must remain blocked even
-- when source text contains superficially adjacent predicates.
------------------------------------------------------------------------

data PlanningClaimKind : Set where
  consultationClaim
  consentClaim
  legalApprovalClaim
  custodialApprovalClaim
  apologyClaim
  repairClaim
  recommendationAcceptedClaim
  recommendationImplementedClaim
  victoryDeclaredClaim
  strategicClosureClaim
  : PlanningClaimKind

record PlanningClaimBoundary : Set where
  constructor planningClaimBoundary
  field
    consultedMeansConsented : Bool
    consultedMeansConsentedIsFalse : consultedMeansConsented ≡ false
    legalApprovalMeansCustodialApproval : Bool
    legalApprovalMeansCustodialApprovalIsFalse :
      legalApprovalMeansCustodialApproval ≡ false
    apologyMeansRepair : Bool
    apologyMeansRepairIsFalse : apologyMeansRepair ≡ false
    recommendationAcceptedMeansImplemented : Bool
    recommendationAcceptedMeansImplementedIsFalse :
      recommendationAcceptedMeansImplemented ≡ false
    declaredVictoryMeansStrategicClosure : Bool
    declaredVictoryMeansStrategicClosureIsFalse :
      declaredVictoryMeansStrategicClosure ≡ false
    analystMayHandAssignPNFWrapper : Bool
    analystMayHandAssignPNFWrapperIsFalse : analystMayHandAssignPNFWrapper ≡ false
    analystMayHandAssignResidual : Bool
    analystMayHandAssignResidualIsFalse : analystMayHandAssignResidual ≡ false

canonicalPlanningClaimBoundary : PlanningClaimBoundary
canonicalPlanningClaimBoundary =
  planningClaimBoundary
    false refl false refl false refl false refl false refl false refl false refl

-- Importing the literal PNF owner here is intentional: downstream adapters
-- should consume its emitted/receipted atoms rather than create a planning-
-- specific parser or manually classify live political text.
record PNFPlanningAdapterBoundary : Set where
  constructor pnfPlanningAdapterBoundary
  field
    planningCreatesIndependentPNFParser : Bool
    planningCreatesIndependentPNFParserIsFalse :
      planningCreatesIndependentPNFParser ≡ false
    sourceTextAloneCreatesFormalResidual : Bool
    sourceTextAloneCreatesFormalResidualIsFalse :
      sourceTextAloneCreatesFormalResidual ≡ false

canonicalPNFPlanningAdapterBoundary : PNFPlanningAdapterBoundary
canonicalPNFPlanningAdapterBoundary =
  pnfPlanningAdapterBoundary false refl false refl
