{-# OPTIONS --safe #-}
module DASHI.Unified.SensibLawActionstepGovernanceTOEExact where

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F
--
-- O. Objective.
-- Reconcile existing SensibLaw legal-governance proofs with the operational
-- Actionstep API/compliance surface and attach the handoff to the DASHI TOE.
--
-- R. Reuse.
-- Reuse SensibLaw semantic non-promotion, production legal-runtime ABI,
-- governed legal-network execution, and Pareto-bound source demand.
--
-- C. Construction.
-- Add one source-bounded operational facade. Do not add a second legal
-- semantics, compliance calculus, workflow calculus, or evidence calculus.
--
-- S. Safety.
-- Actionstep workflow, API, OAuth, trust-accounting, review, and vendor
-- compliance statements do not create legal truth, applicability, violation,
-- authority, evidentiary payment, or certification.
--
-- L. Lane.
-- This lane owns only SensibLaw/Actionstep governance -> TOE normalization.
-- It edits no ESD or digital_esd surface.
--
-- P. Preconditions.
-- Existing SensibLaw owners remain authoritative.
-- Actionstep facts below come only from current official Actionstep
-- documentation and remain operational/vendor claims.
--
-- P. Invariants.
-- Source role, legal authority, runtime permission, compliance status, and
-- semantic promotion remain distinct fibres.
-- Original owners retain theorem ownership.
--
-- P. Postconditions.
-- Unified/Everything, Unifier, and EverythingTOESymmetryResolved369 can reach
-- one exact governance receipt and the fail-closed handoff theorems.
--
-- G. Governance.
-- ITIL, ISO 9000/42001/27001/27701/23894/9241, NIST AI RMF, Six Sigma,
-- C4, and PlantUML are process/design lenses only.
-- No standards certification is claimed.
--
-- F. Verification.
-- Reject trust escapes and ESD edits.
-- Kernel-check this module and its validation facade at exact head.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawSemanticPromotionPolicy as Semantic
import DASHI.Law.SensibLawProductionLegalRuntimeABIExact as Runtime
import DASHI.Law.SensibLawGovernedLegalNetworkStrategyExact as Network
import DASHI.Law.SensibLawParetoBoundSourceDemandExact as Pareto

------------------------------------------------------------------------
-- Primary operational source carriers.
--
-- These are vendor operational sources. They are not legal authorities.
-- No DOI is asserted. No person/entity QID is required for payment.
------------------------------------------------------------------------

record ActionstepOperationalSource : Set where
  constructor actionstep-operational-source
  field
    title : String
    stableIdentifier : String
    sourceLink : String
    sourceClass : String
    doi : String
    qid : String
    deweyTraversal : String
    boundedClaim : String

open ActionstepOperationalSource public

actionstepApiSource : ActionstepOperationalSource
actionstepApiSource = actionstep-operational-source
  "Actionstep API"
  "Actionstep documentation route / API overview"
  "https://support.actionstep.com/hc/en-us/articles/50482549518355-Actionstep-API"
  "primary vendor operational documentation"
  "no DOI asserted"
  "unresolvedQid"
  "340 Law / 658 General management; traversal only"
  "The API provides HTTP access to Actionstep business/workflow data. Production API credentials require a separate production access process."

actionstepAuthSource : ActionstepOperationalSource
actionstepAuthSource = actionstep-operational-source
  "Authentication and Authorization"
  "Actionstep developer documentation / authentication"
  "https://docs.actionstep.com/authentication"
  "primary vendor security documentation"
  "no DOI asserted"
  "unresolvedQid"
  "005.8 Data security / 340 Law; traversal only"
  "API requests run under the authenticated user's security context. API access does not grant more or less data access than that user."

actionstepReviewSource : ActionstepOperationalSource
actionstepReviewSource = actionstep-operational-source
  "API Review Process"
  "Actionstep developer documentation / review-process; effective 2026-08-17"
  "https://docs.actionstep.com/review-process"
  "primary vendor production-integration governance documentation"
  "no DOI asserted"
  "unresolvedQid"
  "005.1 Programming / 658 General management; traversal only"
  "Production credentials remain separately requested. Non-commercial integrations use the stated self-assessment process from 2026-08-17."

actionstepQueenslandTrustSource : ActionstepOperationalSource
actionstepQueenslandTrustSource = actionstep-operational-source
  "Understanding Actionstep's Update to the Queensland Trust Reconciliation Process"
  "Actionstep support article / Queensland trust reconciliation"
  "https://support.actionstep.com/hc/en-us/articles/50482556907283-Understanding-Actionstep-s-Update-to-the-Queensland-Trust-Reconciliation-Process"
  "primary vendor jurisdiction-specific operational documentation"
  "no DOI asserted"
  "unresolvedQid"
  "346 Private law / 658.15 Financial management; traversal only"
  "The vendor describes a Queensland reconciliation change and its stated compliance rationale. The vendor statement does not establish a firm's legal compliance."

actionstepPrimaryOperationalSources : List ActionstepOperationalSource
actionstepPrimaryOperationalSources =
  actionstepApiSource
  ∷ actionstepAuthSource
  ∷ actionstepReviewSource
  ∷ actionstepQueenslandTrustSource
  ∷ []

------------------------------------------------------------------------
-- Canonical governance handoff.
------------------------------------------------------------------------

record SensibLawActionstepGovernanceTOEReceipt : Set₁ where
  constructor sensiblaw-actionstep-governance-toe-receipt
  field
    semanticAuthorityBoundary : Semantic.SemanticPromotionPolicySurface
    runtimeProducerBoundary : Runtime.RuntimeLegalProducerBoundary
    agdaFirstBoundary : Runtime.AgdaFirstRuntimeBoundary
    governedNetworkBoundary : Network.GovernedLegalNetworkBoundary
    sources : List ActionstepOperationalSource
    actionstepIsRuntimeConsumerOnly : Bool
    actionstepIsRuntimeConsumerOnlyIsTrue :
      actionstepIsRuntimeConsumerOnly ≡ true
    actionstepCreatesLegalAuthority : Bool
    actionstepCreatesLegalAuthorityIsFalse :
      actionstepCreatesLegalAuthority ≡ false
    actionstepCreatesComplianceProof : Bool
    actionstepCreatesComplianceProofIsFalse :
      actionstepCreatesComplianceProof ≡ false

open SensibLawActionstepGovernanceTOEReceipt public

canonicalSensibLawActionstepGovernanceTOEReceipt :
  SensibLawActionstepGovernanceTOEReceipt
canonicalSensibLawActionstepGovernanceTOEReceipt =
  sensiblaw-actionstep-governance-toe-receipt
    Semantic.semanticPromotionPolicySurface
    Runtime.canonicalRuntimeLegalProducerBoundary
    Runtime.canonicalAgdaFirstRuntimeBoundary
    Network.canonicalGovernedLegalNetworkBoundary
    actionstepPrimaryOperationalSources
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Existing SensibLaw non-promotion laws remain the theorem owners.
------------------------------------------------------------------------

semanticPromotionDoesNotCreateLegalAuthority :
  Semantic.legalAuthorityFlag Semantic.semanticPromotionAuthorityBoundary ≡ false
semanticPromotionDoesNotCreateLegalAuthority =
  Semantic.semantic-promotion-legal-authority-closed

sourceFollowDoesNotCreateAuthority :
  Runtime.SourceFollowAutomaticallyAuthority → ⊥
sourceFollowDoesNotCreateAuthority =
  Runtime.sourceFollowDoesNotEstablishAuthority

typedMeetDoesNotCreateViolation :
  Runtime.TypedMeetAutomaticallyViolation → ⊥
typedMeetDoesNotCreateViolation =
  Runtime.typedMeetDoesNotEstablishViolation

proofGapDoesNotTriggerUngovernedNetwork :
  Network.ProofGapMayTriggerUngovernedNetwork → ⊥
proofGapDoesNotTriggerUngovernedNetwork =
  Network.proofGapDoesNotTriggerUngovernedNetwork

boundSourceDemandDoesNotCreateAuthority :
  Pareto.BoundSourceDemandCreatesLegalAuthority → ⊥
boundSourceDemandDoesNotCreateAuthority =
  Pareto.boundDemandDoesNotCreateAuthority

------------------------------------------------------------------------
-- Actionstep-specific no-promotion laws.
------------------------------------------------------------------------

data ActionstepWorkflowCreatesLegalApplicability : Set where
data ActionstepUserPermissionCreatesLegalAuthority : Set where
data ActionstepApiAccessPaysEvidenceRequirement : Set where
data ActionstepVendorComplianceClaimProvesFirmCompliance : Set where
data ActionstepProductionCredentialProvesSemanticValidity : Set where
data ActionstepTrustFeatureProvesJurisdictionCompliance : Set where

actionstepWorkflowDoesNotCreateLegalApplicability :
  ActionstepWorkflowCreatesLegalApplicability → ⊥
actionstepWorkflowDoesNotCreateLegalApplicability ()

actionstepPermissionDoesNotCreateLegalAuthority :
  ActionstepUserPermissionCreatesLegalAuthority → ⊥
actionstepPermissionDoesNotCreateLegalAuthority ()

actionstepApiAccessDoesNotPayEvidenceRequirement :
  ActionstepApiAccessPaysEvidenceRequirement → ⊥
actionstepApiAccessDoesNotPayEvidenceRequirement ()

actionstepVendorClaimDoesNotProveFirmCompliance :
  ActionstepVendorComplianceClaimProvesFirmCompliance → ⊥
actionstepVendorClaimDoesNotProveFirmCompliance ()

actionstepProductionCredentialDoesNotProveSemanticValidity :
  ActionstepProductionCredentialProvesSemanticValidity → ⊥
actionstepProductionCredentialDoesNotProveSemanticValidity ()

actionstepTrustFeatureDoesNotProveJurisdictionCompliance :
  ActionstepTrustFeatureProvesJurisdictionCompliance → ⊥
actionstepTrustFeatureDoesNotProveJurisdictionCompliance ()

------------------------------------------------------------------------
-- ZKP frame.
------------------------------------------------------------------------

record SensibLawActionstepTOEZKPFrame : Set where
  constructor sensiblaw-actionstep-toe-zkp-frame
  field
    O-objective : String
    R-reuse : String
    C-construction : String
    S-safety : String
    L-lane : String
    P-preconditions : String
    P-invariants : String
    P-postconditions : String
    G-governance : String
    F-verification : String

canonicalSensibLawActionstepTOEZKPFrame : SensibLawActionstepTOEZKPFrame
canonicalSensibLawActionstepTOEZKPFrame =
  sensiblaw-actionstep-toe-zkp-frame
    "Converge SensibLaw governance and Actionstep operational workflow boundaries into the DASHI TOE."
    "Reuse SensibLaw semantic promotion, legal runtime ABI, governed network, and Pareto bound-source-demand owners."
    "Expose one source-bounded operational receipt and theorem aliases only."
    "Keep runtime permission, workflow, vendor compliance claims, legal authority, evidence payment, applicability, and violation distinct."
    "Own only SensibLaw/Actionstep governance to TOE normalization; mutate no ESD surface."
    "All SensibLaw theorem owners exist; Actionstep facts are bounded to current primary vendor operational documentation."
    "Original owners retain proof ownership; QID/Dewey/source links remain coordinates; no runtime carrier creates legal or semantic authority."
    "All three TOE surfaces reach the same receipt and fail-closed theorem handoffs."
    "Standards remain process lenses only; no certification or legal-compliance conclusion is claimed."
    "Run trust-escape, ESD-diff, root/import, validation, and exact-head Agda kernel checks."
