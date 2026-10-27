{-# OPTIONS --safe #-}
module DASHI.Unified.SensibLawGovernanceTOEExact where

------------------------------------------------------------------------
-- SENSIBLAW / LEGAL GOVERNANCE TOE NORMALIZATION
--
-- This module reuses existing theorem owners.
-- It does not create legal authority.
-- It does not create vendor authority.
-- It does not replace source attribution.
-- It does not identify a case-management implementation with legal doctrine.
--
-- Historical SensibLaw ownership stays with the imported SensibLaw modules.
-- Legal-runtime ownership stays with the imported legal runtime modules.
-- Generic authority transport stays with the governance owner.
-- External meta-introspector repositories retain separate authorship and
-- theorem authority.  This module imports no theorem from those repositories.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Promotion.AuthorityBoundaryCore as Boundary
import DASHI.Interop.SensibLawSemanticPromotionPolicy as Semantic
import DASHI.Law.SensibLawAgdaFirstLegalRuntimeEverything as LegalRuntime
import DASHI.Law.SensibLawITIRParityEverything as Parity
import DASHI.Governance.DomainPermeabilityAuthorityTransport as Domain
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Interop.SensibLawSnowballAttributionLineageAdapterExact as SnowballLineage
import DASHI.Law.SensibLawParetoProofDirectedCorpusSearchEverything as ParetoSearch

------------------------------------------------------------------------
-- Reused canonical owners.
------------------------------------------------------------------------

governanceSemanticAuthorityBoundary :
  Authority.AuthorityNonPromotionBundle
governanceSemanticAuthorityBoundary =
  Semantic.semanticPromotionAuthorityBoundary

governanceSemanticTruthAuthorityStillClosed :
  Authority.truthAuthorityFlag governanceSemanticAuthorityBoundary ≡ false
governanceSemanticTruthAuthorityStillClosed =
  Semantic.semantic-promotion-truth-authority-closed

governanceSemanticLegalAuthorityStillClosed :
  Authority.legalAuthorityFlag governanceSemanticAuthorityBoundary ≡ false
governanceSemanticLegalAuthorityStillClosed =
  Semantic.semantic-promotion-legal-authority-closed

governanceSemanticAllAuthorityStillClosed :
  Authority.promotesAnyAuthority governanceSemanticAuthorityBoundary ≡ false
governanceSemanticAllAuthorityStillClosed =
  Semantic.semantic-promotion-all-authority-closed

governanceLegalAuthorityBoundaryReceipt :
  Boundary.AuthorityBoundaryReceipt
governanceLegalAuthorityBoundaryReceipt =
  Boundary.canonicalLegalAuthorityBoundaryReceipt

governanceLegalAuthorityBoundaryStillFailClosed :
  Authority.promotesAnyAuthority
    (Boundary.receiptAuthorityBundle governanceLegalAuthorityBoundaryReceipt)
  ≡ false
governanceLegalAuthorityBoundaryStillFailClosed =
  Boundary.authorityBoundaryBundlePromotesAnyAuthorityIsFalse
    governanceLegalAuthorityBoundaryReceipt

governanceLegalRuntimeContract :
  LegalRuntime.AgdaFirstLegalRuntimeContract
governanceLegalRuntimeContract =
  LegalRuntime.canonicalAgdaFirstLegalRuntimeContract

governanceRuntimeCannotInventLegalSemantics :
  LegalRuntime.AgdaFirstLegalRuntimeContract.runtimeMayInventMissingFormalLegalSemantics
    governanceLegalRuntimeContract
  ≡ false
governanceRuntimeCannotInventLegalSemantics =
  LegalRuntime.AgdaFirstLegalRuntimeContract.runtimeMayInventMissingFormalLegalSemanticsIsFalse
    governanceLegalRuntimeContract

governanceParserCandidateCannotBecomeTruthByTransport :
  LegalRuntime.AgdaFirstLegalRuntimeContract.parserCandidateMayBecomeTruthByTransport
    governanceLegalRuntimeContract
  ≡ false
governanceParserCandidateCannotBecomeTruthByTransport =
  LegalRuntime.AgdaFirstLegalRuntimeContract.parserCandidateMayBecomeTruthByTransportIsFalse
    governanceLegalRuntimeContract

governanceSourceFollowCannotBecomeAuthorityByTransport :
  LegalRuntime.AgdaFirstLegalRuntimeContract.sourceFollowMayBecomeAuthorityByTransport
    governanceLegalRuntimeContract
  ≡ false
governanceSourceFollowCannotBecomeAuthorityByTransport =
  LegalRuntime.AgdaFirstLegalRuntimeContract.sourceFollowMayBecomeAuthorityByTransportIsFalse
    governanceLegalRuntimeContract

governanceTypedMeetCannotBecomeViolationByTransport :
  LegalRuntime.AgdaFirstLegalRuntimeContract.typedMeetMayBecomeViolationByTransport
    governanceLegalRuntimeContract
  ≡ false
governanceTypedMeetCannotBecomeViolationByTransport =
  LegalRuntime.AgdaFirstLegalRuntimeContract.typedMeetMayBecomeViolationByTransportIsFalse
    governanceLegalRuntimeContract

governanceElementPaymentCannotBecomeLiabilityByTransport :
  LegalRuntime.AgdaFirstLegalRuntimeContract.wrongTypeElementPaymentMayBecomeLiabilityByTransport
    governanceLegalRuntimeContract
  ≡ false
governanceElementPaymentCannotBecomeLiabilityByTransport =
  LegalRuntime.AgdaFirstLegalRuntimeContract.wrongTypeElementPaymentMayBecomeLiabilityByTransportIsFalse
    governanceLegalRuntimeContract

governanceITIRParityLegalRuntimeContract :
  LegalRuntime.AgdaFirstLegalRuntimeContract
governanceITIRParityLegalRuntimeContract =
  Parity.selectedLegalRuntimeContract

governanceITIRParityUsesCanonicalLegalRuntime :
  governanceITIRParityLegalRuntimeContract
  ≡ governanceLegalRuntimeContract
governanceITIRParityUsesCanonicalLegalRuntime =
  refl

------------------------------------------------------------------------
-- Generic case-management and workflow transport boundary.
--
-- This is the existing reusable owner for vendor-neutral case-management
-- transport.  No named vendor gains authority from representation reuse.
------------------------------------------------------------------------

governanceDomainTransportReceipt :
  Domain.DomainTransportReceipt
governanceDomainTransportReceipt =
  Domain.canonicalDomainTransportReceipt

governanceSameTechnicalGrammarDoesNotImplySameMandate :
  Domain.DomainTransportReceipt.sameTechnicalGrammarImpliesSameMandate governanceDomainTransportReceipt
  ≡ false
governanceSameTechnicalGrammarDoesNotImplySameMandate =
  refl

governanceTargetDomainNeedsOwnAuthorityWitness :
  Domain.DomainTransportReceipt.targetDomainNeedsOwnAuthorityWitness governanceDomainTransportReceipt
  ≡ true
governanceTargetDomainNeedsOwnAuthorityWitness =
  refl

governanceRepresentationEqualityDoesNotCreateLegalAuthority :
  Domain.DomainTransportReceipt.representationEqualityCreatesLegalAuthority governanceDomainTransportReceipt
  ≡ false
governanceRepresentationEqualityDoesNotCreateLegalAuthority =
  refl

governanceVendorIdentityDoesNotCreateAuthority :
  Domain.DomainTransportReceipt.vendorIdentityCreatesAuthority governanceDomainTransportReceipt
  ≡ false
governanceVendorIdentityDoesNotCreateAuthority =
  refl

governanceDomainPermeabilityRequiresReview :
  Domain.DomainTransportReceipt.domainPermeabilityRequiresGovernanceReview governanceDomainTransportReceipt
  ≡ true
governanceDomainPermeabilityRequiresReview =
  refl

governanceSameMachineryDoesNotTransportAuthority :
  (Domain.represent Domain.exampleMachinery Domain.sourceDomain Domain.subject
    ≡
   Domain.represent Domain.exampleMachinery Domain.targetDomain Domain.subject →
   Domain.authorised
     Domain.exampleAuthority Domain.sourceDomain Domain.subject →
   Domain.authorised
     Domain.exampleAuthority Domain.targetDomain Domain.subject) →
  ⊥
governanceSameMachineryDoesNotTransportAuthority =
  Domain.sameMachineryDoesNotTransportAuthority

------------------------------------------------------------------------
-- Pareto / snowball governance reuse.
--
-- These owners are already used across SensibLaw and Ibrahim snowball lanes.
-- This normalization keeps attribution and legal authority separate.
------------------------------------------------------------------------

governanceAttributionSnowballBoundary :
  Snowball.AttributionSnowballBoundary
governanceAttributionSnowballBoundary =
  Snowball.canonicalAttributionSnowballBoundary

governanceSnowballCitationDoesNotPromoteProof :
  Snowball.citationMayPromoteProof governanceAttributionSnowballBoundary
  ≡ false
governanceSnowballCitationDoesNotPromoteProof =
  refl

governanceSnowballCitationDoesNotCreateAuthority :
  Snowball.citationMayCreateAuthority governanceAttributionSnowballBoundary
  ≡ false
governanceSnowballCitationDoesNotCreateAuthority =
  refl

governanceSensibLawSnowballLineageBoundary :
  SnowballLineage.SensibLawSnowballLineageBoundary
governanceSensibLawSnowballLineageBoundary =
  SnowballLineage.canonicalSensibLawSnowballLineageBoundary

governanceSnowballCitationDoesNotCreateLegalAuthority :
  SnowballLineage.SensibLawSnowballLineageBoundary.citationCreatesLegalAuthority
    governanceSensibLawSnowballLineageBoundary
  ≡ false
governanceSnowballCitationDoesNotCreateLegalAuthority =
  refl

governanceSnowballSameSourceIdentityDoesNotDetermineClaimStage :
  SnowballLineage.SensibLawSnowballLineageBoundary.sameSourceIdentityDeterminesClaimStage
    governanceSensibLawSnowballLineageBoundary
  ≡ false
governanceSnowballSameSourceIdentityDoesNotDetermineClaimStage =
  refl

governanceParetoDirectiveIsNotLegalAuthority :
  ParetoSearch.SearchDirectiveIsLegalAuthority → ⊥
governanceParetoDirectiveIsNotLegalAuthority =
  ParetoSearch.directiveIsNotAuthority

governanceParetoFrontierDoesNotPrejudgeRetrieval :
  ParetoSearch.FrontierCertificateMakesRetrievedSourceTrue → ⊥
governanceParetoFrontierDoesNotPrejudgeRetrieval =
  ParetoSearch.frontierCertificateDoesNotPrejudgeRetrieval

governanceParetoFeedbackClosureStillNeedsActionAuthority :
  ParetoSearch.FeedbackClosureAutomaticallyAuthorisesAction → ⊥
governanceParetoFeedbackClosureStillNeedsActionAuthority =
  ParetoSearch.feedbackClosureStillNeedsActionAuthority

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F control frame.
------------------------------------------------------------------------

record SensibLawGovernanceTOEZKPFrame : Set where
  field
    O-objective : String
    R-reuse : String
    C-construction : String
    S-safety : String
    L-lane : String
    P-postcondition : String
    G-governance : String
    F-verification : String

    preconditionCanonicalOwnersPresent : Bool
    preconditionCanonicalOwnersPresentIsTrue :
      preconditionCanonicalOwnersPresent ≡ true

    invariantSemanticPromotionDoesNotGrantAuthority : Bool
    invariantSemanticPromotionDoesNotGrantAuthorityIsTrue :
      invariantSemanticPromotionDoesNotGrantAuthority ≡ true

    invariantRuntimeTransportDoesNotCreateLegalTruth : Bool
    invariantRuntimeTransportDoesNotCreateLegalTruthIsTrue :
      invariantRuntimeTransportDoesNotCreateLegalTruth ≡ true

    invariantCaseManagementReuseDoesNotTransportAuthority : Bool
    invariantCaseManagementReuseDoesNotTransportAuthorityIsTrue :
      invariantCaseManagementReuseDoesNotTransportAuthority ≡ true

    postconditionTOENormalizationOnly : Bool
    postconditionTOENormalizationOnlyIsTrue :
      postconditionTOENormalizationOnly ≡ true

canonicalSensibLawGovernanceTOEZKPFrame :
  SensibLawGovernanceTOEZKPFrame
canonicalSensibLawGovernanceTOEZKPFrame =
  record
    { O-objective =
        "Normalize existing SensibLaw, legal-runtime, parity, and authority non-promotion proofs into the DASHI TOE graph."
    ; R-reuse =
        "Reuse AuthorityNonPromotionCore, AuthorityBoundaryCore, SensibLawSemanticPromotionPolicy, SensibLawAgdaFirstLegalRuntimeEverything, SensibLawITIRParityEverything, DomainPermeabilityAuthorityTransport, SnowballAttributionProvenanceInvariantExact, SensibLawSnowballAttributionLineageAdapterExact, and SensibLawParetoProofDirectedCorpusSearchEverything."
    ; C-construction =
        "Add only a theorem-thin normalization owner and facade agreement. Do not duplicate semantic or legal proofs."
    ; S-safety =
        "Keep truth, legal authority, runtime authority, liability, mandate, and vendor identity as separate typed obligations. Keep ESD surfaces import-only."
    ; L-lane =
        "One disjoint governance normalization lane. It does not alter physics, ESD, or external repository theorem ownership."
    ; P-postcondition =
        "The TOE root, Unifier, and Unified facade consume the same canonical fail-closed governance owners."
    ; G-governance =
        "Use ITIL, ISO 9000, ISO/IEC 42001, ISO/IEC 27001, ISO/IEC 27701, ISO/IEC 23894, ISO 9241, NIST AI RMF, Six Sigma, and C4/PlantUML as process lenses only. Make no certification claim."
    ; F-verification =
        "Require repository-referee discovery and lineage checks, zero trust escapes, ESD isolation, facade regression, and Agda kernel checking."
    ; preconditionCanonicalOwnersPresent = true
    ; preconditionCanonicalOwnersPresentIsTrue = refl
    ; invariantSemanticPromotionDoesNotGrantAuthority = true
    ; invariantSemanticPromotionDoesNotGrantAuthorityIsTrue = refl
    ; invariantRuntimeTransportDoesNotCreateLegalTruth = true
    ; invariantRuntimeTransportDoesNotCreateLegalTruthIsTrue = refl
    ; invariantCaseManagementReuseDoesNotTransportAuthority = true
    ; invariantCaseManagementReuseDoesNotTransportAuthorityIsTrue = refl
    ; postconditionTOENormalizationOnly = true
    ; postconditionTOENormalizationOnlyIsTrue = refl
    }
