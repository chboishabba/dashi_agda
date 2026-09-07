module DASHI.Core.EmpiricalSourceDiligenceAdmissionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- EMPIRICAL SOURCE-DILIGENCE ADMISSION
--
-- Repo-wide policy: an empirical proposition may not be promoted merely from a
-- convenient citation string.  It must retain the canonical AttributedSource
-- carrier and an explicit primary-source search, exact locator, temporal/scope
-- bounds, contradiction search, interpretation boundary and applicability
-- boundary.  A citation still creates neither truth nor domain authority.
------------------------------------------------------------------------

data PrimarySearchOutcome : Set where
  primaryLocated : PrimarySearchOutcome
  primaryUnavailable : PrimarySearchOutcome
  primaryInapplicable : PrimarySearchOutcome

data SourceRole : Set where
  primaryProposition : SourceRole
  implementationEvidence : SourceRole
  corroboratingEvidence : SourceRole
  contestingEvidence : SourceRole
  contextualEvidence : SourceRole
  interpretiveEvidence : SourceRole

record SourceDiligence : Set where
  constructor source-diligence
  field
    claimReference : String
    selectedSource : Source.AttributedSource
    sourceRole : SourceRole
    primarySearchAttempted : Bool
    primarySearchAttemptedIsTrue : primarySearchAttempted ≡ true
    primarySearchMethodReference : String
    primarySearchOutcome : PrimarySearchOutcome
    exactSpanOrLocatorReference : String
    sourceDateOrRevisionReference : String
    sameObjectReference : String
    temporalScopeReference : String
    coverageReference : String
    contradictionSearchReference : String
    interpretationBoundaryReference : String
    applicabilityReference : String

open SourceDiligence public

record EmpiricalFactAdmission : Set where
  constructor empirical-fact-admission
  field
    diligence : SourceDiligence
    boundedPropositionReference : String
    sourceSupportsBoundedPropositionReference : String
    provenanceSurvivesProjectionReference : String
    uncertaintyReference : String
    downstreamAuthorityReference : String
    sourceIdentityCreatesTruth : Bool
    sourceIdentityCreatesTruthIsFalse : sourceIdentityCreatesTruth ≡ false
    sourceIdentityCreatesApplicability : Bool
    sourceIdentityCreatesApplicabilityIsFalse : sourceIdentityCreatesApplicability ≡ false
    interpretationBecomesSourceProposition : Bool
    interpretationBecomesSourcePropositionIsFalse : interpretationBecomesSourceProposition ≡ false

open EmpiricalFactAdmission public

data EmpiricalFactWithoutPrimarySearch : Set where
data CitationCreatesEmpiricalTruth : Set where
data CitationCreatesApplicability : Set where

factAdmissionRequiresPrimarySearch : EmpiricalFactWithoutPrimarySearch → ⊥
factAdmissionRequiresPrimarySearch ()

citationDoesNotCreateEmpiricalTruth : CitationCreatesEmpiricalTruth → ⊥
citationDoesNotCreateEmpiricalTruth ()

citationDoesNotCreateApplicability : CitationCreatesApplicability → ⊥
citationDoesNotCreateApplicability ()

record EmpiricalSourceDiligenceBoundary : Set where
  constructor empirical-source-diligence-boundary
  field
    authorTitlePublicationShouldUseAttributedSourceCore : Bool
    authorTitlePublicationShouldUseAttributedSourceCoreIsTrue :
      authorTitlePublicationShouldUseAttributedSourceCore ≡ true
    primarySearchAttemptIsRequiredForNewEmpiricalPromotion : Bool
    primarySearchAttemptIsRequiredForNewEmpiricalPromotionIsTrue :
      primarySearchAttemptIsRequiredForNewEmpiricalPromotion ≡ true
    secondaryFallbackMayBeExplicitlyRetained : Bool
    secondaryFallbackMayBeExplicitlyRetainedIsTrue :
      secondaryFallbackMayBeExplicitlyRetained ≡ true
    citationAloneCreatesAuthority : Bool
    citationAloneCreatesAuthorityIsFalse : citationAloneCreatesAuthority ≡ false

canonicalEmpiricalSourceDiligenceBoundary : EmpiricalSourceDiligenceBoundary
canonicalEmpiricalSourceDiligenceBoundary =
  empirical-source-diligence-boundary true refl true refl true refl false refl

canonicalEmpiricalSourceDiligenceReceipt : Receipt.GenericReceipt
canonicalEmpiricalSourceDiligenceReceipt =
  Receipt.mkNonPromotingReceipt
    "empirical source diligence admission"
    "DASHI.Core.EmpiricalSourceDiligenceAdmissionExact"
    "SourceDiligence / EmpiricalFactAdmission"
    "requires canonical attributed-source metadata plus primary-search, span, time, same-object, coverage, contradiction, interpretation and applicability boundaries"
    "domain-specific source authority and proposition payment remain separate proof obligations"
    "agda -i . DASHI/Core/EmpiricalSourceDiligenceAdmissionExact.agda"
