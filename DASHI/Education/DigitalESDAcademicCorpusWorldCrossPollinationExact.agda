module DASHI.Education.DigitalESDAcademicCorpusWorldCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDSLRSourceReviewBridgeExact as Review
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Wikimedia.IbrahimSnowballSystematicReviewMetaAnalysisPublicationBiasBidiExact as Systematic
import DASHI.Wikimedia.IbrahimSnowballSourceGenealogyIndependenceEvidenceSynthesisBidiExact as Genealogy
import DASHI.Wikimedia.IbrahimSnowballEvidenceSynthesisSourceIndependenceParetoBidiExact as Independence

------------------------------------------------------------------------
-- DIGITAL-ESD ACADEMIC CORPUS WORLD CROSS-POLLINATION
--
-- Reuses existing SensibLaw/SLR scholarly evidence owners rather than defining
-- a Digital-ESD-specific academic ontology.
--
-- Canonical distinctions retained:
--   source/work attribution != source authority
--   manifestation/revision/span/observation remain separate
--   parser/PNF candidate != paper truth
--   reviewer acceptance != SourceAuditAdmission
--   claim ceiling is design/source/receipt relative
--   included publication count != independent evidence units
--   pooled estimate != publication-bias state
--   citation visibility != replicability/evidentiary weight
--   primary-source role != proposition truth
--   publication identity is not title equality and does not require a QID
------------------------------------------------------------------------

slrReviewBoundary : Review.DigitalESDSLRBridgeBoundary
slrReviewBoundary = Review.canonicalDigitalESDSLRBridgeBoundary

studyClaimCeilingBoundary : Ceiling.StudyClaimCeilingBoundary
studyClaimCeilingBoundary = Ceiling.canonicalStudyClaimCeilingBoundary

systematicReviewBoundary : Systematic.SystematicReviewMetaAnalysisBoundary
systematicReviewBoundary = Systematic.canonicalSystematicReviewMetaAnalysisBoundary

sourceGenealogyBoundary :
  Genealogy.SourceGenealogyIndependenceEvidenceSynthesisBoundary
sourceGenealogyBoundary =
  Genealogy.canonicalSourceGenealogyIndependenceEvidenceSynthesisBoundary

sourceIndependenceBoundary :
  Independence.EvidenceSynthesisSourceIndependenceParetoBoundary
sourceIndependenceBoundary =
  Independence.canonicalEvidenceSynthesisSourceIndependenceParetoBoundary

------------------------------------------------------------------------
-- Existing constructive review/synthesis non-factorability.
------------------------------------------------------------------------

includedStudyCountCannotRecoverIndependentEvidenceUnits :
  INF.FactorsThrough
    Systematic.includedCountSurface
    Systematic.evidenceIndependence
  → ⊥
includedStudyCountCannotRecoverIndependentEvidenceUnits =
  Systematic.includedCountCannotFactorIndependentEvidenceUnits

pooledEstimateCannotRecoverPublicationBiasState :
  INF.FactorsThrough
    Systematic.pooledSurface
    Systematic.selectionBiasStatus
  → ⊥
pooledEstimateCannotRecoverPublicationBiasState =
  Systematic.pooledEstimateCannotFactorPublicationBiasStatus

transparentReportingCannotRecoverReviewTruth :
  INF.FactorsThrough
    Systematic.reportingSurface
    Systematic.reviewTruth
  → ⊥
transparentReportingCannotRecoverReviewTruth =
  Systematic.reportingComplianceCannotFactorReviewTruth

reviewInclusionCannotRecoverEvidentiaryWeight :
  INF.FactorsThrough
    Systematic.inclusionSurface
    Systematic.evidentiaryWeight
  → ⊥
reviewInclusionCannotRecoverEvidentiaryWeight =
  Systematic.reviewInclusionCannotFactorEvidentiaryWeight

citationAgreementCannotRecoverPrimarySupport :
  INF.FactorsThrough
    Independence.citationSurface
    Independence.primarySupport
  → ⊥
citationAgreementCannotRecoverPrimarySupport =
  Independence.citationAgreementCannotFactorPrimarySupport

perceivedSourceIndependenceCannotRecoverProvenanceIndependence :
  INF.FactorsThrough
    Independence.perceivedIndependence
    Independence.provenanceIndependence
  → ⊥
perceivedSourceIndependenceCannotRecoverProvenanceIndependence =
  Independence.perceivedIndependenceCannotFactorActualProvenance

------------------------------------------------------------------------
-- Runtime/database consequences.
------------------------------------------------------------------------

data FlatAcademicJsonIsCanonicalCorpusState : Set where
data TitleEqualityCreatesPublicationIdentity : Set where
data DOICreatesEvidenceIndependence : Set where
data PeerReviewCreatesTruth : Set where
data ParserCandidateCreatesPaperTruth : Set where
data ReviewAcceptanceCreatesAuditAdmission : Set where
data IncludedPaperCreatesHighEvidenceWeight : Set where
data PooledEstimateCreatesBiasFreeSynthesis : Set where
data CitationCountCreatesEvidenceWeight : Set where
data PrimarySourceRoleCreatesTruth : Set where
data PublicationQidRequiredForScholarlyIdentity : Set where

flatAcademicJsonDoesNotBecomeCanonicalCorpusState :
  FlatAcademicJsonIsCanonicalCorpusState → ⊥
flatAcademicJsonDoesNotBecomeCanonicalCorpusState ()

titleEqualityDoesNotCreatePublicationIdentity :
  TitleEqualityCreatesPublicationIdentity → ⊥
titleEqualityDoesNotCreatePublicationIdentity ()

doiDoesNotCreateEvidenceIndependence :
  DOICreatesEvidenceIndependence → ⊥
doiDoesNotCreateEvidenceIndependence ()

peerReviewDoesNotCreateTruth :
  PeerReviewCreatesTruth → ⊥
peerReviewDoesNotCreateTruth ()

parserCandidateDoesNotCreatePaperTruth :
  ParserCandidateCreatesPaperTruth → ⊥
parserCandidateDoesNotCreatePaperTruth ()

reviewAcceptanceDoesNotCreateAuditAdmission :
  ReviewAcceptanceCreatesAuditAdmission → ⊥
reviewAcceptanceDoesNotCreateAuditAdmission ()

includedPaperDoesNotCreateHighEvidenceWeight :
  IncludedPaperCreatesHighEvidenceWeight → ⊥
includedPaperDoesNotCreateHighEvidenceWeight ()

pooledEstimateDoesNotCreateBiasFreeSynthesis :
  PooledEstimateCreatesBiasFreeSynthesis → ⊥
pooledEstimateDoesNotCreateBiasFreeSynthesis ()

citationCountDoesNotCreateEvidenceWeight :
  CitationCountCreatesEvidenceWeight → ⊥
citationCountDoesNotCreateEvidenceWeight ()

primarySourceRoleDoesNotCreateTruth :
  PrimarySourceRoleCreatesTruth → ⊥
primarySourceRoleDoesNotCreateTruth ()

publicationQidNotRequiredForScholarlyIdentity :
  PublicationQidRequiredForScholarlyIdentity → ⊥
publicationQidNotRequiredForScholarlyIdentity ()

record DigitalESDAcademicCorpusWorldBoundary : Set where
  constructor digital-esd-academic-corpus-world-boundary
  field
    canonicalSLREvidenceSubstrateReused : Bool
    canonicalSLREvidenceSubstrateReusedIsTrue :
      canonicalSLREvidenceSubstrateReused ≡ true

    exactManifestationRevisionSpanObservationRetained : Bool
    exactManifestationRevisionSpanObservationRetainedIsTrue :
      exactManifestationRevisionSpanObservationRetained ≡ true

    studyClaimCeilingRetained : Bool
    studyClaimCeilingRetainedIsTrue :
      studyClaimCeilingRetained ≡ true

    publicationManifestationAndEvidenceUnitSeparated : Bool
    publicationManifestationAndEvidenceUnitSeparatedIsTrue :
      publicationManifestationAndEvidenceUnitSeparated ≡ true

    sourceGenealogyRetained : Bool
    sourceGenealogyRetainedIsTrue :
      sourceGenealogyRetained ≡ true

    publicationBiasStateRetained : Bool
    publicationBiasStateRetainedIsTrue :
      publicationBiasStateRetained ≡ true

    reviewAdmissionRemainsIndependentPayment : Bool
    reviewAdmissionRemainsIndependentPaymentIsTrue :
      reviewAdmissionRemainsIndependentPayment ≡ true

    publicationQidRequired : Bool
    publicationQidRequiredIsFalse :
      publicationQidRequired ≡ false

    flatJsonIsCanonicalRuntimeState : Bool
    flatJsonIsCanonicalRuntimeStateIsFalse :
      flatJsonIsCanonicalRuntimeState ≡ false

canonicalDigitalESDAcademicCorpusWorldBoundary :
  DigitalESDAcademicCorpusWorldBoundary
canonicalDigitalESDAcademicCorpusWorldBoundary =
  digital-esd-academic-corpus-world-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
