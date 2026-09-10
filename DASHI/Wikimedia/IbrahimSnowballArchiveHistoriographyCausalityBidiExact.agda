module DASHI.Wikimedia.IbrahimSnowballArchiveHistoriographyCausalityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SourceAcquisitionGeometryExact as Acquisition
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as SymbolicVerification
import DASHI.Wikimedia.IbrahimSnowballQiHexagramWitchDivinationBidiExact as Symbolic
import DASHI.Wikimedia.IbrahimSnowballFactCheckingVerificationMediaLiteracyCorrectionBidiExact as Verification

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL BIDI CONTINUATION
--
-- library/information science <-> archives/bibliography/historiography/
-- source criticism <-> anthropology of divination/magic <-> explanation/
-- causality/testing.
--
-- An archive is a custody/access carrier, a bibliography is a citation/index
-- carrier, historiography is a method/representation discipline, source
-- criticism is an evaluation process, and causal/empirical testing is a
-- separate consumer.  Dewey/QID/DOI/canonical links travel with the graph but
-- create none of those relations by themselves.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim archive/historiography/causality BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create custody, source truth, historiographic adequacy, causal mechanism or authority")

archivesQid : Identity.ExternalIdentityDemand
archivesQid = mkQid "archives" "Q166118"

archivalScienceQid : Identity.ExternalIdentityDemand
archivalScienceQid = mkQid "archival science" "Q380313"

libraryScienceQid : Identity.ExternalIdentityDemand
libraryScienceQid = mkQid "library science" "Q199655"

bibliographyQid : Identity.ExternalIdentityDemand
bibliographyQid = mkQid "bibliography" "Q1631107"

historiographyQid : Identity.ExternalIdentityDemand
historiographyQid = mkQid "historiography" "Q50675"

sourceCriticismQid : Identity.ExternalIdentityDemand
sourceCriticismQid = Verification.sourceCriticismQid

genericCausalityQid : Identity.ExternalIdentityDemand
genericCausalityQid = Identity.mkOptionalIdentityDemand
  "Ibrahim archive/historiography/causality BIDI"
  "external concept identity"
  "generic causality / causation across domains"
  Identity.wikidataQid
  (Identity.unresolved
    "Wikidata distinguishes domain-specific causality/causation items in the inspected neighbourhood; no single generic cross-domain QID promoted here")

------------------------------------------------------------------------
-- Dewey coordinates: retain only inspected values; do not infer semantic
-- dependency from shelf position.
------------------------------------------------------------------------

archivalScienceDewey : SymbolicVerification.DeweyCoordinate
archivalScienceDewey = SymbolicVerification.mkVerifiedDewey
  "archival science"
  "020"
  "Wikidata Q380313 DDC statement inspected 2026-09-11"

libraryScienceDewey : SymbolicVerification.DeweyCoordinate
libraryScienceDewey = SymbolicVerification.mkUnresolvedDewey
  "library science"
  "no exact DDC value separately promoted in this pass; archival science Q380313 supplies an inspected 020 neighbourhood only"

historiographyDewey : SymbolicVerification.DeweyCoordinate
historiographyDewey = SymbolicVerification.mkUnresolvedDewey
  "historiography"
  "no exact inspected DDC value promoted in this pass"

bibliographyDewey : SymbolicVerification.DeweyCoordinate
bibliographyDewey = SymbolicVerification.mkUnresolvedDewey
  "bibliography"
  "no exact inspected DDC value promoted in this pass"

causalityDewey : SymbolicVerification.DeweyCoordinate
causalityDewey = SymbolicVerification.mkUnresolvedDewey
  "causality / causation"
  "domain-relative causal concepts retained; no one DDC coordinate promoted"

------------------------------------------------------------------------
-- Source-bounded scholarship at the anthropology/causality seam.
------------------------------------------------------------------------

geschiereAzandeSource : Attribution.AttributedSource
geschiereAzandeSource = Attribution.mkDOISource
  "Peter Geschiere"
  "Rereading Witchcraft, oracles, and magic among the Azande, fifty-five years later"
  "HAU: Journal of Ethnographic Theory 14(3)"
  "2024"
  "10.1086/732346"
  "https://doi.org/10.1086/732346"
  Attribution.academicArticleSource
  "historical/anthropological rereading of explanatory-system and uncertainty approaches to Azande witchcraft and oracles; does not turn ethnographic coherence into empirical proof of supernatural causation"
  Attribution.publicAttribution

winkelmanMagicSource : Attribution.AttributedSource
winkelmanMagicSource = Attribution.mkDOISource
  "Michael Winkelman"
  "Magic: A Theoretical Reassessment"
  "Anthropology of Consciousness"
  "2021"
  "10.1111/anoc.12142"
  "https://doi.org/10.1111/anoc.12142"
  Attribution.academicArticleSource
  "argues for reassessing anthropological assumptions about magic and discusses parapsychological evidence; represented as the author's theoretical/evidentiary argument, not as DASHI endorsement or established causal fact"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Regression 1: bibliographic metadata cannot recover source acquisition state.
------------------------------------------------------------------------

data ArchiveCase : Set where
  sameMetadataOnly sameMetadataPrimaryInspected : ArchiveCase

data MetadataSurface : Set where sameBibliographicMetadata : MetadataSurface
data AcquisitionStatus : Set where sourceNotInspected sourceInspected : AcquisitionStatus

metadataSurface : ArchiveCase → MetadataSurface
metadataSurface _ = sameBibliographicMetadata

acquisitionStatus : ArchiveCase → AcquisitionStatus
acquisitionStatus sameMetadataOnly = sourceNotInspected
acquisitionStatus sameMetadataPrimaryInspected = sourceInspected

archiveAcquisitionDefect : INF.NonFactorabilityWitness metadataSurface acquisitionStatus
archiveAcquisitionDefect = INF.nonFactorabilityWitness
  sameMetadataOnly sameMetadataPrimaryInspected refl (λ ())

bibliographyCannotFactorInspectionStatus :
  INF.FactorsThrough metadataSurface acquisitionStatus → ⊥
bibliographyCannotFactorInspectionStatus =
  INF.witnessRulesOutEveryFlatFactorisation archiveAcquisitionDefect

------------------------------------------------------------------------
-- Regression 2: archival survival/custody cannot determine historical meaning.
------------------------------------------------------------------------

data HistoricalCase : Set where
  sameArchiveDifferentInterpretationA sameArchiveDifferentInterpretationB : HistoricalCase

data ArchiveSurface : Set where sameArchivalCarrier : ArchiveSurface
data HistoricalReading : Set where historiographicReadingA historiographicReadingB : HistoricalReading

archiveSurface : HistoricalCase → ArchiveSurface
archiveSurface _ = sameArchivalCarrier

historicalReading : HistoricalCase → HistoricalReading
historicalReading sameArchiveDifferentInterpretationA = historiographicReadingA
historicalReading sameArchiveDifferentInterpretationB = historiographicReadingB

archiveHistoryDefect : INF.NonFactorabilityWitness archiveSurface historicalReading
archiveHistoryDefect = INF.nonFactorabilityWitness
  sameArchiveDifferentInterpretationA sameArchiveDifferentInterpretationB refl (λ ())

archiveCannotFactorEveryHistoricalInterpretation :
  INF.FactorsThrough archiveSurface historicalReading → ⊥
archiveCannotFactorEveryHistoricalInterpretation =
  INF.witnessRulesOutEveryFlatFactorisation archiveHistoryDefect

------------------------------------------------------------------------
-- Regression 3: explanatory/meaning role cannot determine empirical causality.
------------------------------------------------------------------------

data ExplanationCase : Set where
  sameExplanatoryMeaningCausalEvidencePaid sameExplanatoryMeaningCausalEvidenceOpen : ExplanationCase

data ExplanationSurface : Set where sameSituatedExplanation : ExplanationSurface
data CausalAudit : Set where causalEvidencePaid causalEvidenceOpen : CausalAudit

explanationSurface : ExplanationCase → ExplanationSurface
explanationSurface _ = sameSituatedExplanation

causalAudit : ExplanationCase → CausalAudit
causalAudit sameExplanatoryMeaningCausalEvidencePaid = causalEvidencePaid
causalAudit sameExplanatoryMeaningCausalEvidenceOpen = causalEvidenceOpen

explanationCausalityDefect : INF.NonFactorabilityWitness explanationSurface causalAudit
explanationCausalityDefect = INF.nonFactorabilityWitness
  sameExplanatoryMeaningCausalEvidencePaid sameExplanatoryMeaningCausalEvidenceOpen refl (λ ())

explanatoryMeaningCannotFactorCausalEvidence :
  INF.FactorsThrough explanationSurface causalAudit → ⊥
explanatoryMeaningCannotFactorCausalEvidence =
  INF.witnessRulesOutEveryFlatFactorisation explanationCausalityDefect

------------------------------------------------------------------------
-- Regression 4: failed empirical causal payment does not erase historical or
-- anthropological meaning/source role.
------------------------------------------------------------------------

data CausalStatusCase : Set where
  sameCausalStatusMeaningA sameCausalStatusMeaningB : CausalStatusCase

data CausalStatusSurface : Set where sameCausalAuditStatus : CausalStatusSurface
data SituatedMeaning : Set where situatedMeaningA situatedMeaningB : SituatedMeaning

causalStatusSurface : CausalStatusCase → CausalStatusSurface
causalStatusSurface _ = sameCausalAuditStatus

situatedMeaning : CausalStatusCase → SituatedMeaning
situatedMeaning sameCausalStatusMeaningA = situatedMeaningA
situatedMeaning sameCausalStatusMeaningB = situatedMeaningB

causalStatusMeaningDefect : INF.NonFactorabilityWitness causalStatusSurface situatedMeaning
causalStatusMeaningDefect = INF.nonFactorabilityWitness
  sameCausalStatusMeaningA sameCausalStatusMeaningB refl (λ ())

causalAuditCannotFactorSituatedMeaning :
  INF.FactorsThrough causalStatusSurface situatedMeaning → ⊥
causalAuditCannotFactorSituatedMeaning =
  INF.witnessRulesOutEveryFlatFactorisation causalStatusMeaningDefect

------------------------------------------------------------------------
-- Existing owners reused.
------------------------------------------------------------------------

acquisitionBoundary : Acquisition.SourceAcquisitionBoundary
acquisitionBoundary = Acquisition.canonicalSourceAcquisitionBoundary

symbolicVerificationBoundary : SymbolicVerification.SymbolicVerificationDeweyQidDoiBoundary
symbolicVerificationBoundary = SymbolicVerification.canonicalSymbolicVerificationDeweyQidDoiBoundary

symbolicBoundary : Symbolic.QiHexagramWitchDivinationBoundary
symbolicBoundary = Symbolic.canonicalQiHexagramWitchDivinationBoundary

verificationBoundary : Verification.FactCheckingVerificationMediaLiteracyCorrectionBoundary
verificationBoundary = Verification.canonicalFactCheckingVerificationMediaLiteracyCorrectionBoundary

------------------------------------------------------------------------
-- Reverse BIDI constraints back into parent graph.
------------------------------------------------------------------------

record ArchiveCausalityReverseConstraint : Set where
  constructor archive-causality-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open ArchiveCausalityReverseConstraint public

informationConstraint : ArchiveCausalityReverseConstraint
informationConstraint = archive-causality-reverse-constraint
  "Library / information science"
  "bibliographic identity, archive custody, access route, primary-text inspection, transcription, source criticism and claim truth remain distinct"
  false

historyConstraint : ArchiveCausalityReverseConstraint
historyConstraint = archive-causality-reverse-constraint
  "History / historiography"
  "event, surviving source, archival selection, later representation, interpretation and present use remain distinct"
  false

anthropologyConstraint : ArchiveCausalityReverseConstraint
anthropologyConstraint = archive-causality-reverse-constraint
  "Anthropology / religion / divination"
  "emic meaning, practice, observer model, explanatory function, causal claim and empirical test remain separately attributable"
  false

scienceConstraint : ArchiveCausalityReverseConstraint
scienceConstraint = archive-causality-reverse-constraint
  "Science / causality"
  "hypothesis, mechanism, intervention/observation, evidence, uncertainty and cultural meaning remain separate consumers"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data ArchiveQidCreatesPrimaryInspection : Set where
data BibliographyCreatesSourceTruth : Set where
data HistoriographyCreatesPastEvent : Set where
data SourceCriticismCreatesTruth : Set where
data ExplanatoryMeaningCreatesCausality : Set where
data FailedCausalAuditErasesMeaning : Set where
data DeweyCreatesDependency : Set where

archiveQidDoesNotCreatePrimaryInspection : ArchiveQidCreatesPrimaryInspection → ⊥
archiveQidDoesNotCreatePrimaryInspection ()

bibliographyDoesNotCreateSourceTruth : BibliographyCreatesSourceTruth → ⊥
bibliographyDoesNotCreateSourceTruth ()

historiographyDoesNotCreatePastEvent : HistoriographyCreatesPastEvent → ⊥
historiographyDoesNotCreatePastEvent ()

sourceCriticismDoesNotCreateTruth : SourceCriticismCreatesTruth → ⊥
sourceCriticismDoesNotCreateTruth ()

explanatoryMeaningDoesNotCreateCausality : ExplanatoryMeaningCreatesCausality → ⊥
explanatoryMeaningDoesNotCreateCausality ()

failedCausalAuditDoesNotEraseMeaning : FailedCausalAuditErasesMeaning → ⊥
failedCausalAuditDoesNotEraseMeaning ()

deweyDoesNotCreateDependency : DeweyCreatesDependency → ⊥
deweyDoesNotCreateDependency ()

record ArchiveHistoriographyCausalityBoundary : Set where
  constructor archive-historiography-causality-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    ambiguousGenericCausalityQidRetained : Bool
    deweyRetainedAsNavigationOnly : Bool
    doiAndCanonicalSourceRetained : Bool
    bibliographySeparatedFromAcquisition : Bool
    archiveSeparatedFromInterpretation : Bool
    historiographySeparatedFromPastEvent : Bool
    explanationSeparatedFromCausalEvidence : Bool
    failedEmpiricalPaymentDoesNotEraseMeaning : Bool
    sourceRoleAndTwoEyedComparisonRetained : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open ArchiveHistoriographyCausalityBoundary public

canonicalArchiveHistoriographyCausalityBoundary : ArchiveHistoriographyCausalityBoundary
canonicalArchiveHistoriographyCausalityBoundary =
  archive-historiography-causality-boundary
    true true true true true true true true true true true false
