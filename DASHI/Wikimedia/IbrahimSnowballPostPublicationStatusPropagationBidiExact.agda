module DASHI.Wikimedia.IbrahimSnowballPostPublicationStatusPropagationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballFactCheckingVerificationMediaLiteracyCorrectionBidiExact as Verification
import DASHI.Wikimedia.IbrahimSnowballReplicationSourceGenealogyEvidenceSynthesisBidiExact as Synthesis
import DASHI.Wikimedia.IbrahimSnowballAtomicClaimIntentExperimentAdequacyBidiExact as Atomic

------------------------------------------------------------------------
-- POST-PUBLICATION STATUS / DOWNSTREAM PROPAGATION BIDI
--
-- Publication is not the terminal evidentiary state.  Correction, expression
-- of concern, addendum, retraction and replacement are separate append-only
-- provenance objects.  A downstream citation/review/media/synthesis consumer
-- must therefore resolve the current status of the exact source object before
-- treating historical citation count or an earlier cached copy as current
-- evidential support.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim post-publication-status propagation BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not itself establish scope, truth, downstream invalidity or current source status")

retractionQid : Identity.ExternalIdentityDemand
retractionQid = Verification.retractionQid

retractionNoticeQid : Identity.ExternalIdentityDemand
retractionNoticeQid = Verification.retractionNoticeQid

retractedPaperQid : Identity.ExternalIdentityDemand
retractedPaperQid = mkQid "retracted paper" "Q45182324"

expressionOfConcernQid : Identity.ExternalIdentityDemand
expressionOfConcernQid = mkQid "expression of concern" "Q56478376"

correctionQid : Identity.ExternalIdentityDemand
correctionQid = Verification.correctionQid

crossmarkQid : Identity.ExternalIdentityDemand
crossmarkQid = Identity.mkOptionalIdentityDemand
  "Ibrahim post-publication-status propagation BIDI"
  "external service identity"
  "Crossmark / post-publication update status service"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact Crossmark QID promoted in this pass; canonical Crossref service link retained separately")

postPublicationStatusDewey : Dewey.DeweyCoordinate
postPublicationStatusDewey = Dewey.mkUnresolvedDewey
  "post-publication correction / expression of concern / retraction"
  "no exact single DDC coordinate promoted; publishing ethics, bibliography, research integrity and domain-specific evidence consumers overlap"

------------------------------------------------------------------------
-- Primary / institutional provenance.
------------------------------------------------------------------------

crossrefCrossmarkSource : Attribution.AttributedSource
crossrefCrossmarkSource = Attribution.mkNoDOISource
  "Crossref"
  "Crossmark"
  "Crossref official documentation"
  "current documentation inspected 2026-09-11"
  "https://www.crossref.org/services/crossmark/"
  Attribution.institutionalSource
  "official source for Crossmark current-status/update semantics; states that corrections, retractions and other substantive updates can be surfaced to readers; service metadata does not itself adjudicate every affected downstream claim"
  Attribution.publicAttribution

copeRetractionGuidelinesSource : Attribution.AttributedSource
copeRetractionGuidelinesSource = Attribution.mkDOISource
  "COPE Council"
  "COPE Retraction guidelines — English"
  "Committee on Publication Ethics"
  "2019"
  "10.24318/cope.2019.1.4"
  "https://doi.org/10.24318/cope.2019.1.4"
  Attribution.institutionalSource
  "publication-ethics guidance distinguishing retraction reasons and requiring linked, explicit notices; guidance is not a proposition-level truth oracle"
  Attribution.publicAttribution

climateCorrectionSource : Attribution.AttributedSource
climateCorrectionSource = Attribution.mkDOISource
  "Maximilian Kotz; Anders Levermann; Leonie Wenz"
  "Author Correction: The economic commitment of climate change"
  "Nature 631, E9"
  "2024"
  "10.1038/s41586-024-07732-2"
  "https://doi.org/10.1038/s41586-024-07732-2"
  Attribution.academicArticleSource
  "primary post-publication correction notice for the 2024 Nature article; explicitly reported that the listed corrections did not affect manuscript results, while later status history must still be checked separately"
  Attribution.publicAttribution

climateRetractionSource : Attribution.AttributedSource
climateRetractionSource = Attribution.mkDOISource
  "Maximilian Kotz; Anders Levermann; Leonie Wenz"
  "Retraction Note: The economic commitment of climate change"
  "Nature 648, 764"
  "2025"
  "10.1038/s41586-025-09726-0"
  "https://doi.org/10.1038/s41586-025-09726-0"
  Attribution.academicArticleSource
  "primary retraction notice for DOI 10.1038/s41586-024-07219-0; documents later substantial data/methodology sensitivity and a revised not-yet-peer-reviewed version; downstream uses require source- and claim-scoped re-audit"
  Attribution.publicAttribution

aiEducationRetractionSource : Attribution.AttributedSource
aiEducationRetractionSource = Attribution.mkDOISource
  "Sayed Fayaz Ahmad; Heesup Han; Muhammad Mansoor Alam; Mohd. Khairul Rehmat; Muhammad Irshad; Marcelo Arraño-Muñoz; Antonio Ariza-Montes et al."
  "Retraction Note: Impact of artificial intelligence on human loss in decision making, laziness and safety in education"
  "Humanities and Social Sciences Communications 13, 150"
  "2026"
  "10.1057/s41599-026-06602-8"
  "https://doi.org/10.1057/s41599-026-06602-8"
  Attribution.academicArticleSource
  "primary retraction notice linked to the earlier AI/education article; demonstrates that downstream AI/pedagogy claims must resolve current publication status rather than rely on historical article presence alone"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Exact upstream reuse: no parallel verification or synthesis ontology.
------------------------------------------------------------------------

verificationBoundary : Verification.FactCheckingVerificationMediaLiteracyCorrectionBoundary
verificationBoundary = Verification.canonicalFactCheckingVerificationMediaLiteracyCorrectionBoundary

synthesisBoundary : Synthesis.ReplicationSourceGenealogyEvidenceSynthesisBoundary
synthesisBoundary = Synthesis.canonicalReplicationSourceGenealogyEvidenceSynthesisBoundary

atomicBoundary : Atomic.AtomicClaimIntentExperimentAdequacyBoundary
atomicBoundary = Atomic.canonicalAtomicClaimIntentExperimentAdequacyBoundary

------------------------------------------------------------------------
-- Status history is append-only and object-indexed.
------------------------------------------------------------------------

data PublicationStatus : Set where
  publishedUnqualified : PublicationStatus
  corrected : PublicationStatus
  expressionOfConcernPresent : PublicationStatus
  retracted : PublicationStatus
  replacedOrSuperseded : PublicationStatus

record StatusEvent : Set where
  constructor status-event
  field
    targetDOI : String
    updateDOI : String
    status : PublicationStatus
    effectiveDate : String
    sourceReceipt : String
open StatusEvent public

climateCorrectionEvent : StatusEvent
climateCorrectionEvent = status-event
  "10.1038/s41586-024-07219-0"
  "10.1038/s41586-024-07732-2"
  corrected
  "2024-06-24"
  "Nature Author Correction"

climateRetractionEvent : StatusEvent
climateRetractionEvent = status-event
  "10.1038/s41586-024-07219-0"
  "10.1038/s41586-025-09726-0"
  retracted
  "2025-12-03"
  "Nature Retraction Note"

aiEducationRetractionEvent : StatusEvent
aiEducationRetractionEvent = status-event
  "10.1057/s41599-023-01787-8"
  "10.1057/s41599-026-06602-8"
  retracted
  "2026-02-03"
  "Humanities and Social Sciences Communications Retraction Note"

------------------------------------------------------------------------
-- Regression 1: stable publication identity / DOI cannot recover current status.
------------------------------------------------------------------------

data DOIStatusCase : Set where
  sameDOIBeforeUpdate sameDOIAfterRetraction : DOIStatusCase

data DOISurface : Set where samePublicationDOI : DOISurface
data CurrentStatus : Set where historicallyPublished currentlyRetracted : CurrentStatus

doiSurface : DOIStatusCase → DOISurface
doiSurface _ = samePublicationDOI

currentStatus : DOIStatusCase → CurrentStatus
currentStatus sameDOIBeforeUpdate = historicallyPublished
currentStatus sameDOIAfterRetraction = currentlyRetracted

doiStatusDefect : INF.NonFactorabilityWitness doiSurface currentStatus
doiStatusDefect = INF.nonFactorabilityWitness
  sameDOIBeforeUpdate sameDOIAfterRetraction refl (λ ())

publicationDoiCannotFactorCurrentStatus :
  INF.FactorsThrough doiSurface currentStatus → ⊥
publicationDoiCannotFactorCurrentStatus =
  INF.witnessRulesOutEveryFlatFactorisation doiStatusDefect

------------------------------------------------------------------------
-- Regression 2: an earlier correction status cannot recover a later terminal
-- or nonterminal status.  Current-state lookup is therefore date-indexed.
------------------------------------------------------------------------

data UpdateHistoryCase : Set where
  sameEarlierCorrectionLaterStable sameEarlierCorrectionLaterRetracted : UpdateHistoryCase

data EarlierUpdateSurface : Set where sameEarlierCorrection : EarlierUpdateSurface
data LaterStatus : Set where laterStable laterRetracted : LaterStatus

earlierUpdateSurface : UpdateHistoryCase → EarlierUpdateSurface
earlierUpdateSurface _ = sameEarlierCorrection

laterStatus : UpdateHistoryCase → LaterStatus
laterStatus sameEarlierCorrectionLaterStable = laterStable
laterStatus sameEarlierCorrectionLaterRetracted = laterRetracted

updateHistoryDefect : INF.NonFactorabilityWitness earlierUpdateSurface laterStatus
updateHistoryDefect = INF.nonFactorabilityWitness
  sameEarlierCorrectionLaterStable sameEarlierCorrectionLaterRetracted refl (λ ())

earlierCorrectionCannotFactorLaterStatus :
  INF.FactorsThrough earlierUpdateSurface laterStatus → ⊥
earlierCorrectionCannotFactorLaterStatus =
  INF.witnessRulesOutEveryFlatFactorisation updateHistoryDefect

------------------------------------------------------------------------
-- Regression 3: historical citation/synthesis inclusion cannot recover whether
-- the source remains admissible/appropriately weighted under the current state.
------------------------------------------------------------------------

data DownstreamCase : Set where
  sameHistoricalCitationCurrentSource sameHistoricalCitationUpdatedSource : DownstreamCase

data HistoricalUseSurface : Set where sameHistoricalDownstreamUse : HistoricalUseSurface
data CurrentUseStatus : Set where currentUseStillPaid currentUseRequiresReaudit : CurrentUseStatus

historicalUseSurface : DownstreamCase → HistoricalUseSurface
historicalUseSurface _ = sameHistoricalDownstreamUse

currentUseStatus : DownstreamCase → CurrentUseStatus
currentUseStatus sameHistoricalCitationCurrentSource = currentUseStillPaid
currentUseStatus sameHistoricalCitationUpdatedSource = currentUseRequiresReaudit

downstreamStatusDefect : INF.NonFactorabilityWitness historicalUseSurface currentUseStatus
downstreamStatusDefect = INF.nonFactorabilityWitness
  sameHistoricalCitationCurrentSource sameHistoricalCitationUpdatedSource refl (λ ())

historicalCitationCannotFactorCurrentEvidentialUse :
  INF.FactorsThrough historicalUseSurface currentUseStatus → ⊥
historicalCitationCannotFactorCurrentEvidentialUse =
  INF.witnessRulesOutEveryFlatFactorisation downstreamStatusDefect

------------------------------------------------------------------------
-- Regression 4: retraction of one source does not determine the status of the
-- synthesis conclusion; genealogy and remaining independent evidence must be
-- re-run for the exact consumer.
------------------------------------------------------------------------

data SynthesisCase : Set where
  sameRetractedInputConclusionStillSupported sameRetractedInputConclusionUnsupported : SynthesisCase

data RetractedInputSurface : Set where sameOneInputRetracted : RetractedInputSurface
data SynthesisStatus : Set where synthesisStillSupported synthesisNoLongerSupported : SynthesisStatus

retractedInputSurface : SynthesisCase → RetractedInputSurface
retractedInputSurface _ = sameOneInputRetracted

synthesisStatus : SynthesisCase → SynthesisStatus
synthesisStatus sameRetractedInputConclusionStillSupported = synthesisStillSupported
synthesisStatus sameRetractedInputConclusionUnsupported = synthesisNoLongerSupported

retractionSynthesisDefect : INF.NonFactorabilityWitness retractedInputSurface synthesisStatus
retractionSynthesisDefect = INF.nonFactorabilityWitness
  sameRetractedInputConclusionStillSupported sameRetractedInputConclusionUnsupported refl (λ ())

oneRetractionCannotFactorSynthesisConclusion :
  INF.FactorsThrough retractedInputSurface synthesisStatus → ⊥
oneRetractionCannotFactorSynthesisConclusion =
  INF.witnessRulesOutEveryFlatFactorisation retractionSynthesisDefect

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record StatusPropagationReverseConstraint : Set where
  constructor status-propagation-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open StatusPropagationReverseConstraint public

bibliographyConstraint : StatusPropagationReverseConstraint
bibliographyConstraint = status-propagation-reverse-constraint
  "Bibliography / source identity"
  "stable DOI/work identity, version/update notice, current publication status and historical citation context remain distinct"
  false

scienceConstraint : StatusPropagationReverseConstraint
scienceConstraint = status-propagation-reverse-constraint
  "Science / evidence synthesis"
  "source inclusion, current status, affected claim scope, dependence genealogy, weighting, pooled result and conclusion remain distinct"
  false

mediaConstraint : StatusPropagationReverseConstraint
mediaConstraint = status-propagation-reverse-constraint
  "Media / fact-checking / OSINT"
  "historical article availability, correction/retraction visibility, cached copy, current publisher status and downstream repetition remain distinct"
  false

climateAiConstraint : StatusPropagationReverseConstraint
climateAiConstraint = status-propagation-reverse-constraint
  "Climate / AI / education"
  "domain claim, exact primary source, later update notice, replacement/revised work and current evidential support remain separately attributable"
  false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DOIImpliesCurrentStatus : Set where
data CorrectionIsTerminalStatus : Set where
data RetractionMakesEveryContainedClaimFalse : Set where
data RetractionMakesEveryDownstreamConclusionFalse : Set where
data CitationCountFreezesEvidenceStatus : Set where
data CrossmarkCreatesTruth : Set where
data QidCreatesCurrentStatus : Set where

doiDoesNotEncodeCurrentStatusByItself : DOIImpliesCurrentStatus → ⊥
doiDoesNotEncodeCurrentStatusByItself ()

correctionDoesNotFreezeLaterStatus : CorrectionIsTerminalStatus → ⊥
correctionDoesNotFreezeLaterStatus ()

retractionDoesNotMakeEveryContainedClaimFalse : RetractionMakesEveryContainedClaimFalse → ⊥
retractionDoesNotMakeEveryContainedClaimFalse ()

retractionDoesNotMakeEveryDownstreamConclusionFalse : RetractionMakesEveryDownstreamConclusionFalse → ⊥
retractionDoesNotMakeEveryDownstreamConclusionFalse ()

citationCountDoesNotFreezeEvidenceStatus : CitationCountFreezesEvidenceStatus → ⊥
citationCountDoesNotFreezeEvidenceStatus ()

crossmarkDoesNotCreateTruth : CrossmarkCreatesTruth → ⊥
crossmarkDoesNotCreateTruth ()

qidDoesNotCreateCurrentStatus : QidCreatesCurrentStatus → ⊥
qidDoesNotCreateCurrentStatus ()

record PostPublicationStatusPropagationBoundary : Set where
  constructor post-publication-status-propagation-boundary
  field
    qidsAndUnresolvedServiceIdentityRetained : Bool
    deweyUnresolvedStateRetained : Bool
    primaryUpdateNoticeDoisRetained : Bool
    institutionalCrossrefAndCopeSourcesRetained : Bool
    updateHistoryAppendOnly : Bool
    stableDoiSeparatedFromCurrentStatus : Bool
    earlierCorrectionSeparatedFromLaterStatus : Bool
    historicalCitationSeparatedFromCurrentUse : Bool
    retractionSeparatedFromWholeSynthesisConclusion : Bool
    atomicClaimScopeStillRequired : Bool
    sourceGenealogyReauditRequiredDownstream : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open PostPublicationStatusPropagationBoundary public

canonicalPostPublicationStatusPropagationBoundary :
  PostPublicationStatusPropagationBoundary
canonicalPostPublicationStatusPropagationBoundary =
  post-publication-status-propagation-boundary
    true true true true true true true true true true true true false
