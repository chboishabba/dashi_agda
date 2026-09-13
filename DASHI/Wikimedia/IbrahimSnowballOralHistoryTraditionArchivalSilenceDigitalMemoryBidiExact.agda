module DASHI.Wikimedia.IbrahimSnowballOralHistoryTraditionArchivalSilenceDigitalMemoryBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballSourceMonitoringCollectiveMemoryEpistemicInjusticeBidiExact as Collective
import DASHI.Wikimedia.IbrahimSnowballArchiveHistoriographyCausalityBidiExact as Archive
import DASHI.Wikimedia.IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact as Testimony

------------------------------------------------------------------------
-- IBRAHIM / ORAL-HISTORY / ORAL-TRADITION / ARCHIVAL-SILENCE / DIGITAL-MEMORY BIDI
--
-- Oral history as a discipline, an oral-history interview/record, oral tradition,
-- archive survival, archival silence, forgetting and platform visibility are
-- different carriers.  This owner keeps participant meaning and historically
-- excluded voices recoverable without promoting any narrative directly to
-- event truth; archive absence likewise cannot prove historical absence.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim oral-history/tradition/archival-silence/digital-memory BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create historical truth, archive completeness, source independence, representativeness or collective importance")

oralHistoryDisciplineQid : Identity.ExternalIdentityDemand
oralHistoryDisciplineQid = mkQid "oral history (discipline)" "Q558929"

oralHistoryRecordQid : Identity.ExternalIdentityDemand
oralHistoryRecordQid = mkQid "oral history interview/record" "Q106813818"

oralTraditionQid : Identity.ExternalIdentityDemand
oralTraditionQid = mkQid "oral tradition" "Q209815"

collectiveMemoryQid : Identity.ExternalIdentityDemand
collectiveMemoryQid = Collective.collectiveMemoryQid

forgettingQid : Identity.ExternalIdentityDemand
forgettingQid = mkQid "forgetting" "Q1377840"

archivalSilenceQid : Identity.ExternalIdentityDemand
archivalSilenceQid = Identity.mkOptionalIdentityDemand
  "Ibrahim oral-history/tradition/archival-silence/digital-memory BIDI"
  "external concept identity"
  "archival silence"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact standalone QID promoted in this pass; concept is source-paid through archival/history scholarship")

algorithmicMemoryCurationQid : Identity.ExternalIdentityDemand
algorithmicMemoryCurationQid = Identity.mkOptionalIdentityDemand
  "Ibrahim oral-history/tradition/archival-silence/digital-memory BIDI"
  "external concept identity"
  "algorithmic curation of collective/digital memory"
  Identity.wikidataQid
  (Identity.unresolved
    "no single exact QID promoted; platformization, recommendation, ranking and collective-memory processes remain distinct")

------------------------------------------------------------------------
-- Dewey remains explicit and unresolved unless an exact DDC statement is paid.
------------------------------------------------------------------------

oralHistoryDewey : Dewey.DeweyCoordinate
oralHistoryDewey = Dewey.mkUnresolvedDewey
  "oral history"
  "no exact inspected DDC value promoted in this pass"

oralTraditionDewey : Dewey.DeweyCoordinate
oralTraditionDewey = Dewey.mkUnresolvedDewey
  "oral tradition"
  "no exact inspected DDC value promoted in this pass"

archivalSilenceDewey : Dewey.DeweyCoordinate
archivalSilenceDewey = Dewey.mkUnresolvedDewey
  "archival silence"
  "no exact inspected DDC value promoted in this pass"

------------------------------------------------------------------------
-- DOI/source line.
------------------------------------------------------------------------

thomsonOralMemorySource : Attribution.AttributedSource
thomsonOralMemorySource = Attribution.mkDOISource
  "Alistair Thomson"
  "Memory and Remembering in Oral History"
  "The Oxford Handbook of Oral History"
  "2012"
  "10.1093/oxfordhb/9780195339550.013.0006"
  "https://doi.org/10.1093/oxfordhb/9780195339550.013.0006"
  Attribution.academicChapterSource
  "oral-history memory/remembering methodology; remembering is an active meaning-making process and interview evidence requires interpretation rather than tape-recorder realism"
  Attribution.publicAttribution

olsonArchivalSilenceSource : Attribution.AttributedSource
olsonArchivalSilenceSource = Attribution.mkDOISource
  "Kevin Olson"
  "Archival Silence: How Do We Write the History of the Subaltern Who Cannot Speak?"
  "PS: Political Science & Politics 57(1), 92-94"
  "2024"
  "10.1017/S1049096523000525"
  "https://doi.org/10.1017/S1049096523000525"
  Attribution.academicArticleSource
  "source-bounded discussion of archival silence and subaltern historical reconstruction; archive absence is not promoted to historical absence"
  Attribution.publicAttribution

adriaansenSmitDigitalMemorySource : Attribution.AttributedSource
adriaansenSmitDigitalMemorySource = Attribution.mkDOISource
  "Robbert-Jan Adriaansen; Rik Smit"
  "Collective memory and social media"
  "Current Opinion in Psychology 65, 102077"
  "2025"
  "10.1016/j.copsyc.2025.102077"
  "https://doi.org/10.1016/j.copsyc.2025.102077"
  Attribution.academicArticleSource
  "review of platformization, algorithmic curation and changing collective-memory practices; platform salience is not identified with historical importance or social consensus"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Reuse upstream exact boundaries.
------------------------------------------------------------------------

collectiveBoundary : Collective.SourceMonitoringCollectiveMemoryEpistemicInjusticeBoundary
collectiveBoundary = Collective.canonicalSourceMonitoringCollectiveMemoryEpistemicInjusticeBoundary

archiveBoundary : Archive.ArchiveHistoriographyCausalityBoundary
archiveBoundary = Archive.canonicalArchiveHistoriographyCausalityBoundary

testimonyBoundary : Testimony.TestimonyMemoryCredibilityBoundary
testimonyBoundary = Testimony.canonicalTestimonyMemoryCredibilityBoundary

------------------------------------------------------------------------
-- Regression 1: same lexical label "oral history" cannot recover whether the
-- object is a discipline/method or an interview/record manifestation.
------------------------------------------------------------------------

data OralHistoryLabelCase : Set where
  oralHistoryAsDiscipline oralHistoryAsRecord : OralHistoryLabelCase

data OralHistoryLabelSurface : Set where sameOralHistoryLabel : OralHistoryLabelSurface
data OralHistoryRole : Set where disciplineRole recordRole : OralHistoryRole

oralHistoryLabelSurface : OralHistoryLabelCase → OralHistoryLabelSurface
oralHistoryLabelSurface _ = sameOralHistoryLabel

oralHistoryRole : OralHistoryLabelCase → OralHistoryRole
oralHistoryRole oralHistoryAsDiscipline = disciplineRole
oralHistoryRole oralHistoryAsRecord = recordRole

oralHistoryRoleDefect : INF.NonFactorabilityWitness oralHistoryLabelSurface oralHistoryRole
oralHistoryRoleDefect = INF.nonFactorabilityWitness
  oralHistoryAsDiscipline oralHistoryAsRecord refl (λ ())

oralHistoryLabelCannotFactorRole :
  INF.FactorsThrough oralHistoryLabelSurface oralHistoryRole → ⊥
oralHistoryLabelCannotFactorRole =
  INF.witnessRulesOutEveryFlatFactorisation oralHistoryRoleDefect

------------------------------------------------------------------------
-- Regression 2: archive absence/silence cannot recover the cause of absence.
------------------------------------------------------------------------

data ArchiveGapCase : Set where
  sameArchiveGapNoRecordProduced sameArchiveGapRecordExcludedOrLost : ArchiveGapCase

data ArchiveGapSurface : Set where sameObservedArchiveGap : ArchiveGapSurface
data GapGenealogy : Set where noRecordProduced recordExcludedOrLost : GapGenealogy

archiveGapSurface : ArchiveGapCase → ArchiveGapSurface
archiveGapSurface _ = sameObservedArchiveGap

gapGenealogy : ArchiveGapCase → GapGenealogy
gapGenealogy sameArchiveGapNoRecordProduced = noRecordProduced
gapGenealogy sameArchiveGapRecordExcludedOrLost = recordExcludedOrLost

archiveGapDefect : INF.NonFactorabilityWitness archiveGapSurface gapGenealogy
archiveGapDefect = INF.nonFactorabilityWitness
  sameArchiveGapNoRecordProduced sameArchiveGapRecordExcludedOrLost refl (λ ())

archiveSilenceCannotFactorGapGenealogy :
  INF.FactorsThrough archiveGapSurface gapGenealogy → ⊥
archiveSilenceCannotFactorGapGenealogy =
  INF.witnessRulesOutEveryFlatFactorisation archiveGapDefect

------------------------------------------------------------------------
-- Regression 3: oral transmission/tradition cannot recover proposition truth.
------------------------------------------------------------------------

data OralTraditionCase : Set where
  sameTraditionHistoricallySupported sameTraditionHistoricallyOpen : OralTraditionCase

data OralTraditionSurface : Set where sameOralTraditionStatus : OralTraditionSurface
data HistoricalSupport : Set where historicalSupportPaid historicalSupportOpen : HistoricalSupport

oralTraditionSurface : OralTraditionCase → OralTraditionSurface
oralTraditionSurface _ = sameOralTraditionStatus

historicalSupport : OralTraditionCase → HistoricalSupport
historicalSupport sameTraditionHistoricallySupported = historicalSupportPaid
historicalSupport sameTraditionHistoricallyOpen = historicalSupportOpen

oralTraditionTruthDefect : INF.NonFactorabilityWitness oralTraditionSurface historicalSupport
oralTraditionTruthDefect = INF.nonFactorabilityWitness
  sameTraditionHistoricallySupported sameTraditionHistoricallyOpen refl (λ ())

oralTraditionCannotFactorHistoricalTruth :
  INF.FactorsThrough oralTraditionSurface historicalSupport → ⊥
oralTraditionCannotFactorHistoricalTruth =
  INF.witnessRulesOutEveryFlatFactorisation oralTraditionTruthDefect

------------------------------------------------------------------------
-- Regression 4: platform visibility cannot recover social/historical importance.
------------------------------------------------------------------------

data DigitalMemoryCase : Set where
  sameVisibilityAlgorithmicAmplification sameVisibilityBroadIndependentCommemoration : DigitalMemoryCase

data PlatformVisibilitySurface : Set where samePlatformVisibility : PlatformVisibilitySurface
data VisibilityGenealogy : Set where algorithmicAmplification broadIndependentCommemoration : VisibilityGenealogy

platformVisibilitySurface : DigitalMemoryCase → PlatformVisibilitySurface
platformVisibilitySurface _ = samePlatformVisibility

visibilityGenealogy : DigitalMemoryCase → VisibilityGenealogy
visibilityGenealogy sameVisibilityAlgorithmicAmplification = algorithmicAmplification
visibilityGenealogy sameVisibilityBroadIndependentCommemoration = broadIndependentCommemoration

platformVisibilityDefect : INF.NonFactorabilityWitness platformVisibilitySurface visibilityGenealogy
platformVisibilityDefect = INF.nonFactorabilityWitness
  sameVisibilityAlgorithmicAmplification sameVisibilityBroadIndependentCommemoration refl (λ ())

platformVisibilityCannotFactorMemoryGenealogy :
  INF.FactorsThrough platformVisibilitySurface visibilityGenealogy → ⊥
platformVisibilityCannotFactorMemoryGenealogy =
  INF.witnessRulesOutEveryFlatFactorisation platformVisibilityDefect

------------------------------------------------------------------------
-- Regression 5: non-recall/forgetting surface cannot recover historical or
-- mnemonic origin of the absence.
------------------------------------------------------------------------

data ForgettingCase : Set where
  sameNonRecallRetrievalFailure sameNonRecallNeverEncoded : ForgettingCase

data NonRecallSurface : Set where sameNonRecall : NonRecallSurface
data NonRecallGenealogy : Set where retrievalFailure neverEncoded : NonRecallGenealogy

nonRecallSurface : ForgettingCase → NonRecallSurface
nonRecallSurface _ = sameNonRecall

nonRecallGenealogy : ForgettingCase → NonRecallGenealogy
nonRecallGenealogy sameNonRecallRetrievalFailure = retrievalFailure
nonRecallGenealogy sameNonRecallNeverEncoded = neverEncoded

forgettingDefect : INF.NonFactorabilityWitness nonRecallSurface nonRecallGenealogy
forgettingDefect = INF.nonFactorabilityWitness
  sameNonRecallRetrievalFailure sameNonRecallNeverEncoded refl (λ ())

nonRecallCannotFactorMemoryGenealogy :
  INF.FactorsThrough nonRecallSurface nonRecallGenealogy → ⊥
nonRecallCannotFactorMemoryGenealogy =
  INF.witnessRulesOutEveryFlatFactorisation forgettingDefect

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record OralArchiveDigitalReverseConstraint : Set where
  constructor oral-archive-digital-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open OralArchiveDigitalReverseConstraint public

historyConstraint : OralArchiveDigitalReverseConstraint
historyConstraint = oral-archive-digital-reverse-constraint
  "History / historiography"
  "event, participant recollection, interview cocreation, oral record, archive custody, archival absence and later interpretation remain distinct"
  false

cultureConstraint : OralArchiveDigitalReverseConstraint
cultureConstraint = oral-archive-digital-reverse-constraint
  "Culture / oral tradition / collective memory"
  "transmission, mnemonic practice, social identity, member-level memory, source genealogy and proposition truth remain distinct"
  false

epistemicJusticeConstraint : OralArchiveDigitalReverseConstraint
epistemicJusticeConstraint = oral-archive-digital-reverse-constraint
  "Epistemic justice / archives"
  "lack of surviving institutional record cannot erase participant knowledge or establish that an excluded voice/event was absent"
  false

mediaConstraint : OralArchiveDigitalReverseConstraint
mediaConstraint = oral-archive-digital-reverse-constraint
  "Media / digital collective memory"
  "platform visibility, ranking/curation, repetition, independent commemoration, collective salience and historical importance remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data OralHistoryLabelCreatesRole : Set where
data ArchiveSilenceMeansHistoricalAbsence : Set where
data OralTraditionMeansHistoricalTruth : Set where
data PlatformVisibilityMeansCollectiveImportance : Set where
data ForgettingMeansNeverEncoded : Set where
data OralHistoryQidMeansRecordTruth : Set where

oralHistoryLabelDoesNotCreateRole : OralHistoryLabelCreatesRole → ⊥
oralHistoryLabelDoesNotCreateRole ()

archiveSilenceDoesNotCreateHistoricalAbsence : ArchiveSilenceMeansHistoricalAbsence → ⊥
archiveSilenceDoesNotCreateHistoricalAbsence ()

oralTraditionDoesNotCreateHistoricalTruth : OralTraditionMeansHistoricalTruth → ⊥
oralTraditionDoesNotCreateHistoricalTruth ()

platformVisibilityDoesNotCreateCollectiveImportance : PlatformVisibilityMeansCollectiveImportance → ⊥
platformVisibilityDoesNotCreateCollectiveImportance ()

forgettingDoesNotMeanNeverEncoded : ForgettingMeansNeverEncoded → ⊥
forgettingDoesNotMeanNeverEncoded ()

oralHistoryQidDoesNotCreateRecordTruth : OralHistoryQidMeansRecordTruth → ⊥
oralHistoryQidDoesNotCreateRecordTruth ()

record OralHistoryTraditionArchivalSilenceDigitalMemoryBoundary : Set where
  constructor oral-history-tradition-archival-silence-digital-memory-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    disciplineAndRecordQidsKeptDistinct : Bool
    unresolvedArchivalSilenceQidRetained : Bool
    deweyUnresolvedRetainedExplicitly : Bool
    doiAndSourceRoleRetained : Bool
    oralHistoryLabelSeparatedFromRole : Bool
    archiveSilenceSeparatedFromGapCause : Bool
    oralTraditionSeparatedFromHistoricalTruth : Bool
    platformVisibilitySeparatedFromMemoryGenealogy : Bool
    forgettingSeparatedFromNeverEncoding : Bool
    epistemicJusticeAndArchiveBoundariesCrossPollinated : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open OralHistoryTraditionArchivalSilenceDigitalMemoryBoundary public

canonicalOralHistoryTraditionArchivalSilenceDigitalMemoryBoundary :
  OralHistoryTraditionArchivalSilenceDigitalMemoryBoundary
canonicalOralHistoryTraditionArchivalSilenceDigitalMemoryBoundary =
  oral-history-tradition-archival-silence-digital-memory-boundary
    true true true true true true true true true true true true false
