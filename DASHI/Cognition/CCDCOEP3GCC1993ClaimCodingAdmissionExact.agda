module DASHI.Cognition.CCDCOEP3GCC1993ClaimCodingAdmissionExact where

------------------------------------------------------------------------
-- Original claim-coding evidence stages, NOT author intent or impact.
-- Source owners: Boyce Rensberger, James E. Hansen, John Shlaes/GCC.
-- DASHI owns only the typed admission and non-promotion definitions.
--
-- A catalogue description is not an independently reviewed passage.
-- A coded passage is not empirical evidence of a changed audience.
-- Missing source texts cannot be interpreted as genuine non-mentions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.CCDCOEP3GCC1993DirectionDiscriminatorExact as Direction
import DASHI.Core.DiscriminatorSynthesisExact as D

data CandidateDocument : Set where
  journalistArticle : CandidateDocument
  hansenPublishedReply : CandidateDocument
  gccJuneOriginalUnreviewed : CandidateDocument
  gccSeptemberOriginalUnreviewed : CandidateDocument

data DocumentAdmissibility : Set where
  renderedPublisherOriginal : DocumentAdmissibility
  archivedOriginalNotRead : DocumentAdmissibility

sourceAdmissibility : CandidateDocument → DocumentAdmissibility
sourceAdmissibility journalistArticle = renderedPublisherOriginal
sourceAdmissibility hansenPublishedReply = renderedPublisherOriginal
sourceAdmissibility gccJuneOriginalUnreviewed = archivedOriginalNotRead
sourceAdmissibility gccSeptemberOriginalUnreviewed = archivedOriginalNotRead

unreviewedJuneNotAdmittedAsPublisherText :
  sourceAdmissibility gccJuneOriginalUnreviewed
  ≡ renderedPublisherOriginal → ⊥
unreviewedJuneNotAdmittedAsPublisherText ()

unreviewedSeptemberNotAdmittedAsPublisherText :
  sourceAdmissibility gccSeptemberOriginalUnreviewed
  ≡ renderedPublisherOriginal → ⊥
unreviewedSeptemberNotAdmittedAsPublisherText ()

data CodedMention : Set where
  actuallyPresentInReviewedPassage : CodedMention
  explicitlyAbsentInCompleteReviewedDocument : CodedMention
  undeterminableWithoutOriginal : CodedMention

missingJuneDocument : CodedMention
missingJuneDocument = undeterminableWithoutOriginal

missingSourceNotProvedSilence :
  missingJuneDocument
  ≡ explicitlyAbsentInCompleteReviewedDocument → ⊥
missingSourceNotProvedSilence ()

data OriginalSpeaker : Set where
  newspaperReporter : OriginalSpeaker
  quotedMichaels : OriginalSpeaker
  quotedHansen : OriginalSpeaker
  independentlyAuthoredHansenRebuttal : OriginalSpeaker
  gccCommunicator : OriginalSpeaker

hansenQuotedNotIndependentHansenRebuttal :
  quotedHansen ≡ independentlyAuthoredHansenRebuttal → ⊥
hansenQuotedNotIndependentHansenRebuttal ()

data EvidenceConsumer : Set where
  sourceContent : EvidenceConsumer
  documentedSecondaryAmplification : EvidenceConsumer
  independentReaderExposure : EvidenceConsumer
  causalBeliefChange : EvidenceConsumer
  hostileIntention : EvidenceConsumer

data CurrentlyAdmittedResult : Set where
  originalNewspaperText : CurrentlyAdmittedResult
  independentlyPublishedRebuttal : CurrentlyAdmittedResult
  archivalGCCReference : CurrentlyAdmittedResult

resultConsumer : CurrentlyAdmittedResult → EvidenceConsumer
resultConsumer originalNewspaperText = sourceContent
resultConsumer independentlyPublishedRebuttal = sourceContent
resultConsumer archivalGCCReference = documentedSecondaryAmplification

archiveResultNotExposure :
  resultConsumer archivalGCCReference ≡ independentReaderExposure → ⊥
archiveResultNotExposure ()

publishedTextNotAudienceEffect :
  resultConsumer originalNewspaperText ≡ causalBeliefChange → ⊥
publishedTextNotAudienceEffect ()

secondaryAmplificationNotHostilePurpose :
  resultConsumer archivalGCCReference ≡ hostileIntention → ⊥
secondaryAmplificationNotHostilePurpose ()

-- Having a suitable original passage source is necessary but insufficient:
-- the human reviewing, source-span, full item denominator and coder
-- disagreement must be supported by independent records before
-- consuming a claim-level observational result.
