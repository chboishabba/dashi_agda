module DASHI.Cognition.PNF.SensibLawGenreSubjectDemandOrthogonalityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact as Consumer
import DASHI.Cognition.PNF.SensibLawDocumentDiscourseContextRefinementExact as Context

------------------------------------------------------------------------
-- ORTHOGONAL TEXT CONTEXT
--
-- What a text IS, what it is ABOUT, and what a consumer wants FROM it are
-- separate coordinates over one semantic carrier. None determines the others.
------------------------------------------------------------------------

data TextGenre : Set where
  casualConversation
  transcript
  educationalLecture
  academicDiscussion
  newsReport
  narrativeText
  institutionalDocument
  formalLegalDocument
  unresolvedGenre
  customGenre : String → TextGenre

data SubjectMatter : Set where
  legalSubject
  historicalSubject
  culturalSubject
  politicalSubject
  scientificSubject
  personalSubject
  institutionalSubject
  generalSubject
  customSubject : String → SubjectMatter

record TextContextProfile : Set where
  constructor textContextProfile
  field
    genre : TextGenre
    subjectMatters : List SubjectMatter
    consumerDemand : Consumer.ConsumerDemandProfile
    genreEvidenceReferences : List String
    subjectEvidenceReferences : List String
    contextReference : String

open TextContextProfile public

------------------------------------------------------------------------
-- Same discourse carrier, many contextual readings.
------------------------------------------------------------------------

record ContextualisedDiscourse
    (candidate : Consumer.DiscourseActCandidate)
    (general : Consumer.GeneralDiscourseResolution candidate)
    (profile : TextContextProfile) : Set where
  constructor contextualisedDiscourse
  field
    interpretation :
      Consumer.MultiConsumerDiscourseInterpretation
        candidate general (consumerDemand profile)
    underlyingCandidateSame :
      Consumer.underlyingCandidate interpretation ≡ candidate
    parserRewrittenByGenre : Bool
    parserRewrittenByGenreIsFalse : parserRewrittenByGenre ≡ false
    parserRewrittenBySubjectMatter : Bool
    parserRewrittenBySubjectMatterIsFalse : parserRewrittenBySubjectMatter ≡ false

open ContextualisedDiscourse public

contextualise :
  {candidate : Consumer.DiscourseActCandidate} →
  (general : Consumer.GeneralDiscourseResolution candidate) →
  (profile : TextContextProfile) →
  ContextualisedDiscourse candidate general profile
contextualise {candidate} general profile =
  contextualisedDiscourse
    (Consumer.interpretForDemand general (consumerDemand profile))
    refl
    false refl
    false refl

------------------------------------------------------------------------
-- Canonical mixed-domain examples.
------------------------------------------------------------------------

casualLegalCaseTranscript : Consumer.ConsumerDemandProfile → TextContextProfile
casualLegalCaseTranscript demand =
  textContextProfile
    transcript
    (legalSubject ∷ historicalSubject ∷ culturalSubject ∷ [])
    demand
    ("container evidence: informal/casual transcript" ∷ [])
    ( "discussion concerns a legal case"
    ∷ "discussion may recount historical context"
    ∷ "discussion may analyse cultural effects"
    ∷ [])
    "casual transcript discussing a case; subject matter is not genre"

lawSchoolLecture : Context.DocumentDiscourseFrame → TextContextProfile
lawSchoolLecture frame =
  textContextProfile
    educationalLecture
    (legalSubject ∷ historicalSubject ∷ culturalSubject ∷ [])
    (Consumer.lawSchoolCaseDemand frame)
    ("container evidence: teaching/lecture context" ∷ [])
    ("legal doctrine" ∷ "case history" ∷ "cultural context" ∷ [])
    "law-school lecture may support several simultaneous consumer projections"

------------------------------------------------------------------------
-- Quoted/reported legal material does not inherit source authority merely
-- because the subject matter is legal.
------------------------------------------------------------------------

data ReportedAuthorityStatus : Set where
  authorityUnresolved
  attributedExternalAuthority
  governedAuthorityVerified
  : ReportedAuthorityStatus

record NestedReportedSource : Set where
  constructor nestedReportedSource
  field
    currentDiscourseSourceReference : String
    reportedSourceReference : String
    embeddedPropositionReference : String
    externalAuthorityReference : String
    authorityStatus : ReportedAuthorityStatus

open NestedReportedSource public

casualReportedFinding : NestedReportedSource
casualReportedFinding =
  nestedReportedSource
    "speaker:casual-transcript"
    "reported-source:judge"
    "proposition:reported-finding"
    "external-authority:unresolved"
    authorityUnresolved

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data GenreDeterminesSubjectMatter : Set where
data SubjectMatterDeterminesGenre : Set where
data SubjectMatterDeterminesConsumerDemand : Set where
data ConsumerDemandDeterminesGenre : Set where
data LegalSubjectMeansFormalLegalDocument : Set where
data QuotedFindingIsCourtFinding : Set where
data EducationalLegalDiscussionIsLegalSubmission : Set where

genreDoesNotDetermineSubjectMatter : GenreDeterminesSubjectMatter → ⊥
genreDoesNotDetermineSubjectMatter ()

subjectMatterDoesNotDetermineGenre : SubjectMatterDeterminesGenre → ⊥
subjectMatterDoesNotDetermineGenre ()

subjectMatterDoesNotDetermineConsumerDemand :
  SubjectMatterDeterminesConsumerDemand → ⊥
subjectMatterDoesNotDetermineConsumerDemand ()

consumerDemandDoesNotDetermineGenre : ConsumerDemandDeterminesGenre → ⊥
consumerDemandDoesNotDetermineGenre ()

legalSubjectDoesNotMakeFormalLegalDocument :
  LegalSubjectMeansFormalLegalDocument → ⊥
legalSubjectDoesNotMakeFormalLegalDocument ()

quotedFindingDoesNotBecomeCourtFinding : QuotedFindingIsCourtFinding → ⊥
quotedFindingDoesNotBecomeCourtFinding ()

lawSchoolDiscussionDoesNotBecomeSubmission :
  EducationalLegalDiscussionIsLegalSubmission → ⊥
lawSchoolDiscussionDoesNotBecomeSubmission ()
