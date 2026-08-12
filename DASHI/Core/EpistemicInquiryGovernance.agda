module DASHI.Core.EpistemicInquiryGovernance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Epistemic inquiry governance.
--
-- A participant may contribute data while having no authority over the
-- constitutive coordinates by which those data become legible.  This module
-- therefore distinguishes contribution from authority over the carrier,
-- authorised consumer family, inquiry question family, relevance assignment,
-- projection/coding frame, residuals, admissible dynamics, and revision.
--
-- SoTL / partnership references motivating the governance decomposition:
--
--   Alison Cook-Sather, Catherine Bovill, Peter Felten (2014),
--   "Engaging Students as Partners in Learning and Teaching: A Guide for
--   Faculty", Jossey-Bass.  No journal DOI is assigned to the book.
--
--   Alison Cook-Sather, Melanie Bahti, Anita Ntem (2020),
--   "Pedagogical Partnerships: A How-To Guide for Faculty, Students, and
--   Academic Developers in Higher Education", Center for Engaged Learning.
--   DOI: 10.36284/celelon.oa1.
--
--   Peter Felten, Julianne Bagg, Michael Bumbry, Jennifer Hill, Karen Hornsby,
--   Maria Pratt, Saranne Weller (2013),
--   "A call for expanding inclusive student engagement in SoTL",
--   Teaching & Learning Inquiry 1(2), 63-74.
--   DOI: 10.20343/teachlearninqu.1.2.63.
--
-- These sources motivate participation/partnership and inclusion distinctions.
-- The typed authority profile and no-promotion laws below are DASHI formal
-- constructions; they are not attributed as theorems of those papers.
------------------------------------------------------------------------

data InquiryCoordinate : Set where
  carrierCoordinate : InquiryCoordinate
  consumerCoordinate : InquiryCoordinate
  questionCoordinate : InquiryCoordinate
  relevanceCoordinate : InquiryCoordinate
  projectionCoordinate : InquiryCoordinate
  residualCoordinate : InquiryCoordinate
  dynamicsCoordinate : InquiryCoordinate
  revisionCoordinate : InquiryCoordinate

coordinateName : InquiryCoordinate → String
coordinateName carrierCoordinate = "represented carrier"
coordinateName consumerCoordinate = "authorised consumer / observer family"
coordinateName questionCoordinate = "inquiry question / task family"
coordinateName relevanceCoordinate = "relevance / interpretation assignment"
coordinateName projectionCoordinate = "projection / coding frame"
coordinateName residualCoordinate = "residual / omitted distinction"
coordinateName dynamicsCoordinate = "admissible future use / dynamics"
coordinateName revisionCoordinate = "revision / reopening"

record EpistemicGovernance (Agent : Set) : Set₁ where
  constructor epistemicGovernance
  field
    Authorised : Agent → InquiryCoordinate → Set

open EpistemicGovernance public

record ConstitutiveAccess
    {Agent : Set}
    (governance : EpistemicGovernance Agent)
    (agent : Agent)
    (coordinate : InquiryCoordinate) : Set where
  constructor constitutiveAccess
  field
    authority : Authorised governance agent coordinate
    authorityReceipt : String

open ConstitutiveAccess public

------------------------------------------------------------------------
-- Authority is not adequately represented by the number of coordinates an
-- agent touches.  Keep a coordinate-wise authority profile instead.
------------------------------------------------------------------------

data AuthorityLevel : Set where
  noAuthority : AuthorityLevel
  informed : AuthorityLevel
  respondent : AuthorityLevel
  contesting : AuthorityLevel
  coDeciding : AuthorityLevel
  governing : AuthorityLevel

record EpistemicAuthorityProfile (Agent : Set) : Set₁ where
  constructor epistemicAuthorityProfile
  field
    authorityLevel : Agent → InquiryCoordinate → AuthorityLevel

open EpistemicAuthorityProfile public

------------------------------------------------------------------------
-- Nominal authority, practical access, actual exercise and material effect are
-- four different relations.  No implication between them is built in.
------------------------------------------------------------------------

record LayeredEpistemicGovernance (Agent : Set) : Set₁ where
  constructor layeredEpistemicGovernance
  field
    profile : EpistemicAuthorityProfile Agent
    HasAuthority : Agent → InquiryCoordinate → Set
    HasAccess : Agent → InquiryCoordinate → Set
    Exercised : Agent → InquiryCoordinate → Set
    HadEffect : Agent → InquiryCoordinate → Set
    Contestable : Agent → InquiryCoordinate → Set

open LayeredEpistemicGovernance public

data AccessImpliesAuthorityPermission : Set where
data AuthorityImpliesAccessPermission : Set where
data ExerciseImpliesEffectPermission : Set where
data ExpressionImpliesAuthorityPermission : Set where

accessCannotAutomaticallyPromoteToAuthority :
  AccessImpliesAuthorityPermission → ⊥
accessCannotAutomaticallyPromoteToAuthority ()

authorityCannotAutomaticallyPromoteToAccess :
  AuthorityImpliesAccessPermission → ⊥
authorityCannotAutomaticallyPromoteToAccess ()

exerciseCannotAutomaticallyPromoteToEffect :
  ExerciseImpliesEffectPermission → ⊥
exerciseCannotAutomaticallyPromoteToEffect ()

expressionCannotAutomaticallyPromoteToAuthority :
  ExpressionImpliesAuthorityPermission → ⊥
expressionCannotAutomaticallyPromoteToAuthority ()

record RealisedConstitutiveAgency
    {Agent : Set}
    (governance : LayeredEpistemicGovernance Agent)
    (agent : Agent)
    (coordinate : InquiryCoordinate) : Set where
  constructor realisedConstitutiveAgency
  field
    legitimateAuthority : HasAuthority governance agent coordinate
    practicalAccess : HasAccess governance agent coordinate
    coordinateContestable : Contestable governance agent coordinate

open RealisedConstitutiveAgency public

record RealisedPartnershipEffect
    {Agent : Set}
    (governance : LayeredEpistemicGovernance Agent)
    (agent : Agent)
    (coordinate : InquiryCoordinate) : Set where
  constructor realisedPartnershipEffect
  field
    constitutiveAgency : RealisedConstitutiveAgency governance agent coordinate
    actuallyExercised : Exercised governance agent coordinate
    materiallyAffectedCoordinate : HadEffect governance agent coordinate

open RealisedPartnershipEffect public

------------------------------------------------------------------------
-- Voice remains separate from all constitutive authority surfaces.
------------------------------------------------------------------------

record VoiceContribution (Agent Datum : Set) : Set where
  constructor voiceContribution
  field
    contributor : Agent
    datum : Datum
    contributionReceipt : String

open VoiceContribution public

record VoiceWithoutConstitutiveAgency
    {Agent Datum : Set}
    (governance : EpistemicGovernance Agent)
    (voice : VoiceContribution Agent Datum) : Set₁ where
  constructor voiceWithoutConstitutiveAgency
  field
    noConstitutiveAccess :
      (coordinate : InquiryCoordinate) →
      Authorised governance (contributor voice) coordinate →
      ⊥

open VoiceWithoutConstitutiveAgency public

record ExtractiveInquiry
    {Agent Datum : Set}
    (governance : EpistemicGovernance Agent) : Set₁ where
  constructor extractiveInquiry
  field
    researcher participant : Agent
    participantVoice : VoiceContribution Agent Datum
    participantVoiceIsParticipant :
      contributor participantVoice ≡ participant
    researcherControlsEveryCoordinate :
      (coordinate : InquiryCoordinate) →
      Authorised governance researcher coordinate
    participantControlsNoCoordinate :
      (coordinate : InquiryCoordinate) →
      Authorised governance participant coordinate →
      ⊥

open ExtractiveInquiry public

------------------------------------------------------------------------
-- Concrete witness: voice can be present while constitutive agency is absent.
------------------------------------------------------------------------

data DemoAgent : Set where
  demoResearcher demoStudent : DemoAgent

data DemoDatum : Set where
  demoStudentFeedback : DemoDatum

data DemoAuthority : DemoAgent → InquiryCoordinate → Set where
  demoResearcherOwns :
    (coordinate : InquiryCoordinate) →
    DemoAuthority demoResearcher coordinate

canonicalDemoGovernance : EpistemicGovernance DemoAgent
canonicalDemoGovernance = epistemicGovernance DemoAuthority

canonicalDemoVoice : VoiceContribution DemoAgent DemoDatum
canonicalDemoVoice =
  voiceContribution
    demoStudent
    demoStudentFeedback
    "student contributes feedback inside an already constituted inquiry"

canonicalVoiceWithoutConstitutiveAgency :
  VoiceWithoutConstitutiveAgency canonicalDemoGovernance canonicalDemoVoice
canonicalVoiceWithoutConstitutiveAgency =
  voiceWithoutConstitutiveAgency (λ coordinate ())

canonicalExtractiveInquiry :
  ExtractiveInquiry {Datum = DemoDatum} canonicalDemoGovernance
canonicalExtractiveInquiry =
  extractiveInquiry
    demoResearcher
    demoStudent
    canonicalDemoVoice
    refl
    demoResearcherOwns
    (λ coordinate ())

voiceDoesNotManufactureConstitutiveAuthority :
  (coordinate : InquiryCoordinate) →
  Authorised canonicalDemoGovernance demoStudent coordinate →
  ⊥
voiceDoesNotManufactureConstitutiveAuthority coordinate =
  noConstitutiveAccess canonicalVoiceWithoutConstitutiveAgency coordinate
