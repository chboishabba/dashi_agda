module DASHI.Cognition.CCDCOEP3G20COP21AttributionExact where

------------------------------------------------------------------------
-- Original source-owner: DASHI G20/COP21 institutional comparison.
-- External historical/legal source authors RETAIN original authorship.
--
-- G20 Brisbane leaders, 2014-11-16, communique paragraph 19;
-- G20 Antalya leaders, 2015-11-16, communique paragraph 24;
-- UNFCCC COP21 Parties, 2015-12-12, decision 1/CP.21 and treaty;
-- G20 Hamburg, 2017-07-08, US position AND other leaders' position;
-- C20 Turkey, 2015-09-16, civil-society recommendation;
-- B20 Turkey, 2015, business recommendations (index located).
--
-- Original external statements are DOCUMENTARY facts, not theorem
-- assertions by their authors. Original mathematical proof owner:
-- DASHI.Core.IntersectionalNonFactorability. This file instantiates
-- that existing generic factorisation result and does not claim its
-- mathematical novelty, journal authors' endorsement, or original
-- authorship of summits, negotiations, treaties or submitted briefs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.DiscriminatorSynthesisExact as D

data OriginalDocument : Set where
  brisbane2014 : OriginalDocument
  antalya2015 : OriginalDocument
  parisDecision2015 : OriginalDocument
  parisArticle4 : OriginalDocument
  hamburgUS2017 : OriginalDocument
  hamburgOtherLeaders2017 : OriginalDocument
  c20Turkey2015 : OriginalDocument
  b20Turkey2015 : OriginalDocument
  harrisonAgencyHistory : OriginalDocument

data InstitutionalVoice : Set where
  collectiveG20Leaders : InstitutionalVoice
  unFCCCParties : InstitutionalVoice
  hamburgUnitedStates : InstitutionalVoice
  hamburgOtherG20Leaders : InstitutionalVoice
  civilSocietyC20 : InstitutionalVoice
  businessB20 : InstitutionalVoice
  prCompanyOwnAccount : InstitutionalVoice

speaker : OriginalDocument → InstitutionalVoice
speaker brisbane2014 = collectiveG20Leaders
speaker antalya2015 = collectiveG20Leaders
speaker parisDecision2015 = unFCCCParties
speaker parisArticle4 = unFCCCParties
speaker hamburgUS2017 = hamburgUnitedStates
speaker hamburgOtherLeaders2017 = hamburgOtherG20Leaders
speaker c20Turkey2015 = civilSocietyC20
speaker b20Turkey2015 = businessB20
speaker harrisonAgencyHistory = prCompanyOwnAccount

data SourceSpeechAct : Set where
  summitCommunique : SourceSpeechAct
  copDecision : SourceSpeechAct
  treatyObligation : SourceSpeechAct
  recordedDissent : SourceSpeechAct
  civilSocietyRecommendation : SourceSpeechAct
  businessRecommendation : SourceSpeechAct
  agencySelfAssessment : SourceSpeechAct

speechAct : OriginalDocument → SourceSpeechAct
speechAct brisbane2014 = summitCommunique
speechAct antalya2015 = summitCommunique
speechAct parisDecision2015 = copDecision
speechAct parisArticle4 = treatyObligation
speechAct hamburgUS2017 = recordedDissent
speechAct hamburgOtherLeaders2017 = summitCommunique
speechAct c20Turkey2015 = civilSocietyRecommendation
speechAct b20Turkey2015 = businessRecommendation
speechAct harrisonAgencyHistory = agencySelfAssessment

data Question : Set where
  economicAndClimateWording : Question
  legalCommitment : Question
  stakeholderProposal : Question
  sourceTransmission : Question
  realWorldEffect : Question

data StatementStrength : Set where
  publishedWording : StatementStrength
  recordedInstitutionalPosition : StatementStrength
  formalTreatyRule : StatementStrength
  stakeholderSubmissionOnly : StatementStrength
  agencyClaimOnly : StatementStrength
  attributionNotEstablished : StatementStrength

strength : OriginalDocument → StatementStrength
strength brisbane2014 = recordedInstitutionalPosition
strength antalya2015 = recordedInstitutionalPosition
strength parisDecision2015 = recordedInstitutionalPosition
strength parisArticle4 = formalTreatyRule
strength hamburgUS2017 = recordedInstitutionalPosition
strength hamburgOtherLeaders2017 = recordedInstitutionalPosition
strength c20Turkey2015 = stakeholderSubmissionOnly
strength b20Turkey2015 = stakeholderSubmissionOnly
strength harrisonAgencyHistory = agencyClaimOnly

-- The same summit includes an explicitly attributed US decision and
-- a different position explicitly attributed to other G20 leaders.
-- Flattening both to "G20 2017 climate language" loses this fact.
data BroadClimateTopic : Set where
  climateStatement : BroadClimateTopic

flattenTopic : OriginalDocument → BroadClimateTopic
flattenTopic _ = climateStatement

hamburgDistinctVoices :
  speaker hamburgUS2017 ≡ speaker hamburgOtherLeaders2017 → ⊥
hamburgDistinctVoices ()

hamburgAttributionCannotFactorThroughTopic :
  NF.FactorsThrough flattenTopic speaker → ⊥
hamburgAttributionCannotFactorThroughTopic =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      hamburgUS2017 hamburgOtherLeaders2017 refl hamburgDistinctVoices)

civilSocietyNotLeaders :
  speaker c20Turkey2015 ≡ speaker antalya2015 → ⊥
civilSocietyNotLeaders ()

stakeholderVoiceNotG20Voice :
  NF.FactorsThrough flattenTopic speaker → ⊥
stakeholderVoiceNotG20Voice =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      c20Turkey2015 antalya2015 refl civilSocietyNotLeaders)

treatyObligationNotRecommendation :
  speechAct parisArticle4 ≡ speechAct c20Turkey2015 → ⊥
treatyObligationNotRecommendation ()

legalSpeechActCannotFactorThroughTopic :
  NF.FactorsThrough flattenTopic speechAct → ⊥
legalSpeechActCannotFactorThroughTopic =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      parisArticle4 c20Turkey2015 refl treatyObligationNotRecommendation)

sameThemeNotAgencyEffect :
  strength harrisonAgencyHistory ≡ strength parisArticle4 → ⊥
sameThemeNotAgencyEffect ()

agencySelfAssessmentNotTreatyAuthority :
  NF.FactorsThrough flattenTopic strength → ⊥
agencySelfAssessmentNotTreatyAuthority =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      harrisonAgencyHistory parisArticle4 refl sameThemeNotAgencyEffect)

institutionalVoiceProbe : D.ExperimentBundle OriginalDocument
institutionalVoiceProbe =
  D.experimentBundle
    InstitutionalVoice speaker 1
    "Inspect exact author, adopted institution, and named excluded speaker"
    "Documentary speaker verification, not authorship or influence transport"

hamburgSpeakerSeparation :
  D.BundleSeparates institutionalVoiceProbe
    hamburgUS2017 hamburgOtherLeaders2017
hamburgSpeakerSeparation = D.bundleSeparates hamburgDistinctVoices

hamburgVoiceRefinement :
  D.DiscriminatingLanguageExtension flattenTopic
hamburgVoiceRefinement =
  D.discriminatingLanguageExtension
    (D.currentObserverCollision
      hamburgUS2017 hamburgOtherLeaders2017 refl)
    institutionalVoiceProbe hamburgSpeakerSeparation

-- No source-approved GCC -> G20 or B20/C20 -> Leaders causal edge has
-- been admitted. A genuine transfer requires independently reviewed
-- same-actor, dated document/trail, receipt and policy-decision link.
data SameObjectTransmissionReceipt : Set where

noAutomaticIndustryToSummitTransmission :
  SameObjectTransmissionReceipt → ⊥
noAutomaticIndustryToSummitTransmission ()

data SourceAcceptance : Set where
  sourceLocated : SourceAcceptance
  originalBytesReviewed : SourceAcceptance
  sourceAuthorIdentified : SourceAcceptance
  sameObjectCausalityAudited : SourceAcceptance

record InstitutionallyScopedSource : Set where
  constructor institutionallyScopedSource
  field
    originalAuthorDescription : String
    originalSourceURL : String
    datedSourceEvent : String
    originalSourceStatus : SourceAcceptance
    externalAuthorsEndorseDASHI : Bool
    sourceBytesHashReviewed : Bool
    specificActorDecisionTrailReviewed : Bool

brisbaneSource : InstitutionallyScopedSource
brisbaneSource =
  institutionallyScopedSource
    "G20 leaders, Brisbane, paragraph 19"
    "https://g20.utoronto.ca/2014/2014-1116-communique.html"
    "2014-11-16" sourceLocated false false false

hamburgSource : InstitutionallyScopedSource
hamburgSource =
  institutionallyScopedSource
    "G20 leaders, Hamburg, separately named US and other members"
    "https://g20.utoronto.ca/2017/2017-G20-leaders-declaration.html"
    "2017-07-08" sourceLocated false false false

noEndorsementFromQuotation :
  InstitutionallyScopedSource.externalAuthorsEndorseDASHI
    hamburgSource ≡ false
noEndorsementFromQuotation = refl

noActorTransmissionFromSharedLanguage :
  InstitutionallyScopedSource.specificActorDecisionTrailReviewed
    brisbaneSource ≡ false
noActorTransmissionFromSharedLanguage = refl
