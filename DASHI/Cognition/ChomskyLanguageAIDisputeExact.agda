module DASHI.Cognition.ChomskyLanguageAIDisputeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.ConsentDistrustDualityExact as Media

------------------------------------------------------------------------
-- CHOMSKY: LINGUISTIC CLAIMS, MEDIA PRIOR ART, AND AI-ERA EMPIRICAL PRESSURE
--
-- Existing repo prior art already attributes the institutional-media vocabulary
-- to Herman & Chomsky, Manufacturing Consent (1988), via
-- ConsentDistrustDualityExact.  This owner adds a separate linguistic dispute;
-- political-media and linguistic claims are not fused merely because they share
-- an author.
------------------------------------------------------------------------

data ChomskyThesis : Set where
  generativeCapacity : ChomskyThesis
  competencePerformanceDistinction : ChomskyThesis
  povertyOfStimulus : ChomskyThesis
  languageSpecificInnateConstraint : ChomskyThesis
  internalLanguageArchitecture : ChomskyThesis

data EvidenceDirection : Set where
  supports : EvidenceDirection
  challenges : EvidenceDirection
  mixed : EvidenceDirection
  orthogonal : EvidenceDirection

data AISource : Set where
  openMind2024Limitations : AISource
  haleStanojevic2024Universal : AISource
  pistottiBrownWitbrock2025Gaps : AISource
  poshBench2026 : AISource
  hwang2026CognitiveModel : AISource

record LinguisticEvidenceReceipt : Set where
  constructor linguistic-evidence-receipt
  field
    source : AISource
    target : ChomskyThesis
    direction : EvidenceDirection
    boundedFinding : String
    refutesWholeFramework : Bool
open LinguisticEvidenceReceipt public

poshBenchReceipt : LinguisticEvidenceReceipt
poshBenchReceipt = linguistic-evidence-receipt
  poshBench2026
  povertyOfStimulus
  challenges
  "Transformers trained on developmentally plausible 10-50M-word corpora showed some generalisation on classic poverty-of-stimulus phenomena without direct positive evidence, but remained weaker and less data-efficient than children."
  false

poshBenchInnatenessReceipt : LinguisticEvidenceReceipt
poshBenchInnatenessReceipt = linguistic-evidence-receipt
  poshBench2026
  languageSpecificInnateConstraint
  challenges
  "The result challenges the claim that language-specific innate syntax is the only possible route to the tested generalisations; it does not show that human learners lack inductive biases or innate structure."
  false

hwangReceipt : LinguisticEvidenceReceipt
hwangReceipt = linguistic-evidence-receipt
  hwang2026CognitiveModel
  competencePerformanceDistinction
  supports
  "Across grammaticality and interpretation tasks, current LLMs showed failures on infrequent silent-structure phenomena and did not provide a convincing human cognitive model merely by scaling or adding reasoning capability."
  false

haleStanojevicReceipt : LinguisticEvidenceReceipt
haleStanojevicReceipt = linguistic-evidence-receipt
  haleStanojevic2024Universal
  languageSpecificInnateConstraint
  mixed
  "A multilingual model respected a proposed syntactic universal in several higher-resource languages but not uniformly across languages, suggesting learned structural generalisation plus residual need for bias/data explanations."
  false

pistottiReceipt : LinguisticEvidenceReceipt
pistottiReceipt = linguistic-evidence-receipt
  pistottiBrownWitbrock2025Gaps
  povertyOfStimulus
  challenges
  "Refined minimal-pair evaluation found stronger GPT-2 filler-gap/parasitic-gap generalisation than earlier metrics suggested, showing that evaluation design materially affects claims about syntactic competence."
  false

------------------------------------------------------------------------
-- Compact statement of what survives the AI-era comparison.
------------------------------------------------------------------------

record ChomskyAIStatus : Set where
  constructor chomsky-ai-status
  field
    finiteDataCanSupportUnexpectedGeneralisation : Bool
    innateSyntaxOnlyRouteChallenged : Bool
    humanLikeDataEfficiencyReached : Bool
    llmOutputEquatesHumanMechanism : Bool
    competenceMechanismDistinctionStillLive : Bool
    povertyOfStimulusDebateClosed : Bool
open ChomskyAIStatus public

currentChomskyAIStatus : ChomskyAIStatus
currentChomskyAIStatus = chomsky-ai-status
  true true false false true false

------------------------------------------------------------------------
-- EPSTEIN-CORPUS ATTRIBUTION BOUNDARY.
--
-- EFTA02458524 places Chomsky in Bach's proposed invitee list alongside Doblin
-- and others.  A proposed-list mention is retained only as proposal exposure.
------------------------------------------------------------------------

record ChomskyEpsteinCorpusReceipt : Set where
  constructor chomsky-epstein-corpus-receipt
  field
    sourceReference : String
    proposedInviteeMention : Bool
    attendanceEstablished : Bool
    relationshipEstablished : Bool
    endorsementEstablished : Bool
open ChomskyEpsteinCorpusReceipt public

bachListChomskyReceipt : ChomskyEpsteinCorpusReceipt
bachListChomskyReceipt = chomsky-epstein-corpus-receipt
  "EFTA02458524"
  true false false false

------------------------------------------------------------------------
-- PROMOTION FIREWALLS.
------------------------------------------------------------------------

data LLMGeneralisationRefutesChomsky : Set where
data LLMFailureProvesUniversalGrammar : Set where
data LLMSuccessEstablishesHumanMechanism : Set where
data PovertyOfStimulusImpliesFixedUniversalGrammar : Set where
data ProposedInviteEstablishesRelationship : Set where

data MediaTheoryEstablishesLinguisticTheory : Set where

llmGeneralisationDoesNotRefuteWholeChomskyFramework :
  LLMGeneralisationRefutesChomsky → ⊥
llmGeneralisationDoesNotRefuteWholeChomskyFramework ()

llmFailureDoesNotProveUniversalGrammar :
  LLMFailureProvesUniversalGrammar → ⊥
llmFailureDoesNotProveUniversalGrammar ()

llmSuccessDoesNotEstablishHumanMechanism :
  LLMSuccessEstablishesHumanMechanism → ⊥
llmSuccessDoesNotEstablishHumanMechanism ()

povertyOfStimulusDoesNotFixUniqueInnateTheory :
  PovertyOfStimulusImpliesFixedUniversalGrammar → ⊥
povertyOfStimulusDoesNotFixUniqueInnateTheory ()

proposedInviteDoesNotEstablishChomskyRelationship :
  ProposedInviteEstablishesRelationship → ⊥
proposedInviteDoesNotEstablishChomskyRelationship ()

mediaTheoryDoesNotEstablishLinguisticTheory :
  MediaTheoryEstablishesLinguisticTheory → ⊥
mediaTheoryDoesNotEstablishLinguisticTheory ()

record ChomskyLanguageAIBoundary : Set where
  constructor chomsky-language-ai-boundary
  field
    manufacturingConsentPriorArtRetained : Bool
    politicalAndLinguisticClaimsSeparated : Bool
    innateSyntaxOnlyRouteChallenged : Bool
    wholeFrameworkRefuted : Bool
    humanMechanismRecoveredFromLLM : Bool
    llmFailureProvesUG : Bool
    bachInviteMentionCreatesRelationship : Bool

canonicalChomskyLanguageAIBoundary : ChomskyLanguageAIBoundary
canonicalChomskyLanguageAIBoundary =
  chomsky-language-ai-boundary true true true false false false false
