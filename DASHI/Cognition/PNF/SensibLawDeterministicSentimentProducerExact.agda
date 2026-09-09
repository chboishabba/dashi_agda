module DASHI.Cognition.PNF.SensibLawDeterministicSentimentProducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Sentiment is an auxiliary observation producer, not semantic authority.
--
-- This owner distinguishes rule/lexicon engines from trained statistical
-- pipelines because the project anti-AI/reproducibility rule may care about
-- either (a) absence of learned models, or (b) exact local replayability.
------------------------------------------------------------------------

data SentimentProducerKind : Set where
  vaderParityRust : SentimentProducerKind
  vaderSentimentalRust : SentimentProducerKind
  spacyTrainedPipeline : SentimentProducerKind

data ReproducibilityClass : Set where
  exactReferenceParity : ReproducibilityClass
  deterministicPinnedPort : ReproducibilityClass
  pinnedLearnedWeights : ReproducibilityClass
  unpinnedOrRemote : ReproducibilityClass

data LearnedModelClass : Set where
  noLearnedWeights : LearnedModelClass
  containsLearnedWeights : LearnedModelClass

record SentimentProducerReceipt : Set where
  constructor sentimentProducerReceipt
  field
    producer : SentimentProducerKind
    versionReference : String
    reproducibility : ReproducibilityClass
    learnedModelClass : LearnedModelClass
    lexiconOrModelDigestRequired : Bool
    runtimeDependencies : String
    boundedDescription : String

open SentimentProducerReceipt public

vaderParityReceipt : SentimentProducerReceipt
vaderParityReceipt = sentimentProducerReceipt
  vaderParityRust
  "vader_parity 0.1.0; parity target Python vaderSentiment 3.3.2"
  exactReferenceParity
  noLearnedWeights
  true
  "std-only; zero runtime dependencies according to crate documentation"
  "Rule/lexicon scorer with vendored VADER and emoji data and exact published-score parity against the pinned Python reference. Preferred when reference parity and frozen data provenance dominate throughput concerns."

vaderSentimentalReceipt : SentimentProducerReceipt
vaderSentimentalReceipt = sentimentProducerReceipt
  vaderSentimentalRust
  "bosun-ai/vader-sentimental; current repository checked 2026-09-09"
  deterministicPinnedPort
  noLearnedWeights
  true
  "Rust port; optimized allocation/hash/loop implementation"
  "Rule/lexicon VADER port emphasizing Rust-native performance. It documents speed improvements but does not make the same byte-level Python-3.3.2 parity contract as vader_parity."

spacySmallEnglishReceipt : SentimentProducerReceipt
spacySmallEnglishReceipt = sentimentProducerReceipt
  spacyTrainedPipeline
  "spaCy en_core_web_sm; exact project-installed package version must be retained by runtime receipt"
  pinnedLearnedWeights
  containsLearnedWeights
  true
  "Python spaCy pipeline; tok2vec/tagger/parser/senter/NER/attribute_ruler/lemmatizer capabilities depend on installed package"
  "en_core_web_sm is a trained statistical pipeline, not a rule-only parser. A pinned wheel/config/weights digest can make inference replayable, but this does not satisfy a literal no-learned-model policy."

------------------------------------------------------------------------
-- Project policy interpretation is explicit rather than guessed.
------------------------------------------------------------------------

data AntiAIRuleInterpretation : Set where
  prohibitLearnedModels : AntiAIRuleInterpretation
  prohibitRemoteOrGenerativeInference : AntiAIRuleInterpretation
  requirePinnedReplayability : AntiAIRuleInterpretation

data PolicyCompatibility : Set where
  compatible : PolicyCompatibility
  incompatible : PolicyCompatibility
  requiresPolicyDecision : PolicyCompatibility

compatibility : AntiAIRuleInterpretation → SentimentProducerReceipt → PolicyCompatibility
compatibility prohibitLearnedModels receipt with learnedModelClass receipt
... | noLearnedWeights = compatible
... | containsLearnedWeights = incompatible
compatibility prohibitRemoteOrGenerativeInference receipt with reproducibility receipt
... | unpinnedOrRemote = incompatible
... | _ = compatible
compatibility requirePinnedReplayability receipt with reproducibility receipt
... | unpinnedOrRemote = incompatible
... | _ = compatible

------------------------------------------------------------------------
-- Sentiment output is retained independently of discourse truth/tension.
-- Numeric runtime values are not fabricated here; they enter by receipt.
------------------------------------------------------------------------

record SentimentObservation : Set where
  constructor sentimentObservation
  field
    sourceSpanReference : String
    producerReceiptReference : String
    negativeScore : String
    neutralScore : String
    positiveScore : String
    compoundScore : String
    sourceDigest : String
    producerDigest : String
    observationOnly : Bool

open SentimentObservation public

record SentimentAdmissionBoundary : Set where
  constructor sentimentAdmissionBoundary
  field
    negativeSentimentProvesFalsehood : Bool
    negativeSentimentProvesFalsehoodIsFalse : negativeSentimentProvesFalsehood ≡ false
    neutralSentimentProvesCandour : Bool
    neutralSentimentProvesCandourIsFalse : neutralSentimentProvesCandour ≡ false
    sentimentDiscontinuityMayRaiseSpeakerCutPriority : Bool
    sentimentDiscontinuityMayRaiseSpeakerCutPriorityIsTrue : sentimentDiscontinuityMayRaiseSpeakerCutPriority ≡ true
    sentimentMayBeOneDiscourseFeature : Bool
    sentimentMayBeOneDiscourseFeatureIsTrue : sentimentMayBeOneDiscourseFeature ≡ true

canonicalSentimentAdmissionBoundary : SentimentAdmissionBoundary
canonicalSentimentAdmissionBoundary = sentimentAdmissionBoundary false refl false refl true refl true refl
