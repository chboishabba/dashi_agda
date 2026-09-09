module DASHI.Cognition.PNF.SensibLawABC730DiscourseCutBenchmarkRevisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Empirical revision receipt for slr-discourse-cut-v1 -> v2.
--
-- The first executable run on the ABC 7.30 specimen exposed three distinct
-- failure modes.  They are retained here as observations that justify the v2
-- scorer changes; none is a theorem about speakers or truth.
------------------------------------------------------------------------

data RuntimeFailureMode : Set where
  sentenceResidualFloorBias : RuntimeFailureMode
  ungatedSentimentDistractor : RuntimeFailureMode
  tokenizationFragileSpeakerProfile : RuntimeFailureMode
  parserCrossCutAttachmentPenalty : RuntimeFailureMode

record RuntimeFailureReceipt : Set where
  constructor runtimeFailureReceipt
  field
    failureMode : RuntimeFailureMode
    specimenReference : String
    observedResult : String
    repair : String
    admissionNote : String

open RuntimeFailureReceipt public

sentenceResidualBiasReceipt : RuntimeFailureReceipt
sentenceResidualBiasReceipt = runtimeFailureReceipt
  sentenceResidualFloorBias
  "ABC 7.30 specimen; joint focus sentences 42,45; slr-discourse-cut-v1"
  "sentence 42 residual count 15 contributed +5 to every local cut while sentence 45 residual count 4 contributed +1, suppressing all sentence-45 candidates from the joint top-30"
  "remove residual count from cut score; retain residual density only as sentence inspection priority"
  "high residual density prioritises review but does not identify an intra-sentence cut"

sentimentDistractorReceipt : RuntimeFailureReceipt
sentimentDistractorReceipt = runtimeFailureReceipt
  ungatedSentimentDistractor
  "ABC 7.30 sentence 42 split 67"
  "rhetorical valence change around 'undermining | the ability' produced sentiment delta 1.2389 and outranked the known Wong-to-Husic transition"
  "cap sentiment contribution and treat it as auxiliary unless supported by an independent boundary cue"
  "sentiment discontinuity is affective evidence, not speaker-boundary evidence"

profileTokenizationReceipt : RuntimeFailureReceipt
profileTokenizationReceipt = runtimeFailureReceipt
  tokenizationFragileSpeakerProfile
  "ABC 7.30 sentence 45 with speaker-profiles.example.tsv"
  "spaCy tokenised 'two-state' as two / - / state, so the literal profile marker failed and the right-hand span was spuriously assigned to Ed Husic"
  "derive profile lexical features from unigrams plus normalized hyphen compounds and short lemma n-grams"
  "profile compatibility remains candidate evidence and cannot verify speaker identity"

crossCutDependencyReceipt : RuntimeFailureReceipt
crossCutDependencyReceipt = runtimeFailureReceipt
  parserCrossCutAttachmentPenalty
  "ABC 7.30 sentence 45 split 7"
  "the likely Shoebridge-to-Leeser transition after 'gaslighting from Labor' had five spaCy dependency edges crossing the cut because the right clause was coordinated back into the left parse"
  "report raw and content dependency crossings separately; at independently cued discourse boundaries, do not count cc/conj/punct edges as content-severance evidence"
  "parser attachment across a suspected broadcast cut is a transcript-integrity residual, not proof against the cut"

------------------------------------------------------------------------
-- Revision policy.
------------------------------------------------------------------------

record DiscourseCutV2Policy : Set where
  constructor discourseCutV2Policy
  field
    residualChangesCutRank : Bool
    residualChangesCutRankIsFalse : residualChangesCutRank ≡ false
    residualMayRaiseInspectionPriority : Bool
    residualMayRaiseInspectionPriorityIsTrue : residualMayRaiseInspectionPriority ≡ true
    sentimentUnbounded : Bool
    sentimentUnboundedIsFalse : sentimentUnbounded ≡ false
    sentimentRequiresIndependentCueForFullWeight : Bool
    sentimentRequiresIndependentCueForFullWeightIsTrue : sentimentRequiresIndependentCueForFullWeight ≡ true
    hyphenCompoundsNormalizedForProfiles : Bool
    hyphenCompoundsNormalizedForProfilesIsTrue : hyphenCompoundsNormalizedForProfiles ≡ true
    coordinationCrossingsMayBeDownweightedAtCuedBoundary : Bool
    coordinationCrossingsMayBeDownweightedAtCuedBoundaryIsTrue : coordinationCrossingsMayBeDownweightedAtCuedBoundary ≡ true
    anyFeatureSelfVerifiesCut : Bool
    anyFeatureSelfVerifiesCutIsFalse : anyFeatureSelfVerifiesCut ≡ false

canonicalDiscourseCutV2Policy : DiscourseCutV2Policy
canonicalDiscourseCutV2Policy = discourseCutV2Policy
  false refl
  true refl
  false refl
  true refl
  true refl
  true refl
  false refl

runtimeSchema : String
runtimeSchema = "slr-discourse-cut-v2"

nextBlindBenchmark : String
nextBlindBenchmark =
  "rerun sentences 42 and 45 without speaker profiles first; compare within-sentence rank of split 35 and split 7 against v1, then repeat with normalized profiles"
