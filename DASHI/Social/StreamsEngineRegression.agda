module DASHI.Social.StreamsEngineRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (suc; zero)

open import DASHI.Social.StreamsEngineBoundary

------------------------------------------------------------------------
-- Canonical first-class finance and conversation examples.

transactionAnchorExample : SourceAnchor
transactionAnchorExample =
  sourceAnchor
    transactionAnchor
    "transaction-42"
    "2025-05-03T10:21:00+10:00"
    "2025-05-04T09:00:00+10:00"
    "bank statement import"

utteranceAnchorExample : SourceAnchor
utteranceAnchorExample =
  sourceAnchor
    utteranceAnchor
    "utterance-311"
    "2025-05-03T10:19:00+10:00"
    "2025-05-03T10:19:00+10:00"
    "consented conversation export"

financeStreamExample : StreamDefinition
financeStreamExample =
  streamDefinition
    "stream-finance-net-a-to-b"
    "net flow actor A to actor B"
    financeStreamFamily
    monetaryFlowMeasure
    actorAToActorB
    minorCurrencyUnit
    "actor-a"
    "relationship-a-b"
    deterministicRuleDerivation
    "signed transaction amounts aggregated by actor relation and time window"

concernStreamExample : StreamDefinition
concernStreamExample =
  streamDefinition
    "stream-concern-a-to-b"
    "concern-language score actor A to actor B"
    conversationStreamFamily
    concernMeasure
    actorAToActorB
    boundedScoreUnit
    "actor-a"
    "relationship-a-b"
    modelSuggestionDerivation
    "advisory concern-language feature aggregated over consented utterances"

financePointExample : StreamPoint
financePointExample =
  streamPoint
    financeStreamExample
    "2025-05-03T10:21:00+10:00"
    (suc (suc zero))
    (suc zero)
    (transactionAnchorExample ∷ [])
    "two minor-unit proxy steps in the regression witness"

financePointAdmissible : AdmissibleStreamPoint financePointExample
financePointAdmissible = admissibleStreamPoint one

concernPointExample : StreamPoint
concernPointExample =
  streamPoint
    concernStreamExample
    "2025-05-03T10:19:00+10:00"
    (suc zero)
    (suc (suc zero))
    (utteranceAnchorExample ∷ [])
    "one-half bounded concern proxy; advisory only"

concernPointAdmissible : AdmissibleStreamPoint concernPointExample
concernPointAdmissible = admissibleStreamPoint one

------------------------------------------------------------------------
-- Cross-stream alignment remains candidate-only.

alignmentPatternExample : StreamPattern
alignmentPatternExample =
  streamPattern
    "pattern-finance-concern-alignment"
    financeConversationAlignmentPattern
    candidatePatternStatus
    "2025-05-01"
    "2025-05-31"
    (financeStreamExample ∷ concernStreamExample ∷ [])
    (transactionAnchorExample ∷ utteranceAnchorExample ∷ [])
    "financial-flow change and concern-language change occur in the same review window"
    "temporal alignment is not causation, abuse classification, diagnosis, legal liability, trading advice, or moral verdict"

alignmentPatternAdmissible : AdmissibleStreamPattern alignmentPatternExample
alignmentPatternAdmissible =
  admissibleStreamPattern one one refl

feedbackExample : BidirectionalStreamLink
feedbackExample =
  bidirectionalStreamLink
    streamToReviewAnnotation
    utteranceAnchorExample
    "review-annotation-19"
    true
    refl
    true
    refl
    "candidate pattern produces a reviewable annotation while preserving the raw utterance"

legalAuthorityBlockedRegression :
  AuthorityBlocked legalAuthorityClaim ≡ true
legalAuthorityBlockedRegression = refl

clinicalAuthorityBlockedRegression :
  AuthorityBlocked clinicalAuthorityClaim ≡ true
clinicalAuthorityBlockedRegression = refl

tradingAuthorityBlockedRegression :
  AuthorityBlocked tradingAuthorityClaim ≡ true
tradingAuthorityBlockedRegression = refl

causalAuthorityBlockedRegression :
  AuthorityBlocked causalAuthorityClaim ≡ true
causalAuthorityBlockedRegression = refl

moralAuthorityBlockedRegression :
  AuthorityBlocked moralTruthAuthorityClaim ≡ true
moralAuthorityBlockedRegression = refl

visualizationAuthorityNotBlockedRegression :
  AuthorityBlocked visualizationClaim ≡ false
visualizationAuthorityNotBlockedRegression = refl
