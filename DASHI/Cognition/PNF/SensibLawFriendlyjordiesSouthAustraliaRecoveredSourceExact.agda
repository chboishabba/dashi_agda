module DASHI.Cognition.PNF.SensibLawFriendlyjordiesSouthAustraliaRecoveredSourceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.HumanReviewCore as HumanReview
import DASHI.Core.FriendlyjordiesGovernanceQuestionExact as March
import DASHI.Cognition.PNF.SensibLawPersistentStatementObservationEventSpineExact as Trace
import DASHI.Cognition.PNF.SensibLawChronologyContestationSpineExact as Contest
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesNarrativeGovernanceWeldExact as Weld
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesSouthAustraliaGovernanceWeldExact as Base
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesGovernanceMaxCutExact as Rooted
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesWorldEvidenceExact as World
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedWorldEvidenceExact as Reviewed
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesCausalIdentificationMaxCutExact as Causal
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedCausalIdentificationExact as ReviewedCausal

sensibLawSouthAustraliaRevision : String
sensibLawSouthAustraliaRevision =
  "SensibLaw/agent/friendlyjordies-south-australia-source-20261016 24aa97c0a596f01aca7630ea621bcc4525a90f9a"

southAustraliaArchiveSourceUnitPinned : Bool
southAustraliaArchiveSourceUnitPinned = true

southAustraliaAttributionRetained : Bool
southAustraliaAttributionRetained = true

southAustraliaSourcePaymentCreatesWorldTruth : Bool
southAustraliaSourcePaymentCreatesWorldTruth = false

southAustraliaSourcePaysGovernanceCausation : Bool
southAustraliaSourcePaysGovernanceCausation = false

southAustraliaReviewedCausalPremiseStillRequired : Bool
southAustraliaReviewedCausalPremiseStillRequired = true

mkRecoveredTrace :
  String → String → String → String → String → String →
  Trace.SemanticTracePath
mkRecoveredTrace statementRef exactSpanRef literalText observationRef claimRef downstreamRef =
  Trace.traceFromLinks
    (Trace.statement-candidate-observation-link
      (Trace.persistent-statement-identity
        statementRef
        "demo/narrative/friendlyjordies_chat_arguments.json"
        sensibLawSouthAustraliaRevision
        exactSpanRef
        literalText)
      statementRef
      observationRef
      (Trace.parser-run-identity
        "parser-run:friendlyjordies:south-australia-recovered"
        "sensiblaw-narrative-fixture")
      "review:parse:friendlyjordies:south-australia-recovered"
      "admission:candidate:friendlyjordies:south-australia-recovered"
      true refl false refl false refl false refl)
    (Trace.observation-event-link
      observationRef
      "event:public-discourse:south-australia-renewables"
      "assembly:friendlyjordies:south-australia-recovered"
      true refl false refl)
    (claimRef ∷ [])
    (downstreamRef ∷ [])

southAustraliaSourceTrace : Trace.SemanticTracePath
southAustraliaSourceTrace =
  mkRecoveredTrace
    "statement:friendlyjordies:south-australia-renewables"
    "jordies_case:u6"
    "FriendlyJordies said that South Australia was producing 70% of its energy from renewable sources and was planned to reach 100% the following year."
    "observation:friendlyjordies:south-australia-renewables"
    "claim:friendlyjordies:south-australia-renewables"
    "cmp:south-australia:governance-example"

southAustraliaLaborFramingTrace : Trace.SemanticTracePath
southAustraliaLaborFramingTrace =
  mkRecoveredTrace
    "statement:friendlyjordies:south-australia-labor-framing"
    "jordies_case:u7"
    "FriendlyJordies framed South Australia's renewable trajectory as what happens when you let Labor cook for a quarter of a century."
    "observation:friendlyjordies:south-australia-labor-framing"
    "claim:friendlyjordies:south-australia-labor-framing"
    "cmp:south-australia:governance-causal-framing"

southAustraliaCounterCausalTrace : Trace.SemanticTracePath
southAustraliaCounterCausalTrace =
  mkRecoveredTrace
    "statement:counter:south-australia-causal-framing"
    "counter_analysis:u7"
    "The analysis treated the claimed causal link between long-run Labor governance and South Australia's renewable trajectory as a causal or counterfactual claim requiring independent evidence."
    "observation:counter:south-australia-causal-framing"
    "claim:counter:south-australia-causal-framing"
    "cmp:south-australia:governance-causal-framing"

southAustraliaClaimLeaf : Contest.ClaimLeaf Base.southAustraliaRoot
southAustraliaClaimLeaf =
  Contest.claim-leaf
    "claim:friendlyjordies:south-australia-renewables"
    Contest.affirmation
    "speaker:friendlyjordies"
    ("statement:friendlyjordies:south-australia-renewables" ∷ [])
    ("observation:friendlyjordies:south-australia-renewables" ∷ [])
    []
    ("scope:south-australia-renewables" ∷ [])
    Contest.unreviewed
    "review:friendlyjordies:south-australia-renewables"
    "relation:source-trace:friendlyjordies:south-australia-renewables"
    true refl false refl false refl false refl

southAustraliaRootedTraceClaim :
  Weld.RootedTraceClaim Base.southAustraliaRoot southAustraliaClaimLeaf
southAustraliaRootedTraceClaim =
  Weld.rooted-trace-claim
    southAustraliaSourceTrace
    (Contest.PropositionRoot.propositionRef Base.southAustraliaRoot)
    refl
    (Contest.ClaimLeaf.claimRef southAustraliaClaimLeaf)
    refl
    "receipt:friendlyjordies:south-australia:rooted-trace"
    sensibLawSouthAustraliaRevision
    refl
    "jordies_case:u6"
    refl
    true refl
    false refl

southAustraliaSourcePaidCase : Base.SourcePaidHistoricalCase
southAustraliaSourcePaidCase =
  Base.source-paid-historical-case
    March.southAustraliaRenewables
    (Contest.PropositionRoot.propositionRef Base.southAustraliaRoot)
    southAustraliaSourceTrace
    Rooted.southAustraliaWorldDemand
    false refl

southAustraliaRootedPayment :
  Rooted.RootedHistoricalCasePayment March.southAustraliaRenewables
southAustraliaRootedPayment =
  Rooted.rooted-historical-case-payment
    Base.southAustraliaRoot
    southAustraliaClaimLeaf
    southAustraliaRootedTraceClaim
    southAustraliaSourcePaidCase
    refl
    refl
    false refl

southAustraliaWorldTransitionEvidenceFromReviewedDecision :
  Reviewed.ReviewedWorldEvidenceDecision
    March.southAustraliaRenewables
    World.southAustraliaExternalWorldBundle →
  Base.WorldTransitionEvidence southAustraliaSourcePaidCase
southAustraliaWorldTransitionEvidenceFromReviewedDecision decision =
  Base.world-transition-evidence
    "world-transition:south-australia:reviewed-causal-bridge"
    (Reviewed.sourceRefs decision)
    (HumanReview.GenericHumanReviewReceipt.reviewReceiptRef
      (Reviewed.genericReview decision))
    true refl
    (Reviewed.CausalPremise decision)
    (Reviewed.causalPremiseWitness decision)
    false refl

record SouthAustraliaRecoveredReviewedIdentificationGate : Set₂ where
  constructor south-australia-recovered-reviewed-identification-gate
  field
    rootedSourcePayment :
      Rooted.RootedHistoricalCasePayment March.southAustraliaRenewables
    sourcePaymentMatchesRecovered :
      rootedSourcePayment ≡ southAustraliaRootedPayment
    reviewedIdentification :
      ReviewedCausal.ReviewedIdentifiedTransitionAdmission
        March.southAustraliaRenewables
        Causal.southAustraliaCausalEstimandDemand

open SouthAustraliaRecoveredReviewedIdentificationGate public

data ArchiveSourcePaymentCreatesWorldTruth : Set where
data ArchiveSourcePaymentIdentifiesGovernanceCause : Set where
data SeventyPercentClaimEqualsIndependentEnergyFact : Set where
data LaborFramingEqualsUniversalPartyRanking : Set where

archiveSourcePaymentDoesNotCreateWorldTruth :
  ArchiveSourcePaymentCreatesWorldTruth → ⊥
archiveSourcePaymentDoesNotCreateWorldTruth ()

archiveSourcePaymentDoesNotIdentifyGovernanceCause :
  ArchiveSourcePaymentIdentifiesGovernanceCause → ⊥
archiveSourcePaymentDoesNotIdentifyGovernanceCause ()

attributedSeventyPercentDoesNotEqualIndependentEnergyFact :
  SeventyPercentClaimEqualsIndependentEnergyFact → ⊥
attributedSeventyPercentDoesNotEqualIndependentEnergyFact ()

laborFramingDoesNotCreateUniversalPartyRanking :
  LaborFramingEqualsUniversalPartyRanking → ⊥
laborFramingDoesNotCreateUniversalPartyRanking ()

record SouthAustraliaRecoveredSourceBoundary : Set where
  constructor south-australia-recovered-source-boundary
  field
    archiveSourcePaid : Bool
    outerSpeakerRetained : Bool
    causalFramingSeparated : Bool
    counterAnalysisSeparated : Bool
    independentWorldEvidenceStillRequired : Bool
    causalIdentificationStillRequired : Bool
    humanReviewStillRequired : Bool
    sourcePaymentCreatesWorldTruth : Bool
    universalPartyRankingCreated : Bool

canonicalSouthAustraliaRecoveredSourceBoundary :
  SouthAustraliaRecoveredSourceBoundary
canonicalSouthAustraliaRecoveredSourceBoundary =
  south-australia-recovered-source-boundary
    true true true true true true true false false
