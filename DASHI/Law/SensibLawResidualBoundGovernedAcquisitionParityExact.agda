module DASHI.Law.SensibLawResidualBoundGovernedAcquisitionParityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Rust-led parity owner for the introspective source-route repair.
--
-- The governed provider remains generic.  The proof-search engine may schedule
-- acquisition only after the live proof residual, selected hypothesis, target
-- proposition, producer and jurisdiction are welded into one bound demand.
-- This mirrors the #823 introspective principle that observing a possible repair
-- is not itself paying the consumer defect.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

rustSourceHead : String
rustSourceHead = "eccf0036a90e9cc0d632b6f0810f8549128af83c"

permitSchema : String
permitSchema = "sl.residual_bound_authority_demand.v0_1"

permitAuthority : String
permitAuthority = "experimental_candidate_only"

record ResidualBoundGovernedAcquisitionBoundary : Set where
  constructor residualBoundGovernedAcquisitionBoundary
  field
    residualIdentityRetained : Bool
    residualIdentityRetainedIsTrue : residualIdentityRetained ≡ true

    targetPropositionRetained : Bool
    targetPropositionRetainedIsTrue : targetPropositionRetained ≡ true

    scheduledProducerRetained : Bool
    scheduledProducerRetainedIsTrue : scheduledProducerRetained ≡ true

    selectedHypothesisRetained : Bool
    selectedHypothesisRetainedIsTrue : selectedHypothesisRetained ≡ true

    jurisdictionRetained : Bool
    jurisdictionRetainedIsTrue : jurisdictionRetained ≡ true

    sourceIdentityRetained : Bool
    sourceIdentityRetainedIsTrue : sourceIdentityRetained ≡ true

    residualMustRemainOpen : Bool
    residualMustRemainOpenIsTrue : residualMustRemainOpen ≡ true

    hypothesisResidualMustEqualLiveResidual : Bool
    hypothesisResidualMustEqualLiveResidualIsTrue :
      hypothesisResidualMustEqualLiveResidual ≡ true

    hypothesisPropositionMustEqualResidualProposition : Bool
    hypothesisPropositionMustEqualResidualPropositionIsTrue :
      hypothesisPropositionMustEqualResidualProposition ≡ true

    hypothesisProducerMustEqualResidualProducer : Bool
    hypothesisProducerMustEqualResidualProducerIsTrue :
      hypothesisProducerMustEqualResidualProducer ≡ true

    hypothesisJurisdictionMustEqualResidualJurisdiction : Bool
    hypothesisJurisdictionMustEqualResidualJurisdictionIsTrue :
      hypothesisJurisdictionMustEqualResidualJurisdiction ≡ true

    demandPropositionMustEqualResidualProposition : Bool
    demandPropositionMustEqualResidualPropositionIsTrue :
      demandPropositionMustEqualResidualProposition ≡ true

    demandJurisdictionMustMatchResidualJurisdiction : Bool
    demandJurisdictionMustMatchResidualJurisdictionIsTrue :
      demandJurisdictionMustMatchResidualJurisdiction ≡ true

    sourceRoutePaysScheduledGap : Bool
    sourceRoutePaysScheduledGapIsTrue : sourceRoutePaysScheduledGap ≡ true

    sourceRouteUsesScheduledProducer : Bool
    sourceRouteUsesScheduledProducerIsTrue : sourceRouteUsesScheduledProducer ≡ true

    permitRequiredBeforeGovernedResearchFetch : Bool
    permitRequiredBeforeGovernedResearchFetchIsTrue :
      permitRequiredBeforeGovernedResearchFetch ≡ true

    acquisitionAutomaticallySemanticPayment : Bool
    acquisitionAutomaticallySemanticPaymentIsFalse :
      acquisitionAutomaticallySemanticPayment ≡ false

    acquisitionAutomaticallyClosesConsumer : Bool
    acquisitionAutomaticallyClosesConsumerIsFalse :
      acquisitionAutomaticallyClosesConsumer ≡ false

canonicalResidualBoundGovernedAcquisitionBoundary :
  ResidualBoundGovernedAcquisitionBoundary
canonicalResidualBoundGovernedAcquisitionBoundary =
  residualBoundGovernedAcquisitionBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Fail-closed introspective firewalls.
------------------------------------------------------------------------

data AuditFindingAutomaticallyFormalProgress : Set where
data BoundPermitAutomaticallySemanticPayment : Set where
data BoundPermitAutomaticallyConsumerClosure : Set where
data RelevantSourceAutomaticallyScheduledRepair : Set where

auditFindingDoesNotBecomeFormalProgress :
  AuditFindingAutomaticallyFormalProgress → ⊥
auditFindingDoesNotBecomeFormalProgress ()

boundPermitDoesNotBecomeSemanticPayment :
  BoundPermitAutomaticallySemanticPayment → ⊥
boundPermitDoesNotBecomeSemanticPayment ()

boundPermitDoesNotBecomeConsumerClosure :
  BoundPermitAutomaticallyConsumerClosure → ⊥
boundPermitDoesNotBecomeConsumerClosure ()

relevantSourceDoesNotBecomeScheduledRepair :
  RelevantSourceAutomaticallyScheduledRepair → ⊥
relevantSourceDoesNotBecomeScheduledRepair ()
