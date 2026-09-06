module DASHI.Core.ConsumerGuidedReopenableRefinementExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level; _⊔_)

------------------------------------------------------------------------
-- Consumer-guided reopenable refinement.
--
-- A quotient/fibre may be reopened when a downstream consumer cannot preserve
-- its decision under the current approximation. Exact descent is preferred;
-- approximate descent is allowed only when an explicit decision margin proves
-- the approximation harmless for the consumer.
------------------------------------------------------------------------

data RefinementStatus : Set where
  closed : RefinementStatus
  reopened : RefinementStatus
  refined : RefinementStatus

data ReopenReason : Set where
  consumerConflict : ReopenReason
  insufficientMargin : ReopenReason
  approximationTooLarge : ReopenReason
  newEvidence : ReopenReason

data RefinementBoundary : Set where
  noApproximateDescentWithoutMargin : RefinementBoundary
  noLowMarginClosureByConvention : RefinementBoundary
  noConsumerConflictCountsAsRefutation : RefinementBoundary
  noRefinementErasesOldProvenance : RefinementBoundary
  noNewFibreSilentlyClaimsOldAuthority : RefinementBoundary

record ConsumerObservation
    {State Observation : Set}
    (observe : State → Observation) : Set₁ where
  field
    observationReading : String

open ConsumerObservation public

record ExactConsumerDescent
    {Fine Coarse Output : Set}
    (project : Fine → Coarse)
    (consume : Fine → Output) : Set₁ where
  constructor exactConsumerDescent
  field
    quotientConsumer : Coarse → Output
    exactDescent :
      ∀ fine →
      consume fine ≡ quotientConsumer (project fine)

open ExactConsumerDescent public

record ReopenableConsumerQuotient
    {Fine Coarse Output : Set}
    (project : Fine → Coarse)
    (consume : Fine → Output) : Set₁ where
  constructor reopenableConsumerQuotient
  field
    status : RefinementStatus
    exactOwner : ExactConsumerDescent project consume
    canReopen : Bool
    reopenReason : ReopenReason
    provenanceReceipt : String

open ReopenableConsumerQuotient public

exactDescentConsumerAgreement :
  ∀ {Fine Coarse Output}
    {project : Fine → Coarse}
    {consume : Fine → Output} →
  (descent : ExactConsumerDescent project consume) →
  ∀ fine →
  consume fine ≡ quotientConsumer descent (project fine)
exactDescentConsumerAgreement descent fine = exactDescent descent fine

------------------------------------------------------------------------
-- Finite witness carrier for consumer failures and targeted reopening.
------------------------------------------------------------------------

record ConsumerFailureWitness
    {Fine Coarse Output : Set}
    (project : Fine → Coarse)
    (consume : Fine → Output) : Set₁ where
  constructor consumerFailureWitness
  field
    left right : Fine
    sameOldFibre : project left ≡ project right
    consumerSeparates : consume left → consume right → Set
    witnessReading : String

open ConsumerFailureWitness public

record RefinementReceipt : Set where
  constructor refinementReceipt
  field
    oldCarrier : String
    newCarrier : String
    consumerName : String
    reason : ReopenReason
    evidenceReceipt : String
    preservesOldProvenance : Bool

open RefinementReceipt public

record ReopenableRefinement
    {Fine Old New : Set}
    (oldProject : Fine → Old)
    (newProject : Fine → New) : Set₁ where
  constructor reopenableRefinement
  field
    oldStatus : RefinementStatus
    newStatus : RefinementStatus
    receipt : RefinementReceipt
    newRefinesOld :
      ∀ x y →
      newProject x ≡ newProject y →
      oldProject x ≡ oldProject y

open ReopenableRefinement public

------------------------------------------------------------------------
-- Reopening is not refutation. The old quotient remains a valid historical
-- object even if a new consumer forces finer distinctions.
------------------------------------------------------------------------

record HistoricalCarrierStatus : Set where
  constructor historicalCarrierStatus
  field
    carrierName : String
    wasAdmissibleForPriorConsumer : Bool
    stillRetained : Bool
    currentConsumerRequiresRefinement : Bool

open HistoricalCarrierStatus public

reopeningDoesNotEraseHistory :
  HistoricalCarrierStatus → Bool
reopeningDoesNotEraseHistory status = stillRetained status

------------------------------------------------------------------------
-- Approximate descent.
------------------------------------------------------------------------

record ApproximateConsumerDescent
    {Fine Coarse Output : Set}
    (project : Fine → Coarse)
    (consume : Fine → Output)
    (Within : Output → Output → Set) : Set₁ where
  constructor approximateConsumerDescent
  field
    quotientConsumer : Coarse → Output
    approximationBound :
      ∀ fine →
      Within (consume fine) (quotientConsumer (project fine))

open ApproximateConsumerDescent public

record ConsumerDecisionMargin
    {Output Decision : Set}
    (Within : Output → Output → Set)
    (decide : Output → Decision) : Set₁ where
  constructor consumerDecisionMargin
  field
    stableInsideMargin :
      ∀ actual approximate →
      Within actual approximate →
      decide actual ≡ decide approximate

open ConsumerDecisionMargin public

approximateDescentPreservesDecision :
  ∀ {Fine Coarse Output Decision}
    {project : Fine → Coarse}
    {consume : Fine → Output}
    {Within : Output → Output → Set}
    {decide : Output → Decision} →
  (descent : ApproximateConsumerDescent project consume Within) →
  ConsumerDecisionMargin Within decide →
  ∀ fine →
  decide (consume fine)
  ≡ decide (quotientConsumer descent (project fine))
approximateDescentPreservesDecision {consume = consume} descent margin fine =
  stableInsideMargin margin
    (consume fine)
    (quotientConsumer descent (project fine))
    (approximationBound descent fine)

------------------------------------------------------------------------
-- 6. Low-margin / large-defect regions can be declared as the only places in
--    which refinement is allowed to split an old fibre.
------------------------------------------------------------------------

record ConsumerGuidedRefinementRegion
    {Fine Old New : Set}
    (oldProject : Fine → Old)
    (newProject : Fine → New) : Set₁ where
  constructor consumerGuidedRefinementRegion
  field
    NeedsRefinement : Fine → Set
    localRefinement :
      ∀ x y →
      newProject x ≡ newProject y →
      oldProject x ≡ oldProject y
    noSplitOutsideNeed :
      ∀ x y →
      oldProject x ≡ oldProject y →
      (NeedsRefinement x → NeedsRefinement y → Set) →
      Set

open ConsumerGuidedRefinementRegion public

------------------------------------------------------------------------
-- Canonical policy surface.
------------------------------------------------------------------------

record ConsumerGuidedRefinementPolicy : Set₁ where
  constructor consumerGuidedRefinementPolicy
  field
    Consumer : Set
    consumerName : Consumer → String
    lowMarginRequiresReopen : Consumer → Bool
    exactDescentCloses : Consumer → Bool
    approximateDescentNeedsMargin : Consumer → Bool
    preserveHistoricalCarrier : Consumer → Bool

open ConsumerGuidedRefinementPolicy public

canonicalBoundaries : List RefinementBoundary
canonicalBoundaries =
  noApproximateDescentWithoutMargin
  ∷ noLowMarginClosureByConvention
  ∷ noConsumerConflictCountsAsRefutation
  ∷ noRefinementErasesOldProvenance
  ∷ noNewFibreSilentlyClaimsOldAuthority
  ∷ []
