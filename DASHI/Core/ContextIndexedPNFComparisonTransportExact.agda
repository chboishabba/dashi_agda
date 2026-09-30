module DASHI.Core.ContextIndexedPNFComparisonTransportExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl; cong; trans)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Refinement
import DASHI.Core.IndexedInterpretationMorphismExact as Indexed

------------------------------------------------------------------------
-- DASHI-local generic weld: context/consumer-indexed observable semantics.
-- Distinct from original JMD finite-Wikidata Lean property checker.
-- No unreviewed text extraction, similarity or S29 status creates truth.
------------------------------------------------------------------------

record ConsumerFrame : Set where
  constructor frame
  field
    sourceRevision : String
    contextReference : String
    queryReference : String
    interpretationReference : String
    provenanceReference : String
open ConsumerFrame public

-- Query-local licence: operation and consumer observations agree under a
-- mapping. The licence is not global semantic equivalence.
record LicensedTransport
  (A B Outcome : Set)
  (observeA : A → Outcome)
  (observeB : B → Outcome) : Set where
  constructor licensed
  field
    forward : A → B
    preserve : (x : A) → observeB (forward x) ≡ observeA x
open LicensedTransport public

identityLicence :
  ∀ {A Outcome : Set} (observe : A → Outcome) →
  LicensedTransport A A observe observe
identityLicence observe = licensed (λ x → x) (λ x → refl)

composeLicence :
  ∀ {A B C Outcome : Set}
  {a : A → Outcome} {b : B → Outcome} {c : C → Outcome} →
  LicensedTransport A B a b →
  LicensedTransport B C b c →
  LicensedTransport A C a c
composeLicence f g =
  licensed
    (λ x → forward g (forward f x))
    (λ x → trans (preserve g (forward f x)) (preserve f x))

-- A licence preserves consumer equality, not necessarily source identity.
transportedConsumerEquality :
  ∀ {A B Outcome : Set}
  {a : A → Outcome} {b : B → Outcome} →
  (f : LicensedTransport A B a b) →
  ∀ x y → a x ≡ a y →
  b (forward f x) ≡ b (forward f y)
transportedConsumerEquality f x y same =
  trans (preserve f x)
    (trans same (symmetry (preserve f y)))
  where
    symmetry : ∀ {X : Set} {u v : X} → u ≡ v → v ≡ u
    symmetry refl = refl

-- Typed obligation state is an independent coordinate from support polarity.
data ObligationState : Set where
  discharged refuted missing outsideScope contested : ObligationState

data EvidencePolarity : Set where
  neither supports counters both : EvidencePolarity

record QualifiedObligation : Set where
  constructor qualified-obligation
  field
    operationReference : String
    contractReference : String
    witnessReferences : List String
    missingPremiseReferences : List String
    state : ObligationState
    polarity : EvidencePolarity
    provenanceReferences : List String
open QualifiedObligation public

-- A source-native observation and its interpretation stay separate.
record IndexedCandidate : Set where
  constructor indexed-candidate
  field
    sourceRevision : String
    spanOrStatementReference : String
    frameReference : String
    predicateReference : String
    roleReference : String
    qualifierReference : String
    assertionWrapperReference : String
    originalSourcePreserved : Bool
    candidateOnly : Bool
    semanticAuthorityCreated : Bool
open IndexedCandidate public

record ComparisonReceipt : Set where
  constructor comparison-receipt
  field
    left : IndexedCandidate
    right : IndexedCandidate
    consumerFrame : ConsumerFrame
    comparisonReference : String
    obligations : List QualifiedObligation
    sourceReopenReferences : List String
    requiresReview : Bool
    promotedClaimTruth : Bool
    createsEditAuthority : Bool
open ComparisonReceipt public

-- Evidence accumulation is append-only; admission and interpretation
-- revision are separate operations owned by downstream authorities.
record EvidenceLedger : Set where
  constructor ledger
  field
    supportReferences : List String
    counterReferences : List String
    missingReferences : List String
    provenanceReferences : List String
open EvidenceLedger public

addSupport : String → EvidenceLedger → EvidenceLedger
addSupport s e = ledger
  (s ∷ supportReferences e)
  (counterReferences e)
  (missingReferences e)
  (provenanceReferences e)
  where open import Agda.Builtin.List using (_∷_)

addCounter : String → EvidenceLedger → EvidenceLedger
addCounter s e = ledger
  (supportReferences e)
  (s ∷ counterReferences e)
  (missingReferences e)
  (provenanceReferences e)
  where open import Agda.Builtin.List using (_∷_)

counterUnchangedBySupport :
  ∀ s e → counterReferences (addSupport s e) ≡ counterReferences e
counterUnchangedBySupport s e = refl

supportUnchangedByCounter :
  ∀ s e → supportReferences (addCounter s e) ≡ supportReferences e
supportUnchangedByCounter s e = refl

-- A declared repair requires a *separate* consumer preservation witness.
record ConsumerBoundedRepair
  (State Outcome : Set)
  (consumer : State → Outcome) : Set where
  constructor consumer-bounded-repair
  field
    repair : State → State
    consumerPreservation : ∀ s → consumer (repair s) ≡ consumer s
    repairedObligationReference : String
    rerunObligationReferences : List String
open ConsumerBoundedRepair public

repairPreservesConsumerEquality :
  ∀ {State Outcome : Set}
  {consumer : State → Outcome} →
  (r : ConsumerBoundedRepair State Outcome consumer) →
  ∀ s t → consumer s ≡ consumer t →
  consumer (repair r s) ≡ consumer (repair r t)
repairPreservesConsumerEquality r s t same =
  trans (consumerPreservation r s)
    (trans same (symmetry (consumerPreservation r t)))
  where
    symmetry : ∀ {X : Set} {u v : X} → u ≡ v → v ≡ u
    symmetry refl = refl

-- Existing proofs remain the authority for interpretation-index collision
-- and consumer-sufficient residual refinement.
indexCountermodel :
  Indexed.OutputEqualityTransfersAcrossIndices Indexed.demoSystem → ⊥
indexCountermodel = Indexed.surfaceEqualityDoesNotSupplyCrossIndexLicence

consumerCollisionNecessity :
  ∀ {State Coarse Fine Outcome : Set}
  {coarse : State → Coarse}
  {fine : State → Fine}
  {consumer : State → Outcome} →
  (collision : Refinement.ConsumerRelevantCollision coarse consumer) →
  Refinement.ConsumerSufficient fine consumer →
  fine (Refinement.left collision) ≡ fine (Refinement.right collision) → ⊥
consumerCollisionNecessity =
  Refinement.everySufficientObserverSeparatesRelevantCollision
