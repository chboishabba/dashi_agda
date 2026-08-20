module DASHI.Cognition.PNF.DependencyIndexedOwnerWakeupExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)

------------------------------------------------------------------------
-- Sparse owner invalidation.
--
-- A reduced factor changing physical producer does not by itself justify a
-- consumer wake-up. Consumers observe factor AVAILABILITY. The reverse index
-- therefore follows exactly those factor refs whose availability flips and
-- exactly those owners whose admitted proposals declare such a dependency.
------------------------------------------------------------------------

record ReverseDependencyIndex (Owner Factor : Set) : Set₁ where
  field
    requires : Owner → Factor → Set
    successor : Factor → Owner → Set
    exact : ∀ factor owner → successor factor owner ≡ requires owner factor

open ReverseDependencyIndex public

record AvailabilityDelta (Factor : Set) : Set₁ where
  field
    changed : Factor → Set

open AvailabilityDelta public

record ExactSparseWakeup
  (Owner Factor : Set)
  (index : ReverseDependencyIndex Owner Factor)
  (delta : AvailabilityDelta Factor)
  : Set₁ where
  field
    wake : Owner → Set
    wakeExact :
      ∀ owner →
      wake owner
      ≡
      Σ Factor (λ factor →
        Σ (changed delta factor) (λ _ → requires index owner factor))

open ExactSparseWakeup public

indexedWakeupHasNoUnindexedOwners :
  ∀ {Owner Factor : Set}
    {index : ReverseDependencyIndex Owner Factor}
    {delta : AvailabilityDelta Factor}
    (certificate : ExactSparseWakeup Owner Factor index delta)
    (owner : Owner) →
  wake certificate owner
  ≡
  Σ Factor (λ factor →
    Σ (changed delta factor) (λ _ → requires index owner factor))
indexedWakeupHasNoUnindexedOwners certificate owner =
  wakeExact certificate owner

------------------------------------------------------------------------
-- Producer multiplicity boundary.
--
-- Physical producer churn is intentionally separate from consumer-visible
-- availability. An implementation must prove this projection before using a
-- producer-set edit as the changed relation above.
------------------------------------------------------------------------

record ProducerMultiplicityProjection (Owner Factor : Set) : Set₁ where
  field
    producedBy : Factor → Owner → Set
    available : Factor → Set
    availabilityIffProducer :
      ∀ factor →
      available factor ≡ Σ Owner (λ owner → producedBy factor owner)

open ProducerMultiplicityProjection public

------------------------------------------------------------------------
-- Candidate-target provenance dependencies.
--
-- A represented candidate is not only dependent on its demand-level index key;
-- it is also dependent on the provenance atoms supporting the represented
-- target.  If target t is currently a candidate for demand d and atom a supports
-- t, then a change to a may need to reopen d.  This is the formal seam used by
-- the runtime's token -> object/factor target -> demand reverse index.
------------------------------------------------------------------------

record CandidateTargetSupportIndex
  (Demand Target Atom : Set)
  : Set₁ where
  field
    representedCandidate : Demand → Target → Set
    targetSupportedBy : Target → Atom → Set
    reverseTargetDependency : Atom → Demand → Set
    reverseTargetExact :
      ∀ atom demand →
      reverseTargetDependency atom demand
      ≡
      Σ Target (λ target →
        Σ (representedCandidate demand target) (λ _ →
          targetSupportedBy target atom))

open CandidateTargetSupportIndex public

candidateTargetReverseIndexIsExact :
  ∀ {Demand Target Atom : Set}
    (index : CandidateTargetSupportIndex Demand Target Atom)
    (atom : Atom)
    (demand : Demand) →
  reverseTargetDependency index atom demand
  ≡
  Σ Target (λ target →
    Σ (representedCandidate index demand target) (λ _ →
      targetSupportedBy index target atom))
candidateTargetReverseIndexIsExact index atom demand =
  reverseTargetExact index atom demand

------------------------------------------------------------------------
-- Sound over-wake boundary.
--
-- Exact reverse indexes are desirable for precision, but incremental semantic
-- soundness requires only that every dependency which CAN affect a consumer is
-- present in the wake index. Extra stale edges may do unnecessary work; a
-- missing required edge can suppress necessary reopening. This permits a
-- conservative implementation to delay exact deletion/reference counting
-- without turning absence of an index row into semantic evidence.
------------------------------------------------------------------------

record SoundReverseDependency (Atom Demand : Set) : Set₁ where
  field
    requiredWake : Atom → Demand → Set
    indexedWake : Atom → Demand → Set
    noMissingRequiredWake :
      ∀ atom demand → requiredWake atom demand → indexedWake atom demand

open SoundReverseDependency public

requiredWakeCannotBeMissing :
  ∀ {Atom Demand : Set}
    (index : SoundReverseDependency Atom Demand)
    (atom : Atom)
    (demand : Demand) →
  requiredWake index atom demand → indexedWake index atom demand
requiredWakeCannotBeMissing index atom demand =
  noMissingRequiredWake index atom demand
