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
