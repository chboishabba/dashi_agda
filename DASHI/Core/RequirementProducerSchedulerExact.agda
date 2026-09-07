module DASHI.Core.RequirementProducerSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- REQUIREMENT -> MISSING COORDINATE -> PRODUCER SCHEDULER
--
-- DASHI-original generic machinery.  It does not prescribe a Bayesian or
-- utility-theoretic scheduler.  Applications provide requirement predicates,
-- current closure status, producer identity and salience evidence explicitly.
------------------------------------------------------------------------

record RequirementSystem : Set₁ where
  constructor requirement-system
  field
    Question Coordinate Producer : Set
    requiredFor : Question → Coordinate → Bool
    closed : Coordinate → Bool
    producerFor : Coordinate → Producer
    requirementReference : String
    producerReference : String

open RequirementSystem public

MissingFor : RequirementSystem → Question _ → Coordinate _ → Set
MissingFor sys q c =
  (requiredFor sys q c ≡ true) × (closed sys c ≡ false)

record MissingCoordinateReceipt
    (sys : RequirementSystem)
    (q : Question sys) : Set₁ where
  constructor missing-coordinate-receipt
  field
    coordinate : Coordinate sys
    missing : MissingFor sys q coordinate

open MissingCoordinateReceipt public

scheduledProducer :
  ∀ {sys : RequirementSystem} {q : Question sys} →
  MissingCoordinateReceipt sys q → Producer sys
scheduledProducer {sys} receipt = producerFor sys (coordinate receipt)

------------------------------------------------------------------------
-- Salience is consumer-relative and independently evidenced.
------------------------------------------------------------------------

record ProducerSalience
    (sys : RequirementSystem)
    (q : Question sys)
    (receipt : MissingCoordinateReceipt sys q) : Set₁ where
  constructor producer-salience
  field
    Cost ExpectedReduction AuthorityAdmissibility : Set
    cost : Cost
    expectedReduction : ExpectedReduction
    authorityAdmissibility : AuthorityAdmissibility
    salienceReference : String

open ProducerSalience public

record ScheduledRequirement
    (sys : RequirementSystem)
    (q : Question sys) : Set₁ where
  constructor scheduled-requirement
  field
    missingReceipt : MissingCoordinateReceipt sys q
    salience : ProducerSalience sys q missingReceipt
    scheduleReference : String

open ScheduledRequirement public

nextProducer :
  ∀ {sys : RequirementSystem} {q : Question sys} →
  ScheduledRequirement sys q → Producer sys
nextProducer {sys} scheduled = scheduledProducer (missingReceipt scheduled)

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RequiredImpliesClosedPermission : Set where

data MissingImpliesHighestSaliencePermission : Set where

data CheapestImpliesMostInformativePermission : Set where

data MostInformativeImpliesAuthorityAdmissiblePermission : Set where

data ProducerExistenceImpliesCoordinateClosedPermission : Set where

requiredDoesNotAutoPromoteToClosed : RequiredImpliesClosedPermission → ⊥
requiredDoesNotAutoPromoteToClosed ()

missingDoesNotAutoPromoteToHighestSalience : MissingImpliesHighestSaliencePermission → ⊥
missingDoesNotAutoPromoteToHighestSalience ()

cheapestDoesNotAutoPromoteToMostInformative : CheapestImpliesMostInformativePermission → ⊥
cheapestDoesNotAutoPromoteToMostInformative ()

mostInformativeDoesNotAutoPromoteToAuthorityAdmissible :
  MostInformativeImpliesAuthorityAdmissiblePermission → ⊥
mostInformativeDoesNotAutoPromoteToAuthorityAdmissible ()

producerExistenceDoesNotAutoCloseCoordinate :
  ProducerExistenceImpliesCoordinateClosedPermission → ⊥
producerExistenceDoesNotAutoCloseCoordinate ()

record RequirementProducerSchedulerBoundary : Set where
  constructor requirement-producer-scheduler-boundary
  field
    schedulingIsConsumerRelative : Bool
    schedulingIsConsumerRelativeIsTrue : schedulingIsConsumerRelative ≡ true
    everyMissingRequirementHasSamePriority : Bool
    everyMissingRequirementHasSamePriorityIsFalse :
      everyMissingRequirementHasSamePriority ≡ false
    producerIdentityAloneClosesRequirement : Bool
    producerIdentityAloneClosesRequirementIsFalse :
      producerIdentityAloneClosesRequirement ≡ false

canonicalRequirementProducerSchedulerBoundary : RequirementProducerSchedulerBoundary
canonicalRequirementProducerSchedulerBoundary =
  requirement-producer-scheduler-boundary true refl false refl false refl
