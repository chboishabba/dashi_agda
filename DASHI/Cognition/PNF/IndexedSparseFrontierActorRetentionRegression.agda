module DASHI.Cognition.PNF.IndexedSparseFrontierActorRetentionRegression where

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Cognition.PNF.IndexedSparseFrontierActorRetentionExact

factor objectKind role : Nat
factor = 11
objectKind = 22
role = 33

profile : RetainedActorProfile
profile = retainedActorProfile factor objectKind role

constrainedDemand : ActorRetentionDemand
constrainedDemand =
  actorRetentionDemand
    (just factor)
    (just objectKind)
    (just role)

constrainedRetention : IndexedActorRetention constrainedDemand profile
constrainedRetention =
  indexedActorRetention
    (actorRetentionConstraintWitness
      (requiredEquals refl)
      (requiredEquals refl)
      (requiredEquals refl))

constrainedLegacyParity :
  legacyToIndexed (indexedToLegacy constrainedRetention)
    ≡ constrainedRetention
constrainedLegacyParity = indexedLegacyRoundTrip constrainedRetention

wildcardRetention :
  IndexedActorRetention allWildcardRetentionDemand profile
wildcardRetention = allWildcardRetentionMatchesEveryProfile profile
