module DASHI.Cognition.PNF.IndexedSparseFrontierObjectCandidateRegression where

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Cognition.PNF.IndexedSparseFrontierObjectCandidateExact

factor objectKind head predicate role : Nat
factor = 11
objectKind = 22
head = 33
predicate = 44
role = 55

profile : ActorProfileKeys
profile = actorProfileKeys factor objectKind head predicate role

headDemand : ObjectDemandKeys
headDemand =
  objectDemandKeys
    (just factor)
    (just objectKind)
    (just head)
    (just role)

predicateDemand : ObjectDemandKeys
predicateDemand =
  objectDemandKeys
    (just factor)
    (just objectKind)
    (just predicate)
    (just role)

headCandidate : IndexedObjectCandidate headDemand profile
headCandidate =
  indexedObjectCandidate
    (objectCandidateConstraintWitness
      (requiredEquals refl)
      (requiredEquals refl)
      (lexicalMatchesHead refl)
      (requiredEquals refl))

predicateCandidate : IndexedObjectCandidate predicateDemand profile
predicateCandidate =
  indexedObjectCandidate
    (objectCandidateConstraintWitness
      (requiredEquals refl)
      (requiredEquals refl)
      (lexicalMatchesPredicate refl)
      (requiredEquals refl))

headCandidateLegacyParity :
  legacyToIndexed (indexedToLegacy headCandidate) ≡ headCandidate
headCandidateLegacyParity = indexedLegacyRoundTrip headCandidate

predicateCandidateLegacyParity :
  legacyToIndexed (indexedToLegacy predicateCandidate) ≡ predicateCandidate
predicateCandidateLegacyParity = indexedLegacyRoundTrip predicateCandidate

wildcardCandidate : IndexedObjectCandidate allWildcardDemand profile
wildcardCandidate = allWildcardMatchesEveryProfile profile
