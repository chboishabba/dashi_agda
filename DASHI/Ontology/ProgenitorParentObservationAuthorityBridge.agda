module DASHI.Ontology.ProgenitorParentObservationAuthorityBridge where

open import DASHI.Core.Prelude using (Bool; true; false; _≡_; refl; ⊥)
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.ConsumerIndexedRelevanceMeasure as Relevance
import DASHI.Cognition.PNF.ProofRelevantIdentityFibres as Identity

open import DASHI.Ontology.ProgenitorParentHyperfabric
open import DASHI.Ontology.ProgenitorParentProjectionFibre
open import DASHI.Ontology.ProgenitorParentObserverDynamicsBridge

data DisclosureVariant : Set where
  hiddenDonor disclosedDonor : DisclosureVariant

variantCarrier : DisclosureVariant → ParentCarrier
variantCarrier hiddenDonor = anonymousDonorCarrier
variantCarrier disclosedDonor = anonymousDonorDisclosableCarrier

variantDisclosureObserver : Observer.Observer DisclosureVariant Bool
variantDisclosureObserver variant =
  identityDisclosable (carrierRelation (variantCarrier variant))

variantDisclosureObserverSeparating :
  Observer.Separating variantDisclosureObserver
variantDisclosureObserverSeparating hiddenDonor hiddenDonor equality = refl
variantDisclosureObserverSeparating hiddenDonor disclosedDonor ()
variantDisclosureObserverSeparating disclosedDonor hiddenDonor ()
variantDisclosureObserverSeparating disclosedDonor disclosedDonor equality = refl

separatingObserverDoesNotGrantSurfaceWorldIdentity :
  Identity.WorldCanonicalPermission Identity.surfaceLocal → ⊥
separatingObserverDoesNotGrantSurfaceWorldIdentity =
  Identity.surfaceIdentityCannotClaimWorldIdentity

knownDisclosableStateDoesNotGrantSurfaceWorldIdentity :
  identityKnown anonymousDonorDisclosableRelation ≡ true
  × identityDisclosable anonymousDonorDisclosableRelation ≡ true
  × (Identity.WorldCanonicalPermission Identity.surfaceLocal → ⊥)
knownDisclosableStateDoesNotGrantSurfaceWorldIdentity =
  refl , (refl , Identity.surfaceIdentityCannotClaimWorldIdentity)

consumerRelevanceCannotPromoteWorldTruth :
  Relevance.NormalizedMassWorldTruthPermission → ⊥
consumerRelevanceCannotPromoteWorldTruth =
  Relevance.normalizedMassCannotAssertWorldTruth

consumerNormalizationCannotProveObserverUniverseComplete :
  Relevance.CandidateNormalizationCompletenessPermission → ⊥
consumerNormalizationCannotProveObserverUniverseComplete =
  Relevance.candidateWeightsSummingToUnitCannotProveUniverseComplete

record ParentObservationAuthorityBoundary : Set where
  constructor parentObservationAuthorityBoundary
  field
    disclosureObserverSeparatingOnWitnessFibre : Bool
    disclosureObserverSeparatingOnWitnessFibreIsTrue :
      disclosureObserverSeparatingOnWitnessFibre ≡ true
    separatingDoesNotGrantWorldIdentityAuthority : Bool
    separatingDoesNotGrantWorldIdentityAuthorityIsTrue :
      separatingDoesNotGrantWorldIdentityAuthority ≡ true
    stateDisclosureFlagDoesNotGrantWorldIdentityAuthority : Bool
    stateDisclosureFlagDoesNotGrantWorldIdentityAuthorityIsTrue :
      stateDisclosureFlagDoesNotGrantWorldIdentityAuthority ≡ true
    relevanceNormalizationDoesNotGrantWorldTruth : Bool
    relevanceNormalizationDoesNotGrantWorldTruthIsTrue :
      relevanceNormalizationDoesNotGrantWorldTruth ≡ true

canonicalParentObservationAuthorityBoundary : ParentObservationAuthorityBoundary
canonicalParentObservationAuthorityBoundary =
  parentObservationAuthorityBoundary true refl true refl true refl true refl
