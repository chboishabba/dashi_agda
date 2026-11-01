module DASHI.Biology.ParentalFearConsumerSufficiencyBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Biology.ParentalFearObserverRefinementExact as FearObserver
import DASHI.Biology.ParentalFearSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- Source calibration:
-- Justen O'Connor and Alice Brown (2013),
-- "A qualitative study of 'fear' as a regulator of children's independent
-- physical activity in the suburbs", Health & Place 24, 157-164.
-- DOI: 10.1016/j.healthplace.2013.09.002.
--
-- DASHI extension:
-- The earlier parental-fear observer module constructs a collision under the
-- coarse fear observer and a separation under intervention need.  This module
-- does not redefine descent.  It instantiates the repository owner
-- ConsumerDescentMinimalObserverExact, so the paper bridge participates in the
-- same consumer-relative sufficiency language used elsewhere in DASHI.
------------------------------------------------------------------------

fearInterventionNonDescentWitness :
  Consumer.ConsumerNonDescentWitness
    FearObserver.fearOnlyObserver
    FearObserver.interventionNeed
fearInterventionNonDescentWitness =
  Consumer.consumerNonDescentWitness
    FearObserver.capabilityLimited
    FearObserver.guardianNetworkLimited
    FearObserver.sameCoarseFear
    FearObserver.interventionNeedsDiffer

fearOnlyNotConsumerSufficient :
  Consumer.ConsumerSufficient
    FearObserver.fearOnlyObserver
    FearObserver.interventionNeed →
  ⊥
fearOnlyNotConsumerSufficient =
  Consumer.nonDescentWitnessBlocksSufficiency fearInterventionNonDescentWitness

fearOnlyDoesNotFactorInterventionNeed :
  Consumer.FactorsThrough
    FearObserver.fearOnlyObserver
    FearObserver.interventionNeed →
  ⊥
fearOnlyDoesNotFactorInterventionNeed =
  Consumer.nonDescentWitnessBlocksFactorization fearInterventionNonDescentWitness

interventionNeedObserverIsLeastSufficient :
  Consumer.LeastSufficientConsumerObserver FearObserver.interventionNeed
interventionNeedObserverIsLeastSufficient =
  Consumer.canonicalConsumerObserverIsLeast FearObserver.interventionNeed

record ParentalFearConsumerSufficiencyBridge : Set₁ where
  constructor mkParentalFearConsumerSufficiencyBridge
  field
    attribution : Attribution.ParentalFearSourceAttribution
    attributionIsCanonical :
      attribution ≡ Attribution.canonicalParentalFearSourceAttribution
    nonDescentWitnessReusesGenericOwner : Bool
    nonDescentWitnessReusesGenericOwnerIsTrue :
      nonDescentWitnessReusesGenericOwner ≡ true
    fearOnlyFailsDeclaredConsumerSufficiency : Bool
    fearOnlyFailsDeclaredConsumerSufficiencyIsTrue :
      fearOnlyFailsDeclaredConsumerSufficiency ≡ true
    fearOnlyFactorizationBlocked : Bool
    fearOnlyFactorizationBlockedIsTrue :
      fearOnlyFactorizationBlocked ≡ true
    consumerObserverLeastSufficientConstructed : Bool
    consumerObserverLeastSufficientConstructedIsTrue :
      consumerObserverLeastSufficientConstructed ≡ true
    sufficiencyIsConsumerRelativeNotWorldComplete : Bool
    sufficiencyIsConsumerRelativeNotWorldCompleteIsTrue :
      sufficiencyIsConsumerRelativeNotWorldComplete ≡ true
    sourceClaimSeparatedFromDashiTheorem : Bool
    sourceClaimSeparatedFromDashiTheoremIsTrue :
      sourceClaimSeparatedFromDashiTheorem ≡ true
    reading : String

open ParentalFearConsumerSufficiencyBridge public

canonicalParentalFearConsumerSufficiencyBridge :
  ParentalFearConsumerSufficiencyBridge
canonicalParentalFearConsumerSufficiencyBridge =
  mkParentalFearConsumerSufficiencyBridge
    Attribution.canonicalParentalFearSourceAttribution refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    "DASHI extension: the existing consumer-descent core classifies the parental-fear collision as a genuine insufficiency result. Equal coarse fear observations do not force equal intervention-need outcomes, so fear alone is not sufficient for that declared consumer and no factorization through the fear quotient exists. The result is consumer-relative and does not claim a universally sufficient parenting ontology."
