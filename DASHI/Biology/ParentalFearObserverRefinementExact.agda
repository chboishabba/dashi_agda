module DASHI.Biology.ParentalFearObserverRefinementExact where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Biology.ParentalFearIndependentMobilityExact as Fear
import DASHI.Biology.ParentalFearSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- DASHI cross-pollination: coarse fear observation versus situated,
-- intervention-relevant context.
--
-- Source calibration:
--   O'Connor, Justen; Brown, Alice (2013),
--   "A qualitative study of 'fear' as a regulator of children's independent
--   physical activity in the suburbs", Health & Place 24, 157-164.
--   DOI 10.1016/j.healthplace.2013.09.002.
--
-- Source-supported premise:
--   the study reports that parents can share a coarse fear / anxiety surface
--   while the relevant mediating circumstances differ: child skills and
--   capabilities, community connectivity / potential guardians, route and
--   infrastructure, biographies, bodily responses, and other situated factors.
--
-- DASHI extension:
--   we instantiate the repository's generic observer-refinement machinery to
--   prove a finite witness that a fear-only observation can fail to determine
--   an intervention-relevant distinction.  This is not a claim that the paper
--   experimentally compared the two synthetic witness states below, nor that
--   either intervention is universally optimal.
------------------------------------------------------------------------

data CoarseFearObservation : Set where
  elevatedFear : CoarseFearObservation

-- Two deliberately minimal witness states with the same coarse fear label but
-- different intervention-relevant context.
data IASTWitnessState : Set where
  capabilityLimited : IASTWitnessState
  guardianNetworkLimited : IASTWitnessState

fearOnlyObserver : Observer.Observer IASTWitnessState CoarseFearObservation
fearOnlyObserver capabilityLimited = elevatedFear
fearOnlyObserver guardianNetworkLimited = elevatedFear

data InterventionRelevantContext : Set where
  childCapabilityContext : InterventionRelevantContext
  communityConnectivityContext : InterventionRelevantContext

contextObserver :
  Observer.Observer IASTWitnessState InterventionRelevantContext
contextObserver capabilityLimited = childCapabilityContext
contextObserver guardianNetworkLimited = communityConnectivityContext

sameCoarseFear :
  fearOnlyObserver capabilityLimited
  ≡ fearOnlyObserver guardianNetworkLimited
sameCoarseFear = refl

contextSeparates :
  contextObserver capabilityLimited
  ≡ contextObserver guardianNetworkLimited →
  ⊥
contextSeparates ()

fearPlusContextStrictlyRefinesFearOnly :
  Observer.StrictRefinement
    fearOnlyObserver
    (Observer.pairObserver fearOnlyObserver contextObserver)
fearPlusContextStrictlyRefinesFearOnly =
  Observer.strictPairRefinement
    fearOnlyObserver
    contextObserver
    capabilityLimited
    guardianNetworkLimited
    sameCoarseFear
    contextSeparates

------------------------------------------------------------------------
-- Intervention need does not descend through the coarse fear quotient.
--
-- The intervention names mirror strategy families reported in the paper:
-- skill/capability development and broader social-network / guardian support.
-- They are typed needs for this finite witness, not prescriptive clinical or
-- parenting recommendations.
------------------------------------------------------------------------

data InterventionNeed : Set where
  developChildSkillsNeed : InterventionNeed
  broadenGuardianNetworkNeed : InterventionNeed

interventionNeed : IASTWitnessState → InterventionNeed
interventionNeed capabilityLimited = developChildSkillsNeed
interventionNeed guardianNetworkLimited = broadenGuardianNetworkNeed

interventionNeedsDiffer :
  interventionNeed capabilityLimited
  ≡ interventionNeed guardianNetworkLimited →
  ⊥
interventionNeedsDiffer ()

FearOnlyInterventionReconstruction : Set
FearOnlyInterventionReconstruction =
  Σ (CoarseFearObservation → InterventionNeed)
    (λ reconstruct →
      ∀ state →
      reconstruct (fearOnlyObserver state) ≡ interventionNeed state)

fearOnlyObservationCannotDetermineInterventionNeed :
  FearOnlyInterventionReconstruction → ⊥
fearOnlyObservationCannotDetermineInterventionNeed reconstruction =
  interventionNeedsDiffer
    (trans
      (sym (commutes capabilityLimited))
      (commutes guardianNetworkLimited))
  where
    reconstruct = proj₁ reconstruction
    commutes = proj₂ reconstruction

------------------------------------------------------------------------
-- Source and boundary receipt.
------------------------------------------------------------------------

record ParentalFearObserverRefinementBridge : Set where
  constructor mkParentalFearObserverRefinementBridge
  field
    sourceFormalisation : Fear.ParentalFearIndependentMobilitySource
    sourceFormalisationIsCanonical :
      sourceFormalisation ≡ Fear.canonicalParentalFearIndependentMobilitySource
    attribution : Attribution.ParentalFearSourceAttribution
    attributionIsCanonical :
      attribution ≡ Attribution.canonicalParentalFearSourceAttribution
    coarseFearCollisionConstructed : Bool
    coarseFearCollisionConstructedIsTrue : coarseFearCollisionConstructed ≡ true
    strictContextRefinementConstructed : Bool
    strictContextRefinementConstructedIsTrue :
      strictContextRefinementConstructed ≡ true
    fearOnlyInterventionDescentBlocked : Bool
    fearOnlyInterventionDescentBlockedIsTrue :
      fearOnlyInterventionDescentBlocked ≡ true
    syntheticWitnessNotEmpiricalPair : Bool
    syntheticWitnessNotEmpiricalPairIsTrue :
      syntheticWitnessNotEmpiricalPair ≡ true
    interventionNeedNotUniversalPrescription : Bool
    interventionNeedNotUniversalPrescriptionIsTrue :
      interventionNeedNotUniversalPrescription ≡ true
    sourceClaimSeparatedFromDashiTheorem : Bool
    sourceClaimSeparatedFromDashiTheoremIsTrue :
      sourceClaimSeparatedFromDashiTheorem ≡ true
    reading : String

open ParentalFearObserverRefinementBridge public

canonicalParentalFearObserverRefinementBridge :
  ParentalFearObserverRefinementBridge
canonicalParentalFearObserverRefinementBridge =
  mkParentalFearObserverRefinementBridge
    Fear.canonicalParentalFearIndependentMobilitySource refl
    Attribution.canonicalParentalFearSourceAttribution refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    "DASHI extension: equal coarse fear labels can inhabit distinct situated context fibres, and the finite witness proves that an intervention-relevant distinction need not reconstruct from fear alone. The 2013 paper supplies the qualitative motivation and strategy families; the strict-refinement and non-descent theorem is repository mathematics, not a source-level empirical claim."
