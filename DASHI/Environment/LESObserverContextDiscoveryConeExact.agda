module DASHI.Environment.LESObserverContextDiscoveryConeExact where

open import DASHI.Core.Prelude

import DASHI.Core.CounterexampleGuidedConsumerRefinementExact as CG
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core
import DASHI.Environment.LESObservationSourceRegistryExact as Sources

------------------------------------------------------------------------
-- OBSERVER-CONTEXT DISCOVERY CONE FOR LES
--
-- Source calibration:
--   Sources.holmgren2002 records Holmgren's Observe and Interact principle.
--   The mathematical constructions below are DASHI extensions.
--
-- Central separation:
--   representation adequacy is consumer-relative;
--   discovery adequacy is observer-context-relative.
--
-- If the current observer language collapses two worlds that a downstream
-- consumer must distinguish, no recharting of that language can repair the
-- loss.  A successful repair must enrich the observer so that the witnessed
-- worlds become observationally distinct.
------------------------------------------------------------------------

record ObserverContextHyperfabric : Set₁ where
  constructor observerContextHyperfabric
  field
    World : Set
    Context : Set
    Language : Context → Set
    observe : (context : Context) → World → Language context

open ObserverContextHyperfabric public

record DiscoveryConeExpansion
    {World Coarse Refined Output : Set}
    (coarse : World → Coarse)
    (refined : World → Refined)
    (consume : World → Output) : Set₁ where
  constructor discoveryConeExpansion
  field
    inadequacy : Core.ConsumerDescentDefect coarse consume
    refinement : CG.Refinement coarse refined
    split : CG.WitnessSplit inadequacy refined

open DiscoveryConeExpansion public

-- A successful discovery-cone expansion cannot itself be only a relabelling
-- of the old observer.  If it factors through the coarse observation, it cannot
-- split the witnessed collision.

successfulExpansionCannotFactorThroughOldObserver :
  ∀ {World Coarse Refined Output}
    {coarse : World → Coarse}
    {refined : World → Refined}
    {consume : World → Output} →
  (expansion : DiscoveryConeExpansion coarse refined consume) →
  (fromCoarse : Coarse → Refined) →
  ((state : World) → refined state ≡ fromCoarse (coarse state)) →
  ⊥
successfulExpansionCannotFactorThroughOldObserver expansion fromCoarse factors =
  CG.refinementThatFactorsThroughCoarseCannotSplitDefect
    (inadequacy expansion)
    _
    fromCoarse
    factors
    (split expansion)

------------------------------------------------------------------------
-- DIRT / SOIL PNF WITNESS
--
-- This is a repository-native finite witness, not an empirical pedology claim.
-- "Dirt" is used as the deliberately coarse observer surface.  "Soil" is a
-- richer consumer distinction in this specimen.  The theorem is not that the
-- English words have fixed scientific meanings; it is that a task-insufficient
-- observer cannot be repaired by downstream reweighting.
------------------------------------------------------------------------

data SoilWorld : Set where
  inertSubstrate livingRelationalSoil : SoilWorld

data DirtReading : Set where
  brownEarth : DirtReading

data SoilDistinction : Set where
  inertMaterial livingSystem : SoilDistinction

data SoilObserverContext : Set where
  dirtFrame soilFrame : SoilObserverContext

soilLanguage : SoilObserverContext → Set
soilLanguage dirtFrame = DirtReading
soilLanguage soilFrame = SoilDistinction

observeSoil : (context : SoilObserverContext) → SoilWorld → soilLanguage context
observeSoil dirtFrame inertSubstrate = brownEarth
observeSoil dirtFrame livingRelationalSoil = brownEarth
observeSoil soilFrame inertSubstrate = inertMaterial
observeSoil soilFrame livingRelationalSoil = livingSystem

soilObserverHyperfabric : ObserverContextHyperfabric
soilObserverHyperfabric =
  observerContextHyperfabric
    SoilWorld
    SoilObserverContext
    soilLanguage
    observeSoil

dirtProjection : SoilWorld → DirtReading
dirtProjection = observeSoil dirtFrame

soilProjection : SoilWorld → SoilDistinction
soilProjection = observeSoil soilFrame

-- In this finite witness the downstream consumer needs the richer distinction.
soilConsumer : SoilWorld → SoilDistinction
soilConsumer = soilProjection

dirtConsumerDefect : Core.ConsumerDescentDefect dirtProjection soilConsumer
dirtConsumerDefect =
  Core.consumerDescentDefect
    inertSubstrate
    livingRelationalSoil
    refl
    (λ ())

-- Therefore "dirt" is not a consumer-sufficient PNF for this declared
-- consumer.  It may still be sufficient for another consumer; no global claim
-- about the lexical category is made.

dirtCannotServeAsSoilConsumerPNF :
  Core.ConsumerDescent dirtProjection soilConsumer → ⊥
dirtCannotServeAsSoilConsumerPNF descent =
  Core.consumerDescentDefectContradictsDescent descent dirtConsumerDefect

forgetSoilDistinction : SoilDistinction → DirtReading
forgetSoilDistinction inertMaterial = brownEarth
forgetSoilDistinction livingSystem = brownEarth

soilRefinesDirt : CG.Refinement dirtProjection soilProjection
soilRefinesDirt =
  CG.refinement
    forgetSoilDistinction
    factorises
  where
    factorises : (state : SoilWorld) →
      dirtProjection state ≡ forgetSoilDistinction (soilProjection state)
    factorises inertSubstrate = refl
    factorises livingRelationalSoil = refl

soilProjectionSplitsDirtDefect :
  CG.WitnessSplit dirtConsumerDefect soilProjection
soilProjectionSplitsDirtDefect = CG.witnessSplit (λ ())

soilDiscoveryConeExpansion :
  DiscoveryConeExpansion dirtProjection soilProjection soilConsumer
soilDiscoveryConeExpansion =
  discoveryConeExpansion
    dirtConsumerDefect
    soilRefinesDirt
    soilProjectionSplitsDirtDefect

-- This is the exact finite form of "you cannot know what you do not know to
-- look for": once the current observer has collapsed the pair, no function of
-- that coarse reading can manufacture the missing living-system distinction.

noDirtRechartCanRecoverSoilDistinction :
  (rechart : DirtReading → SoilDistinction) →
  ((state : SoilWorld) → soilProjection state ≡ rechart (dirtProjection state)) →
  ⊥
noDirtRechartCanRecoverSoilDistinction rechart factors =
  successfulExpansionCannotFactorThroughOldObserver
    soilDiscoveryConeExpansion rechart factors

------------------------------------------------------------------------
-- UNKNOWN-UNKNOWN / OBSERVER-INadequacy SHAPE
--
-- A consumer collision witnesses something stronger than parameter uncertainty:
-- the declared observation language is missing a distinction required by that
-- consumer.  Counterexample-guided refinement supplies the positive repair
-- obligation while retaining the repo-wide boundary that one split does not
-- prove global future safety.
------------------------------------------------------------------------

soilCounterexampleGuidedRefinement :
  CG.CounterexampleGuidedRefinement dirtProjection soilConsumer
soilCounterexampleGuidedRefinement =
  CG.counterexampleGuidedRefinement
    dirtConsumerDefect
    soilProjection
    soilProjectionSplitsDirtDefect

record ObserverContextDiscoveryBoundary : Set where
  constructor observerContextDiscoveryBoundary
  field
    taskSufficientCompressionIsWorldIdentity : Bool
    taskSufficientCompressionIsWorldIdentityIsFalse :
      taskSufficientCompressionIsWorldIdentity ≡ false

    reweightingRecoversUnrepresentedDistinction : Bool
    reweightingRecoversUnrepresentedDistinctionIsFalse :
      reweightingRecoversUnrepresentedDistinction ≡ false

    oneWitnessSplitProvesGlobalObserverCompleteness : Bool
    oneWitnessSplitProvesGlobalObserverCompletenessIsFalse :
      oneWitnessSplitProvesGlobalObserverCompleteness ≡ false

    richerObserverIsIntrinsicallyMoreTrue : Bool
    richerObserverIsIntrinsicallyMoreTrueIsFalse :
      richerObserverIsIntrinsicallyMoreTrue ≡ false

    observerContextAndConsumerAreTheSameObject : Bool
    observerContextAndConsumerAreTheSameObjectIsFalse :
      observerContextAndConsumerAreTheSameObject ≡ false

canonicalObserverContextDiscoveryBoundary : ObserverContextDiscoveryBoundary
canonicalObserverContextDiscoveryBoundary =
  observerContextDiscoveryBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
