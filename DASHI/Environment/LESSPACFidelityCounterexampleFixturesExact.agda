module DASHI.Environment.LESSPACFidelityCounterexampleFixturesExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerRelativeReductionSearchExact as Search
import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction

------------------------------------------------------------------------
-- FINITE FIDELITY COUNTEREXAMPLE FIXTURES
--
-- These are synthetic theorem fixtures, not empirical site data.  They encode
-- the three distinctions the physical LES stack says progressively richer
-- models may need to retain:
--
--   bucket -> Richards              : soil hydraulic profile / conductivity
--   Richards -> hydraulic SPAC      : plant hydraulic history / vulnerability
--   hydraulic SPAC -> electro/bio   : nutrient / electrochemical state
--
-- The purpose is proof-search regression: a cheap candidate is rejected only
-- by an explicit consumer-future collision, never merely because a richer model
-- exists.
------------------------------------------------------------------------

data Probe : Set where
  stressPulse : Probe

data FineState : Set where
  soilFast soilSlow
  soilFastAfter soilSlowAfter
  plantIntact plantVulnerable
  plantIntactAfter plantVulnerableAfter
  nutrientReplete nutrientLimited
  nutrientRepleteAfter nutrientLimitedAfter
  : FineState

data Observation : Set where
  baseline
  fastDrain slowDrain
  intactResponse vulnerableResponse
  nutrientRepleteResponse nutrientLimitedResponse
  : Observation

fineStep : Probe → FineState → FineState
fineStep stressPulse soilFast = soilFastAfter
fineStep stressPulse soilSlow = soilSlowAfter
fineStep stressPulse plantIntact = plantIntactAfter
fineStep stressPulse plantVulnerable = plantVulnerableAfter
fineStep stressPulse nutrientReplete = nutrientRepleteAfter
fineStep stressPulse nutrientLimited = nutrientLimitedAfter
fineStep stressPulse state = state

observe : FineState → Observation
observe soilFast = baseline
observe soilSlow = baseline
observe plantIntact = baseline
observe plantVulnerable = baseline
observe nutrientReplete = baseline
observe nutrientLimited = baseline
observe soilFastAfter = fastDrain
observe soilSlowAfter = slowDrain
observe plantIntactAfter = intactResponse
observe plantVulnerableAfter = vulnerableResponse
observe nutrientRepleteAfter = nutrientRepleteResponse
observe nutrientLimitedAfter = nutrientLimitedResponse

------------------------------------------------------------------------
-- Candidate codes.
------------------------------------------------------------------------

data BucketCode : Set where
  bucketSame : BucketCode

data RichardsCode : Set where
  richardsFast richardsSlow richardsOther : RichardsCode

data SPACCode : Set where
  spacIntact spacVulnerable spacOther : SPACCode

data ElectroBioCode : Set where
  electroReplete electroLimited electroOther : ElectroBioCode

bucketProject : FineState → BucketCode
bucketProject state = bucketSame

richardsProject : FineState → RichardsCode
richardsProject soilFast = richardsFast
richardsProject soilFastAfter = richardsFast
richardsProject soilSlow = richardsSlow
richardsProject soilSlowAfter = richardsSlow
richardsProject state = richardsOther

spacProject : FineState → SPACCode
spacProject plantIntact = spacIntact
spacProject plantIntactAfter = spacIntact
spacProject plantVulnerable = spacVulnerable
spacProject plantVulnerableAfter = spacVulnerable
spacProject state = spacOther

electroBioProject : FineState → ElectroBioCode
electroBioProject nutrientReplete = electroReplete
electroBioProject nutrientRepleteAfter = electroReplete
electroBioProject nutrientLimited = electroLimited
electroBioProject nutrientLimitedAfter = electroLimited
electroBioProject state = electroOther

bucketCandidate : Search.ReductionCandidate FineState Probe Observation fineStep observe
bucketCandidate =
  Search.reductionCandidate
    BucketCode bucketProject
    "empirical water-balance candidate"
    zero
    "lowest declared fidelity"
    "soil profile, plant history and nutrient state omitted"
    "synthetic proof fixture only"

richardsCandidate : Search.ReductionCandidate FineState Probe Observation fineStep observe
richardsCandidate =
  Search.reductionCandidate
    RichardsCode richardsProject
    "Richards soil-hydraulic candidate"
    (suc zero)
    "soil hydraulic state retained"
    "plant hydraulic history and nutrient state omitted"
    "synthetic proof fixture only"

spacCandidate : Search.ReductionCandidate FineState Probe Observation fineStep observe
spacCandidate =
  Search.reductionCandidate
    SPACCode spacProject
    "hydraulic SPAC candidate"
    (suc (suc zero))
    "plant hydraulic state retained"
    "electrochemical/nutrient state omitted"
    "synthetic proof fixture only"

electroBioCandidate : Search.ReductionCandidate FineState Probe Observation fineStep observe
electroBioCandidate =
  Search.reductionCandidate
    ElectroBioCode electroBioProject
    "electro-biogeochemical SPAC candidate"
    (suc (suc (suc zero)))
    "nutrient/electrochemical distinction retained"
    "fixture does not claim full physical completeness"
    "synthetic proof fixture only"

------------------------------------------------------------------------
-- Tier 0 failure: bucket collapses a soil-hydraulic distinction that one stress
-- pulse exposes to the consumer.  Richards retains that distinction.
------------------------------------------------------------------------

bucketSoilCollision : bucketProject soilFast ≡ bucketProject soilSlow
bucketSoilCollision = refl

richardsSeparatesSoilPair :
  richardsProject soilFast ≡ richardsProject soilSlow → ⊥
richardsSeparatesSoilPair ()

bucketFutureSeparates :
  observe (Reduction.run fineStep (stressPulse ∷ []) soilFast)
  ≡ observe (Reduction.run fineStep (stressPulse ∷ []) soilSlow) → ⊥
bucketFutureSeparates ()

bucketRefutation : Search.CandidateRefutation bucketCandidate
bucketRefutation =
  Reduction.candidateReductionFailure
    soilFast soilSlow bucketSoilCollision
    (stressPulse ∷ [])
    bucketFutureSeparates

------------------------------------------------------------------------
-- Tier 1 failure: a soil-only code collapses distinct plant hydraulic histories.
-- The hydraulic-SPAC code retains the distinction.
------------------------------------------------------------------------

richardsPlantCollision :
  richardsProject plantIntact ≡ richardsProject plantVulnerable
richardsPlantCollision = refl

spacSeparatesPlantPair :
  spacProject plantIntact ≡ spacProject plantVulnerable → ⊥
spacSeparatesPlantPair ()

richardsPlantFutureSeparates :
  observe (Reduction.run fineStep (stressPulse ∷ []) plantIntact)
  ≡ observe (Reduction.run fineStep (stressPulse ∷ []) plantVulnerable) → ⊥
richardsPlantFutureSeparates ()

richardsRefutation : Search.CandidateRefutation richardsCandidate
richardsRefutation =
  Reduction.candidateReductionFailure
    plantIntact plantVulnerable richardsPlantCollision
    (stressPulse ∷ [])
    richardsPlantFutureSeparates

------------------------------------------------------------------------
-- Tier 2 failure: hydraulic SPAC collapses a nutrient/electrochemical state
-- distinction that matters after the declared stress.  The electro/bio code
-- retains it.
------------------------------------------------------------------------

spacNutrientCollision :
  spacProject nutrientReplete ≡ spacProject nutrientLimited
spacNutrientCollision = refl

electroBioSeparatesNutrientPair :
  electroBioProject nutrientReplete ≡ electroBioProject nutrientLimited → ⊥
electroBioSeparatesNutrientPair ()

spacNutrientFutureSeparates :
  observe (Reduction.run fineStep (stressPulse ∷ []) nutrientReplete)
  ≡ observe (Reduction.run fineStep (stressPulse ∷ []) nutrientLimited) → ⊥
spacNutrientFutureSeparates ()

spacRefutation : Search.CandidateRefutation spacCandidate
spacRefutation =
  Reduction.candidateReductionFailure
    nutrientReplete nutrientLimited spacNutrientCollision
    (stressPulse ∷ [])
    spacNutrientFutureSeparates

------------------------------------------------------------------------
-- Regression boundary.
------------------------------------------------------------------------

record SPACFidelityCounterexampleBoundary : Set where
  constructor spacFidelityCounterexampleBoundary
  field
    bucketCanEraseHydraulicConsumerDistinction : Bool
    richardsCanErasePlantHistoryConsumerDistinction : Bool
    hydraulicSPACCanEraseNutrientConsumerDistinction : Bool
    richerTierExistenceAloneRefutesCheaperTier : Bool
    richerTierExistenceAloneRefutesCheaperTierIsFalse :
      richerTierExistenceAloneRefutesCheaperTier ≡ false
    fixturesAreEmpiricalValidationData : Bool
    fixturesAreEmpiricalValidationDataIsFalse :
      fixturesAreEmpiricalValidationData ≡ false

canonicalSPACFidelityCounterexampleBoundary : SPACFidelityCounterexampleBoundary
canonicalSPACFidelityCounterexampleBoundary =
  spacFidelityCounterexampleBoundary true true true false refl false refl
