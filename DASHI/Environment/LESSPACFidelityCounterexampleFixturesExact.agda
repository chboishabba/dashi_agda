module DASHI.Environment.LESSPACFidelityCounterexampleFixturesExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerRelativeReductionSearchExact as Search
import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction

data Probe : Set where stressPulse : Probe

data FineState : Set where
  soilFast soilSlow soilFastAfter soilSlowAfter
  plantIntact plantVulnerable plantIntactAfter plantVulnerableAfter
  nutrientReplete nutrientLimited nutrientRepleteAfter nutrientLimitedAfter
  : FineState

data Observation : Set where
  baseline fastDrain slowDrain intactResponse vulnerableResponse
  nutrientRepleteResponse nutrientLimitedResponse : Observation

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

data BucketCode : Set where bucketSame : BucketCode

data RichardsCode : Set where richardsFast richardsSlow richardsOther : RichardsCode

data SPACCode : Set where spacIntact spacVulnerable spacOther : SPACCode

data ElectroBioCode : Set where electroReplete electroLimited electroOther : ElectroBioCode

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
bucketCandidate = Search.reductionCandidate BucketCode bucketProject "empirical water-balance candidate" zero "lowest declared fidelity" "soil profile, plant history and nutrient state omitted" "synthetic proof fixture only"

richardsCandidate : Search.ReductionCandidate FineState Probe Observation fineStep observe
richardsCandidate = Search.reductionCandidate RichardsCode richardsProject "Richards soil-hydraulic candidate" (suc zero) "soil hydraulic state retained" "plant hydraulic history and nutrient state omitted" "synthetic proof fixture only"

spacCandidate : Search.ReductionCandidate FineState Probe Observation fineStep observe
spacCandidate = Search.reductionCandidate SPACCode spacProject "hydraulic SPAC candidate" (suc (suc zero)) "plant hydraulic state retained" "electrochemical/nutrient state omitted" "synthetic proof fixture only"

electroBioCandidate : Search.ReductionCandidate FineState Probe Observation fineStep observe
electroBioCandidate = Search.reductionCandidate ElectroBioCode electroBioProject "electro-biogeochemical SPAC candidate" (suc (suc (suc zero))) "nutrient/electrochemical distinction retained" "fixture does not claim full physical completeness" "synthetic proof fixture only"

bucketRefutation : Search.CandidateRefutation bucketCandidate
bucketRefutation = Reduction.candidateReductionFailure soilFast soilSlow refl (stressPulse ∷ []) impossible
  where
    impossible : observe (Reduction.run fineStep (stressPulse ∷ []) soilFast) ≡ observe (Reduction.run fineStep (stressPulse ∷ []) soilSlow) → ⊥
    impossible ()

richardsRefutation : Search.CandidateRefutation richardsCandidate
richardsRefutation = Reduction.candidateReductionFailure plantIntact plantVulnerable refl (stressPulse ∷ []) impossible
  where
    impossible : observe (Reduction.run fineStep (stressPulse ∷ []) plantIntact) ≡ observe (Reduction.run fineStep (stressPulse ∷ []) plantVulnerable) → ⊥
    impossible ()

spacRefutation : Search.CandidateRefutation spacCandidate
spacRefutation = Reduction.candidateReductionFailure nutrientReplete nutrientLimited refl (stressPulse ∷ []) impossible
  where
    impossible : observe (Reduction.run fineStep (stressPulse ∷ []) nutrientReplete) ≡ observe (Reduction.run fineStep (stressPulse ∷ []) nutrientLimited) → ⊥
    impossible ()

richardsSeparatesSoilPair : richardsProject soilFast ≡ richardsProject soilSlow → ⊥
richardsSeparatesSoilPair ()

spacSeparatesPlantPair : spacProject plantIntact ≡ spacProject plantVulnerable → ⊥
spacSeparatesPlantPair ()

electroBioSeparatesNutrientPair : electroBioProject nutrientReplete ≡ electroBioProject nutrientLimited → ⊥
electroBioSeparatesNutrientPair ()

record SPACFidelityCounterexampleBoundary : Set where
  constructor spacFidelityCounterexampleBoundary
  field
    bucketCanEraseHydraulicConsumerDistinction : Bool
    richardsCanErasePlantHistoryConsumerDistinction : Bool
    hydraulicSPACCanEraseNutrientConsumerDistinction : Bool
    richerTierExistenceAloneRefutesCheaperTier : Bool
    richerTierExistenceAloneRefutesCheaperTierIsFalse : richerTierExistenceAloneRefutesCheaperTier ≡ false
    fixturesAreEmpiricalValidationData : Bool
    fixturesAreEmpiricalValidationDataIsFalse : fixturesAreEmpiricalValidationData ≡ false

canonicalSPACFidelityCounterexampleBoundary : SPACFidelityCounterexampleBoundary
canonicalSPACFidelityCounterexampleBoundary = spacFidelityCounterexampleBoundary true true true false refl false refl
