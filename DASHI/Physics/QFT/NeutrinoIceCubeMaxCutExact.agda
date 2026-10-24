module DASHI.Physics.QFT.NeutrinoIceCubeMaxCutExact where

-- Reuse-first neutrino audit.  Mathematical calculations are exact, whereas
-- the input numbers are versioned empirical fixtures from NuFIT 6.1 (2025).
-- No first-principles neutrino mass, physical PMNS matrix, or IceCube source
-- inference is constructed by this module.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; _-_)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤ᵇ_)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.FactorVecFalsifiablePredictionLanes as FactorVec

------------------------------------------------------------------------
-- Existing 15SSP ratio claim: reuse the canonical owner, not a new law.
------------------------------------------------------------------------

factorVecCandidateIsOneOver31 :
  (lane : FactorVec.NeutrinoMixingRatioLane) →
  FactorVec.predictedMassSplittingRatio lane ≡
    FactorVec.ratio 1 31
factorVecCandidateIsOneOver31 =
  FactorVec.canonicalNeutrinoMassSplittingRatio

------------------------------------------------------------------------
-- NuFIT 6.1: NO, IC24 with SK atmospheric data, published 3 sigma
-- one-dimensional component ranges.  All quantities are integers in
-- units of 10^(-8) eV^2:
--
-- delta m^2_21: 7.236 ... 7.823 x 10^(-5) eV^2
-- delta m^2_31: 2.450 ... 2.576 x 10^(-3) eV^2
--
-- The Cartesian rectangle of these intervals is an over-approximation
-- of the correlated joint confidence region.  Thus exclusion from the
-- rectangle is a conservative interval statement, NOT a new chi-square
-- or independent 3 sigma hypothesis test.
------------------------------------------------------------------------

solarLower : Nat
solarLower = 7236

solarBest : Nat
solarBest = 7537

solarUpper : Nat
solarUpper = 7823

normalAtmosLower : Nat
normalAtmosLower = 245000

normalAtmosBest : Nat
normalAtmosBest = 251100

normalAtmosUpper : Nat
normalAtmosUpper = 257600

-- 1/31 > solarUpper/normalAtmosLower since
-- 31 * 7823 = 242513 < 245000.
candidateCrossProduct : 31 * solarUpper ≡ 242513
candidateCrossProduct = refl

positiveGap : normalAtmosLower - (31 * solarUpper) ≡ 2487
positiveGap = refl

-- Boolean decision proof using the library's natural comparison.
-- The observation's generous upper ratio cannot reach 1/31.
normalThreeSigmaRectangleExcludesOneOver31 :
  (normalAtmosLower ≤ᵇ (31 * solarUpper)) ≡ false
normalThreeSigmaRectangleExcludesOneOver31 = refl

-- The NO best fit is likewise below the proposed ratio.
normalBestFitBelowCandidate :
  (normalAtmosBest ≤ᵇ (31 * solarBest)) ≡ false
normalBestFitBelowCandidate = refl

------------------------------------------------------------------------
-- Exact four-phase, maximal two-flavour vacuum toy.
--
-- U = Hadamard and mass-phase = 1, i, -1, -i.  Appearance amplitude
-- is (1 - phase)/2, survival amplitude (1 + phase)/2.
-- We prove the squared *numerators* sum to 4, so their probabilities
-- sum to 1 after dividing by 4.  This is an exact finite illustration,
-- NOT three-flavour PMNS, propagation through matter, or detection.
------------------------------------------------------------------------

data Phase4 : Set where
  phase0 phase90 phase180 phase270 : Phase4

data SignedUnit : Set where
  minusOne signedZero plusOne : SignedUnit

phaseReal : Phase4 → SignedUnit
phaseReal phase0   = plusOne
phaseReal phase90  = signedZero
phaseReal phase180 = minusOne
phaseReal phase270 = signedZero

phaseImag : Phase4 → SignedUnit
phaseImag phase0   = signedZero
phaseImag phase90  = plusOne
phaseImag phase180 = signedZero
phaseImag phase270 = minusOne

oneMinus : SignedUnit → Nat
oneMinus minusOne   = 2
oneMinus signedZero = 1
oneMinus plusOne    = 0

onePlus : SignedUnit → Nat
onePlus minusOne   = 0
onePlus signedZero = 1
onePlus plusOne    = 2

square : SignedUnit → Nat
square minusOne   = 1
square signedZero = 0
square plusOne    = 1

appearanceNumSq : Phase4 → Nat
appearanceNumSq p =
  oneMinus (phaseReal p) * oneMinus (phaseReal p) +
  square (phaseImag p)

survivalNumSq : Phase4 → Nat
survivalNumSq p =
  onePlus (phaseReal p) * onePlus (phaseReal p) +
  square (phaseImag p)

toyProbabilityConservation :
  (p : Phase4) → appearanceNumSq p + survivalNumSq p ≡ 4
toyProbabilityConservation phase0   = refl
toyProbabilityConservation phase90  = refl
toyProbabilityConservation phase180 = refl
toyProbabilityConservation phase270 = refl

toyNoAppearanceAtZero : appearanceNumSq phase0 ≡ 0
toyNoAppearanceAtZero = refl

toyFullAppearanceAtPi : appearanceNumSq phase180 ≡ 4
toyFullAppearanceAtPi = refl

quarterTurn : Phase4 → Phase4
quarterTurn phase0   = phase90
quarterTurn phase90  = phase180
quarterTurn phase180 = phase270
quarterTurn phase270 = phase0

fourQuarterTurnsIdentity : (p : Phase4) →
  quarterTurn (quarterTurn (quarterTurn (quarterTurn p))) ≡ p
fourQuarterTurnsIdentity phase0   = refl
fourQuarterTurnsIdentity phase90  = refl
fourQuarterTurnsIdentity phase180 = refl
fourQuarterTurnsIdentity phase270 = refl

------------------------------------------------------------------------
-- Typed experimental boundary.  Unlike the toy phases, actual
-- IceCube point-source inference needs calibrated detector response,
-- atmospheric backgrounds, exposure, and a likelihood with nuisance
-- handling.  These are NOT provided here.
------------------------------------------------------------------------

record IceCubeInferenceInterface : Set₁ where
  field
    Event Direction Energy Exposure DetectorResponse Nuisance Source : Set
    Likelihood : Set
    eventDirection : Event → Direction
    eventEnergy : Event → Energy
    response : Event → DetectorResponse
    backgroundModel : Event → Nuisance
    sourceLikelihood : Source → Event → Exposure → Likelihood
    validatedResponse : DetectorResponse → Set
    validatedExposure : Exposure → Set
    validatedBackground : Nuisance → Set

data PhysicalNeutrinoPromotion : Set where

noPhysicalNeutrinoPromotionFromToy :
  PhysicalNeutrinoPromotion → ⊥
noPhysicalNeutrinoPromotionFromToy ()

nufitFixtureSource : String
nufitFixtureSource =
  "NuFIT 6.1 (2025), IC24 with SK atmospheric, NO, v61.tbl-parameters.pdf"

iceCubeDataSource : String
iceCubeDataSource =
  "IceCube Collaboration IceTracks-DR2 (2026), doi:10.7910/DVN/MMIIZA"

claimBoundary : String
claimBoundary =
  "Only finite algebra and conservative NuFIT interval arithmetic are proved; no physical PMNS, Majorana nature, detector inference or new neutrino observation is proved."
