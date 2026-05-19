module DASHI.Arithmetic.PartialResult where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Nat using (_≤_)
open import Data.Nat.Base using (NonZero)
open import Data.Nat.Divisibility using (_∣_)

open import MonsterOntos using (SSP; toNat)

open import DASHI.Arithmetic.GlobalPressure using
  ( GlobalPressureStructure
  ; globalPressureStructure
  ; totalPressure
  ; wallPressure
  ; totalPressure≡wallPressure
  )
open import DASHI.Arithmetic.TrackedSupport using
  ( TrackedSupportStructure
  ; trackedSupportStructure
  ; trackedSupport
  ; totalPressure≤trackedSupport
  )
open import DASHI.Arithmetic.WeightedPressure using
  ( WeightedPressureStructure
  ; weightedPressureStructure
  ; weightedPressure
  ; weightedSupport
  ; weightedPressure≤weightedSupport
  )
open import DASHI.Arithmetic.EpsilonBound using
  ( TrackedEpsilonBoundStructure
  ; trackedEpsilonBoundStructure
  ; explicitTrackedEpsilonBound
  ; trackedPrimeLogConstant
  )
open import DASHI.Arithmetic.ActiveWallStructure using
  ( ActiveWallStructure
  ; activeWallStructure
  ; activeWallCount
  ; supportPrimeCount
  ; activeWallCount≤supportPrimeCount
  )
open import DASHI.Arithmetic.ActiveWallBounds using
  ( ActiveWallBoundStructure
  ; activeWallBoundStructure
  ; activeWallScaledPressure
  ; totalPressure≤activeWallScaledPressure
  )
open import DASHI.Arithmetic.DeltaGrowth using
  ( DeltaGrowthStructure
  ; deltaGrowthStructure
  ; logNat
  ; pow
  )
open import DASHI.Arithmetic.DeltaInteraction using
  ( DeltaInteractionSurface
  ; deltaInteractionSurface
  ; distinctPrimePowerProductDividesSum
  ; twoPrimeInteractionBudget
  )
open import DASHI.Arithmetic.TrackedCoprimeTable using (_≢_)
open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using (deltaAt)
open import DASHI.Arithmetic.KPrimeInteraction using
  ( KPrimeInteractionSurface
  ; kPrimeInteractionSurface
  )
open import DASHI.Arithmetic.DeltaRarity using
  ( DeltaRarityStructure
  ; deltaRarityStructure
  ; thresholdRarity
  ; thresholdRarity2
  ; thresholdCount
  ; largeDeltaCount2
  )
open import DASHI.Arithmetic.MaxPressure using (weightedMaxPressure)

------------------------------------------------------------------------
-- Strongest honest partial result currently supported by the repo.
--
-- This packages the already-landed theorem family:
--   - totalPressure ≡ wallPressure
--   - totalPressure ≤ trackedSupport
--   - weightedPressure ≤ weightedSupport
--   - explicit tracked epsilon-envelope surface
--   - distinct tracked prime-power factors combine via the two-prime budget
--   - thresholdCount k ≤ supportPrimeCount
--
-- It does not mention the radical comparison, which remains the open gap.

record PartialResultSurface : Set₁ where
  field
    wallStructure : GlobalPressureStructure
    trackedStructure : TrackedSupportStructure
    weightedStructure : WeightedPressureStructure
    activeWallStructure' : ActiveWallStructure
    activeWallBounds : ActiveWallBoundStructure
    deltaGrowth : DeltaGrowthStructure
    deltaInteraction : DeltaInteractionSurface
    kPrimeInteraction : KPrimeInteractionSurface
    deltaRarity : DeltaRarityStructure
    wallDecomposition :
      ∀ x y →
      totalPressure x y ≡ wallPressure x y
    activeWallSubset :
      ∀ x y →
      activeWallCount x y ≤ supportPrimeCount x y
    activeWallScaledBound :
      ∀ x y →
      totalPressure x y ≤ activeWallScaledPressure x y
    twoPrimeBudget :
      ∀ p q x y →
      p ≢ q →
      (pow (toNat p) (deltaAt p x y) * pow (toNat q) (deltaAt q x y)) ∣ (x + y)
    twoPrimeSizeBound :
      ∀ p q x y →
      .{{_ : NonZero (x + y)}} →
      p ≢ q →
      (pow (toNat p) (deltaAt p x y) * pow (toNat q) (deltaAt q x y)) ≤ (x + y)
    thresholdRarityBound :
      ∀ k x y →
      thresholdCount k x y ≤ supportPrimeCount x y
    thresholdRarity2Subset :
      ∀ x y →
      largeDeltaCount2 x y ≤ supportPrimeCount x y
    trackedGlobalBound :
      ∀ x y →
      totalPressure x y ≤ trackedSupport x y
    weightedGlobalBound :
      ∀ x y →
      weightedPressure x y ≤ weightedSupport x y
    epsilonBound :
      TrackedEpsilonBoundStructure

open PartialResultSurface public

partialResultSurface : PartialResultSurface
partialResultSurface = record
  { wallStructure = globalPressureStructure
  ; trackedStructure = trackedSupportStructure
  ; weightedStructure = weightedPressureStructure
  ; activeWallStructure' = activeWallStructure
  ; activeWallBounds = activeWallBoundStructure
  ; deltaGrowth = deltaGrowthStructure
  ; deltaInteraction = deltaInteractionSurface
  ; kPrimeInteraction = kPrimeInteractionSurface
  ; deltaRarity = deltaRarityStructure
  ; wallDecomposition = totalPressure≡wallPressure
  ; activeWallSubset = activeWallCount≤supportPrimeCount
  ; activeWallScaledBound = totalPressure≤activeWallScaledPressure
  ; twoPrimeBudget = distinctPrimePowerProductDividesSum
  ; twoPrimeSizeBound = twoPrimeInteractionBudget
  ; thresholdRarityBound = thresholdRarity
  ; thresholdRarity2Subset = thresholdRarity2
  ; trackedGlobalBound = totalPressure≤trackedSupport
  ; weightedGlobalBound = weightedPressure≤weightedSupport
  ; epsilonBound = trackedEpsilonBoundStructure
  }

------------------------------------------------------------------------
-- Convenience re-exports for consumers that want the theorem bundle
-- without unpacking the record.

wallOnlyDecomposition :
  ∀ x y →
  totalPressure x y ≡ wallPressure x y
wallOnlyDecomposition = totalPressure≡wallPressure

trackedUnweightedBound :
  ∀ x y →
  totalPressure x y ≤ trackedSupport x y
trackedUnweightedBound = totalPressure≤trackedSupport

weightedBound :
  ∀ x y →
  weightedPressure x y ≤ weightedSupport x y
weightedBound = weightedPressure≤weightedSupport

activeWallSubsetSupport :
  ∀ x y →
  activeWallCount x y ≤ supportPrimeCount x y
activeWallSubsetSupport = activeWallCount≤supportPrimeCount

activeWallScaledGlobalBound :
  ∀ x y →
  totalPressure x y ≤ activeWallScaledPressure x y
activeWallScaledGlobalBound = totalPressure≤activeWallScaledPressure

twoPrimeInteractionDivides :
  ∀ p q x y →
  p ≢ q →
  (pow (toNat p) (deltaAt p x y) * pow (toNat q) (deltaAt q x y)) ∣ (x + y)
twoPrimeInteractionDivides = distinctPrimePowerProductDividesSum

twoPrimeInteractionSizeBound :
  ∀ p q x y →
  .{{_ : NonZero (x + y)}} →
  p ≢ q →
  (pow (toNat p) (deltaAt p x y) * pow (toNat q) (deltaAt q x y)) ≤ (x + y)
twoPrimeInteractionSizeBound = twoPrimeInteractionBudget

largeDeltaThreshold2Support :
  ∀ x y →
  largeDeltaCount2 x y ≤ supportPrimeCount x y
largeDeltaThreshold2Support = thresholdRarity2

thresholdRaritySupport :
  ∀ k x y →
  thresholdCount k x y ≤ supportPrimeCount x y
thresholdRaritySupport = thresholdRarity

epsilonTrackedBound :
  ∀ x y →
  weightedPressure x y ≤
    trackedPrimeLogConstant * suc (logNat (weightedMaxPressure x y)) * logNat (x + y)
epsilonTrackedBound = explicitTrackedEpsilonBound
