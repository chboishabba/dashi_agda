module DASHI.Arithmetic.KPrimeInteraction where

open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (NonZero)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP using (+-mono-≤)
open import Data.Nat.Divisibility using (_∣_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty using (⊥)

open import Ontology.GodelLattice using (Vec15)
open import DASHI.TrackedPrimes using
  ( SSP
  ; toNat
  ; trackedPrimeList
  )

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int
  ; deltaAt
  )
open import DASHI.Arithmetic.ActiveWallStructure using
  ( supportMaskAt
  ; supportPrimeCount
  )
open import DASHI.Arithmetic.DeltaGrowth using
  ( pow
  ; deltaPowerDividesSum
  ; deltaPower≤sum
  )
open import DASHI.Arithmetic.TrackedCoprimeTable using (_≢_)
open import DASHI.Arithmetic.DeltaInteraction using
  ( distinctPrimePowerProductDividesSum
  ; twoPrimeInteractionBudget
  )
open import DASHI.Arithmetic.DeltaRarity using
  ( thresholdAt
  ; thresholdMask15
  ; thresholdCount
  ; thresholdCount≤supportPrimeCount
  ; thresholdAt≤supportMaskAt
  )

------------------------------------------------------------------------
-- Minimal k-prime interaction surface.
--
-- The list side is the new honest step: a finite inductive carrier of the
-- tracked primes with a recursive threshold/support count theorem.
-- The pairwise interaction side is imported directly from DeltaInteraction.
-- The hard family product theorem remains intentionally out of scope.

familyThresholdCount : Nat → List SSP → Int → Int → Nat
familyThresholdCount k [] x y = zero
familyThresholdCount k (p ∷ ps) x y =
  thresholdAt k p x y + familyThresholdCount k ps x y

familySupportCount : List SSP → Int → Int → Nat
familySupportCount [] x y = zero
familySupportCount (p ∷ ps) x y =
  supportMaskAt p x y + familySupportCount ps x y

familyThresholdSupportSubset :
  ∀ k ps x y →
  familyThresholdCount k ps x y ≤ familySupportCount ps x y
familyThresholdSupportSubset k [] x y = NatP.≤-refl
familyThresholdSupportSubset k (p ∷ ps) x y =
  +-mono-≤
    (thresholdAt≤supportMaskAt k p x y)
    (familyThresholdSupportSubset k ps x y)

pairPowerDivides :
  ∀ p q x y →
  p ≢ q →
  (pow (toNat p) (deltaAt p x y) * pow (toNat q) (deltaAt q x y)) ∣ (x + y)
pairPowerDivides = distinctPrimePowerProductDividesSum

pairPowerBound :
  ∀ p q x y →
  .{{_ : NonZero (x + y)}} →
  p ≢ q →
  (pow (toNat p) (deltaAt p x y) * pow (toNat q) (deltaAt q x y)) ≤ (x + y)
pairPowerBound = twoPrimeInteractionBudget

trackedFamilyThresholdCount : Nat → Int → Int → Nat
trackedFamilyThresholdCount k x y = familyThresholdCount k trackedPrimeList x y

trackedFamilySupportCount : Int → Int → Nat
trackedFamilySupportCount x y = familySupportCount trackedPrimeList x y

trackedFamilyThresholdSupportSubset :
  ∀ k x y →
  trackedFamilyThresholdCount k x y ≤ trackedFamilySupportCount x y
trackedFamilyThresholdSupportSubset k x y =
  familyThresholdSupportSubset k trackedPrimeList x y

------------------------------------------------------------------------
-- Reusable vector compatibility surface.

kThresholdMask : Nat → Int → Int → Vec15 Nat
kThresholdMask = thresholdMask15

kThresholdCount : Nat → Int → Int → Nat
kThresholdCount = thresholdCount

kThresholdSupportSubset :
  ∀ k x y →
  kThresholdCount k x y ≤ supportPrimeCount x y
kThresholdSupportSubset = thresholdCount≤supportPrimeCount

------------------------------------------------------------------------
-- Single-lane arithmetic budget, reused from DeltaGrowth.

singleLanePowerDivides :
  ∀ p x y →
  pow (toNat p) (deltaAt p x y) ∣ (x + y)
singleLanePowerDivides = deltaPowerDividesSum

singleLanePowerBound :
  ∀ p x y →
  .{{_ : NonZero (x + y)}} →
  pow (toNat p) (deltaAt p x y) ≤ x + y
singleLanePowerBound = deltaPower≤sum

record KPrimeInteractionSurface : Set₁ where
  field
    primeList : List SSP
    thresholdMaskFn : Nat → Int → Int → Vec15 Nat
    thresholdCountFn : Nat → Int → Int → Nat
    thresholdSupportSubset :
      ∀ k x y →
      thresholdCountFn k x y ≤ supportPrimeCount x y
    listThresholdCount :
      Nat → List SSP → Int → Int → Nat
    listSupportCount :
      List SSP → Int → Int → Nat
    listThresholdSupportSubset :
      ∀ k ps x y →
      listThresholdCount k ps x y ≤ listSupportCount ps x y
    pairPowerDividesFn :
      ∀ p q x y →
      p ≢ q →
      (pow (toNat p) (deltaAt p x y) * pow (toNat q) (deltaAt q x y)) ∣ (x + y)
    pairPowerBoundFn :
      ∀ p q x y →
      .{{_ : NonZero (x + y)}} →
      p ≢ q →
      (pow (toNat p) (deltaAt p x y) * pow (toNat q) (deltaAt q x y)) ≤ (x + y)
    lanePowerDivides :
      ∀ p x y →
      pow (toNat p) (deltaAt p x y) ∣ (x + y)
    lanePowerBound :
      ∀ p x y →
      .{{_ : NonZero (x + y)}} →
      pow (toNat p) (deltaAt p x y) ≤ x + y

open KPrimeInteractionSurface public

kPrimeInteractionSurface : KPrimeInteractionSurface
kPrimeInteractionSurface = record
  { primeList = trackedPrimeList
  ; thresholdMaskFn = kThresholdMask
  ; thresholdCountFn = kThresholdCount
  ; thresholdSupportSubset = kThresholdSupportSubset
  ; listThresholdCount = familyThresholdCount
  ; listSupportCount = familySupportCount
  ; listThresholdSupportSubset = familyThresholdSupportSubset
  ; pairPowerDividesFn = pairPowerDivides
  ; pairPowerBoundFn = pairPowerBound
  ; lanePowerDivides = singleLanePowerDivides
  ; lanePowerBound = singleLanePowerBound
  }
