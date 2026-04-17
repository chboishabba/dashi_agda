module DASHI.Arithmetic.ActiveWallStructure where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; z≤n)
open import Data.Nat.Properties as NatP using (≤-refl)

open import Ontology.GodelLattice using (Vec15)
open import DASHI.TrackedPrimes using
  ( SSP
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  ; mapTrackedPrimes15
  )

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int
  ; deltaAt
  ; delta15
  ; gammaAt
  ; gamma15
  )
open import DASHI.Arithmetic.MaxPressure using
  ( weightedMaxPressure )
open import DASHI.Arithmetic.TrackedSupport using
  ( sum15≤
  ; supportAt
  ; deltaAt≤supportAt
  )
open import DASHI.Statistics.Vec15Descriptive using
  ( countNonZeroNat
  ; countNonZero15
  )

------------------------------------------------------------------------
-- Active-wall structure.
--
-- The raw wall bit tracks equal valuations, including the inert zero-zero
-- case. The active wall is the stronger object needed for arithmetic
-- control: tracked primes whose local cancellation lift is genuinely
-- non-zero.

activeWallAt : SSP → Int → Int → Bool
activeWallAt p x y with deltaAt p x y
... | zero = false
... | suc _ = true

activeWallMaskAt : SSP → Int → Int → Nat
activeWallMaskAt p x y = countNonZeroNat (deltaAt p x y)

supportMaskAt : SSP → Int → Int → Nat
supportMaskAt p x y = countNonZeroNat (supportAt p x y)

activeWallMask15 : Int → Int → Vec15 Nat
activeWallMask15 x y = mapTrackedPrimes15 (λ p → activeWallMaskAt p x y)

supportMask15 : Int → Int → Vec15 Nat
supportMask15 x y = mapTrackedPrimes15 (λ p → supportMaskAt p x y)

activeWallCount : Int → Int → Nat
activeWallCount x y = countNonZero15 (delta15 x y)

supportPrimeCount : Int → Int → Nat
supportPrimeCount x y = countNonZero15 (gamma15 x y)

------------------------------------------------------------------------
-- Local monotonicity for the active-wall indicator.

countNonZeroNat-mono :
  ∀ a b →
  a ≤ b →
  countNonZeroNat a ≤ countNonZeroNat b
countNonZeroNat-mono zero zero _ = ≤-refl
countNonZeroNat-mono zero (suc _) _ = z≤n
countNonZeroNat-mono (suc _) zero ()
countNonZeroNat-mono (suc _) (suc _) _ = ≤-refl

activeWallMaskAt≤supportMaskAt :
  ∀ p x y →
  activeWallMaskAt p x y ≤ supportMaskAt p x y
activeWallMaskAt≤supportMaskAt p x y =
  countNonZeroNat-mono
    (deltaAt p x y)
    (gammaAt p x y)
    (deltaAt≤supportAt p x y)

------------------------------------------------------------------------
-- Active-wall primes are a support-side subset over the tracked carrier.

activeWallCount≤supportPrimeCount :
  ∀ x y →
  activeWallCount x y ≤ supportPrimeCount x y
activeWallCount≤supportPrimeCount x y =
  sum15≤
    (activeWallMaskAt p2 x y) (activeWallMaskAt p3 x y) (activeWallMaskAt p5 x y) (activeWallMaskAt p7 x y)
    (activeWallMaskAt p11 x y) (activeWallMaskAt p13 x y) (activeWallMaskAt p17 x y) (activeWallMaskAt p19 x y)
    (activeWallMaskAt p23 x y) (activeWallMaskAt p29 x y) (activeWallMaskAt p31 x y) (activeWallMaskAt p41 x y)
    (activeWallMaskAt p47 x y) (activeWallMaskAt p59 x y) (activeWallMaskAt p71 x y)
    (supportMaskAt p2 x y) (supportMaskAt p3 x y) (supportMaskAt p5 x y) (supportMaskAt p7 x y)
    (supportMaskAt p11 x y) (supportMaskAt p13 x y) (supportMaskAt p17 x y) (supportMaskAt p19 x y)
    (supportMaskAt p23 x y) (supportMaskAt p29 x y) (supportMaskAt p31 x y) (supportMaskAt p41 x y)
    (supportMaskAt p47 x y) (supportMaskAt p59 x y) (supportMaskAt p71 x y)
    (activeWallMaskAt≤supportMaskAt p2 x y)
    (activeWallMaskAt≤supportMaskAt p3 x y)
    (activeWallMaskAt≤supportMaskAt p5 x y)
    (activeWallMaskAt≤supportMaskAt p7 x y)
    (activeWallMaskAt≤supportMaskAt p11 x y)
    (activeWallMaskAt≤supportMaskAt p13 x y)
    (activeWallMaskAt≤supportMaskAt p17 x y)
    (activeWallMaskAt≤supportMaskAt p19 x y)
    (activeWallMaskAt≤supportMaskAt p23 x y)
    (activeWallMaskAt≤supportMaskAt p29 x y)
    (activeWallMaskAt≤supportMaskAt p31 x y)
    (activeWallMaskAt≤supportMaskAt p41 x y)
    (activeWallMaskAt≤supportMaskAt p47 x y)
    (activeWallMaskAt≤supportMaskAt p59 x y)
    (activeWallMaskAt≤supportMaskAt p71 x y)

record ActiveWallStructure : Set₁ where
  field
    activeCount : Int → Int → Nat
    supportCount : Int → Int → Nat
    weightedPeak : Int → Int → Nat
    activeSubsetOfSupport :
      ∀ x y →
      activeCount x y ≤ supportCount x y

open ActiveWallStructure public

activeWallStructure : ActiveWallStructure
activeWallStructure = record
  { activeCount = activeWallCount
  ; supportCount = supportPrimeCount
  ; weightedPeak = weightedMaxPressure
  ; activeSubsetOfSupport = activeWallCount≤supportPrimeCount
  }
