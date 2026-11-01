module DASHI.Arithmetic.DeltaRarity where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_≤_; _∸_)
open import Data.Nat.Properties as NatP using (m∸n≤m)

open import MonsterOntos using
  ( SSP
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  )
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int
  ; deltaAt
  )
open import DASHI.Arithmetic.ActiveWallStructure using
  ( supportMaskAt
  ; supportPrimeCount
  ; countNonZeroNat-mono
  )
open import DASHI.Arithmetic.TrackedSupport using
  ( sum15≤
  ; supportAt
  ; deltaAt≤supportAt
  )
open import DASHI.Statistics.Vec15Descriptive using
  ( countNonZeroNat
  )

------------------------------------------------------------------------
-- Threshold masks on the tracked 15-prime carrier.
--
-- `thresholdAt k` is the indicator for δ_p ≥ suc k.
-- In particular:
--   thresholdAt zero = δ_p ≥ 1
--   thresholdAt (suc zero) = δ_p ≥ 2
-- so the current threshold-2 rarity surface is just the `suc zero` slice.

thresholdAt : Nat → SSP → Int → Int → Nat
thresholdAt zero p x y = countNonZeroNat (deltaAt p x y)
thresholdAt (suc k) p x y = countNonZeroNat (deltaAt p x y ∸ k)

thresholdMask15 : Nat → Int → Int → Vec15 Nat
thresholdMask15 k x y =
  mkVec15
    (thresholdAt k p2 x y) (thresholdAt k p3 x y) (thresholdAt k p5 x y) (thresholdAt k p7 x y)
    (thresholdAt k p11 x y) (thresholdAt k p13 x y) (thresholdAt k p17 x y) (thresholdAt k p19 x y)
    (thresholdAt k p23 x y) (thresholdAt k p29 x y) (thresholdAt k p31 x y) (thresholdAt k p41 x y)
    (thresholdAt k p47 x y) (thresholdAt k p59 x y) (thresholdAt k p71 x y)

thresholdCount : Nat → Int → Int → Nat
thresholdCount k x y =
  thresholdAt k p2 x y + thresholdAt k p3 x y + thresholdAt k p5 x y + thresholdAt k p7 x y +
  thresholdAt k p11 x y + thresholdAt k p13 x y + thresholdAt k p17 x y + thresholdAt k p19 x y +
  thresholdAt k p23 x y + thresholdAt k p29 x y + thresholdAt k p31 x y + thresholdAt k p41 x y +
  thresholdAt k p47 x y + thresholdAt k p59 x y + thresholdAt k p71 x y

largeDeltaAt2 : SSP → Int → Int → Nat
largeDeltaAt2 = thresholdAt (suc zero)

largeDeltaMask15 : Int → Int → Vec15 Nat
largeDeltaMask15 = thresholdMask15 (suc zero)

largeDeltaCount2 : Int → Int → Nat
largeDeltaCount2 = thresholdCount (suc zero)

------------------------------------------------------------------------
-- Pointwise support inclusion.
--
-- If δ_p ≥ suc k then δ_p is certainly nonzero, so every threshold slice
-- sits inside the same support-side shadow already used by the active-wall
-- bridge.

thresholdAt≤supportMaskAt :
  ∀ k p x y →
  thresholdAt k p x y ≤ supportMaskAt p x y
thresholdAt≤supportMaskAt zero p x y =
  countNonZeroNat-mono
    (deltaAt p x y)
    (supportAt p x y)
    (deltaAt≤supportAt p x y)
thresholdAt≤supportMaskAt (suc k) p x y =
  NatP.≤-trans
    (countNonZeroNat-mono
      (deltaAt p x y ∸ k)
      (deltaAt p x y)
      (m∸n≤m (deltaAt p x y) k))
    (countNonZeroNat-mono
      (deltaAt p x y)
      (supportAt p x y)
      (deltaAt≤supportAt p x y))

------------------------------------------------------------------------
-- Lift the threshold support inclusion across the tracked carrier.

thresholdCount≤supportPrimeCount :
  ∀ k x y →
  thresholdCount k x y ≤ supportPrimeCount x y
thresholdCount≤supportPrimeCount k x y =
  sum15≤
    (thresholdAt k p2 x y) (thresholdAt k p3 x y) (thresholdAt k p5 x y) (thresholdAt k p7 x y)
    (thresholdAt k p11 x y) (thresholdAt k p13 x y) (thresholdAt k p17 x y) (thresholdAt k p19 x y)
    (thresholdAt k p23 x y) (thresholdAt k p29 x y) (thresholdAt k p31 x y) (thresholdAt k p41 x y)
    (thresholdAt k p47 x y) (thresholdAt k p59 x y) (thresholdAt k p71 x y)
    (supportMaskAt p2 x y) (supportMaskAt p3 x y) (supportMaskAt p5 x y) (supportMaskAt p7 x y)
    (supportMaskAt p11 x y) (supportMaskAt p13 x y) (supportMaskAt p17 x y) (supportMaskAt p19 x y)
    (supportMaskAt p23 x y) (supportMaskAt p29 x y) (supportMaskAt p31 x y) (supportMaskAt p41 x y)
    (supportMaskAt p47 x y) (supportMaskAt p59 x y) (supportMaskAt p71 x y)
    (thresholdAt≤supportMaskAt k p2 x y)
    (thresholdAt≤supportMaskAt k p3 x y)
    (thresholdAt≤supportMaskAt k p5 x y)
    (thresholdAt≤supportMaskAt k p7 x y)
    (thresholdAt≤supportMaskAt k p11 x y)
    (thresholdAt≤supportMaskAt k p13 x y)
    (thresholdAt≤supportMaskAt k p17 x y)
    (thresholdAt≤supportMaskAt k p19 x y)
    (thresholdAt≤supportMaskAt k p23 x y)
    (thresholdAt≤supportMaskAt k p29 x y)
    (thresholdAt≤supportMaskAt k p31 x y)
    (thresholdAt≤supportMaskAt k p41 x y)
    (thresholdAt≤supportMaskAt k p47 x y)
    (thresholdAt≤supportMaskAt k p59 x y)
    (thresholdAt≤supportMaskAt k p71 x y)

thresholdRarity :
  ∀ k x y →
  thresholdCount k x y ≤ supportPrimeCount x y
thresholdRarity = thresholdCount≤supportPrimeCount

largeDeltaAt2≤supportMaskAt :
  ∀ p x y →
  largeDeltaAt2 p x y ≤ supportMaskAt p x y
largeDeltaAt2≤supportMaskAt = thresholdAt≤supportMaskAt (suc zero)

largeDeltaCount2≤supportPrimeCount :
  ∀ x y →
  largeDeltaCount2 x y ≤ supportPrimeCount x y
largeDeltaCount2≤supportPrimeCount = thresholdCount≤supportPrimeCount (suc zero)

thresholdRarity2 :
  ∀ x y →
  largeDeltaCount2 x y ≤ supportPrimeCount x y
thresholdRarity2 = largeDeltaCount2≤supportPrimeCount

record DeltaRarityStructure : Set₁ where
  field
    thresholdMaskFn : Nat → SSP → Int → Int → Nat
    thresholdCountFn : Nat → Int → Int → Nat
    thresholdSupportSubset :
      ∀ k x y →
      thresholdCountFn k x y ≤ supportPrimeCount x y

open DeltaRarityStructure public

deltaRarityStructure : DeltaRarityStructure
deltaRarityStructure = record
  { thresholdMaskFn = thresholdAt
  ; thresholdCountFn = thresholdCount
  ; thresholdSupportSubset = thresholdCount≤supportPrimeCount
  }
