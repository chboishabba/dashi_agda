module DASHI.Physics.Closure.NSTriadKNHHDirectionalLayerCakeRound41Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Classical result: Cavalieri/layer-cake representation of a nonnegative
-- function by its superlevel sets.  No DOI is assigned to the classical
-- identity itself.
--
-- DASHI CONTRIBUTION
--
-- Round 40 identified E Theta as the single directional-defect mass feeding
-- both HH-good and HH-bad.  The continuation analysis observed that
--
--   Theta = integral_0^1 1_{Theta>s} ds
--
-- makes E Theta the aggregate bad mass across all possible thresholds.
--
-- This file gives an exact finite rational version suitable for the current
-- constructive carrier.  A defect cell is partitioned into finitely many
-- threshold widths; a Bool records whether the cell is active on a slice.
-- If the active widths reconstruct Theta exactly, then the weighted sum of
-- slice masses reconstructs E Theta exactly.  Summing over physical cells
-- preserves the identity.  Thus threshold optimization may be studied as a
-- decomposition of one conserved defect budget rather than as unrelated
-- good/bad bookkeeping.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record ThresholdSlice : Set where
  constructor threshold-slice
  field
    width : ℚ
    active : Bool
    widthNonnegative : 0ℚ ≤ width

open ThresholdSlice public

activeWidth : ThresholdSlice → ℚ
activeWidth slice with active slice
... | true = width slice
... | false = 0ℚ

sumActiveWidth : List ThresholdSlice → ℚ
sumActiveWidth [] = 0ℚ
sumActiveWidth (slice ∷ rest) =
  activeWidth slice + sumActiveWidth rest

weightedSliceMass : ℚ → ThresholdSlice → ℚ
weightedSliceMass energy slice = energy * activeWidth slice

sumWeightedSliceMass : ℚ → List ThresholdSlice → ℚ
sumWeightedSliceMass energy [] = 0ℚ
sumWeightedSliceMass energy (slice ∷ rest) =
  weightedSliceMass energy slice + sumWeightedSliceMass energy rest

energyDistributesAcrossActiveWidths :
  ∀ energy slices →
  sumWeightedSliceMass energy slices
  ≡ energy * sumActiveWidth slices
energyDistributesAcrossActiveWidths energy [] = solve (energy ∷ [])
energyDistributesAcrossActiveWidths energy (slice ∷ rest)
  rewrite energyDistributesAcrossActiveWidths energy rest =
  solve
    ( energy
    ∷ activeWidth slice
    ∷ sumActiveWidth rest
    ∷ [])

record DirectionalDefectLayerCakeCell : Set where
  field
    energy defect : ℚ
    energyNonnegative : 0ℚ ≤ energy
    defectNonnegative : 0ℚ ≤ defect
    slices : List ThresholdSlice
    activeWidthsResolveDefect : sumActiveWidth slices ≡ defect

open DirectionalDefectLayerCakeCell public

weightedDefect : DirectionalDefectLayerCakeCell → ℚ
weightedDefect cell = energy cell * defect cell

layerCakeMass : DirectionalDefectLayerCakeCell → ℚ
layerCakeMass cell = sumWeightedSliceMass (energy cell) (slices cell)

finiteLayerCakeCellExact :
  ∀ cell → layerCakeMass cell ≡ weightedDefect cell
finiteLayerCakeCellExact cell =
  trans
    (energyDistributesAcrossActiveWidths (energy cell) (slices cell))
    (cong (energy cell *_) (activeWidthsResolveDefect cell))

sumWeightedDefect sumLayerCakeMass : List DirectionalDefectLayerCakeCell → ℚ
sumWeightedDefect [] = 0ℚ
sumWeightedDefect (cell ∷ rest) =
  weightedDefect cell + sumWeightedDefect rest

sumLayerCakeMass [] = 0ℚ
sumLayerCakeMass (cell ∷ rest) =
  layerCakeMass cell + sumLayerCakeMass rest

finiteDirectionalLayerCakeExact :
  ∀ cells → sumLayerCakeMass cells ≡ sumWeightedDefect cells
finiteDirectionalLayerCakeExact [] = refl
finiteDirectionalLayerCakeExact (cell ∷ rest)
  rewrite finiteLayerCakeCellExact cell
        | finiteDirectionalLayerCakeExact rest = refl

canonicalSingleSlice :
  (energy defect : ℚ) →
  0ℚ ≤ energy →
  0ℚ ≤ defect →
  DirectionalDefectLayerCakeCell
canonicalSingleSlice energy defect energyNN defectNN = record
  { energy = energy
  ; defect = defect
  ; energyNonnegative = energyNN
  ; defectNonnegative = defectNN
  ; slices = threshold-slice defect true defectNN ∷ []
  ; activeWidthsResolveDefect = solve (defect ∷ [])
  }

record NestedBadMassPair : Set where
  field
    lowerThreshold upperThreshold : ℚ
    lowerBadMass upperBadMass : ℚ
    thresholdOrder : lowerThreshold ≤ upperThreshold
    badMassDecreasesWithThreshold : upperBadMass ≤ lowerBadMass

open NestedBadMassPair public

higherThresholdCannotIncreaseBadMass :
  (pair : NestedBadMassPair) → upperBadMass pair ≤ lowerBadMass pair
higherThresholdCannotIncreaseBadMass = badMassDecreasesWithThreshold

hhDirectionalFiniteLayerCakeClosed : Bool
hhDirectionalFiniteLayerCakeClosed = true

physicalThresholdSuperlevelFamilyConstructed : Bool
physicalThresholdSuperlevelFamilyConstructed = false

hhDirectionalFiniteLayerCakeClosedIsTrue :
  hhDirectionalFiniteLayerCakeClosed ≡ true
hhDirectionalFiniteLayerCakeClosedIsTrue = refl
