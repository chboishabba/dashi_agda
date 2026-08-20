module DASHI.Physics.Closure.NSTriadKNHeterochiralGapRelativeDampingRound106Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND106 / GAP GAIN BELONGS IN c/S BEFORE TIME INTEGRATION
--
-- Let L be the low radius, H a high radius, g a low/high envelope with
--
--   L <= g H,
--
-- and let S be the Waleffe phase damping scale with H^2 <= S.
--
-- * Low-minority geometry already gives c <= 2 L^2, hence
--
--     c <= 2 g^2 S.
--
-- * Once the Round102 Waleffe--Heron high-minority improvement is retained in
--   the literal coefficient, c <= 2 L H, hence
--
--     c <= 2 g S.
--
-- These are exact ordered-rational implications.  They identify the weights
-- that must multiply the SIGNED adverse-episode forcing before any network
-- summation: two gap powers for low minority, one for high minority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record GapDampingGeometry : Set where
  constructor gap-damping-geometry
  field
    low high gap dampingScale : ℚ
    lowNonnegative : 0ℚ ≤ low
    highNonnegative : 0ℚ ≤ high
    gapNonnegative : 0ℚ ≤ gap
    dampingScaleNonnegative : 0ℚ ≤ dampingScale
    lowBelowGapHigh : low ≤ gap * high
    highSquaredBelowDamping : high * high ≤ dampingScale

open GapDampingGeometry public

two : ℚ
two = 2

twoNonnegative : 0ℚ ≤ two
twoNonnegative = ℚP.<⇒≤ (ℚP.positive⁻¹ two)

lowSquaredBelowGapSquaredHighSquared :
  (G : GapDampingGeometry) →
  low G * low G ≤ (gap G * gap G) * (high G * high G)
lowSquaredBelowGapSquaredHighSquared G =
  let
    L = low G
    H = high G
    g = gap G

    first : L * L ≤ (g * H) * (g * H)
    first =
      ℚP.*-mono-≤
        (lowNonnegative G) (lowNonnegative G)
        (let instance gNN = nonNegative (gapNonnegative G)
                  hNN = nonNegative (highNonnegative G)
              in ℚP.nonNegative⁻¹ (g * H))
        (let instance gNN = nonNegative (gapNonnegative G)
                  hNN = nonNegative (highNonnegative G)
              in ℚP.nonNegative⁻¹ (g * H))
        (lowBelowGapHigh G) (lowBelowGapHigh G)

    endpoint : (g * H) * (g * H) ≡ (g * g) * (H * H)
    endpoint = solve (g ∷ H ∷ [])
  in
  subst (λ upper → L * L ≤ upper) endpoint first

lowMinorityCoefficientHasSquaredGap :
  (G : GapDampingGeometry) →
  (coefficient : ℚ) →
  coefficient ≤ two * (low G * low G) →
  coefficient ≤ (two * (gap G * gap G)) * dampingScale G
lowMinorityCoefficientHasSquaredGap G coefficient coefficientBound =
  let
    g2 = gap G * gap G
    lowSquareToGapHigh = lowSquaredBelowGapSquaredHighSquared G

    doubled :
      two * (low G * low G)
      ≤ two * (g2 * (high G * high G))
    doubled =
      let instance twoNN = nonNegative twoNonnegative
      in ℚP.*-monoˡ-≤-nonNeg two lowSquareToGapHigh

    g2NN : 0ℚ ≤ g2
    g2NN =
      let instance gNN = nonNegative (gapNonnegative G)
      in ℚP.nonNegative⁻¹ g2

    factorNN : 0ℚ ≤ two * g2
    factorNN =
      let instance twoNN = nonNegative twoNonnegative
          gNN = nonNegative g2NN
      in ℚP.nonNegative⁻¹ (two * g2)

    dampingStep :
      (two * g2) * (high G * high G)
      ≤ (two * g2) * dampingScale G
    dampingStep =
      let instance fNN = nonNegative factorNN
      in ℚP.*-monoˡ-≤-nonNeg (two * g2)
        (highSquaredBelowDamping G)

    middleMeaning :
      two * (g2 * (high G * high G))
      ≡ (two * g2) * (high G * high G)
    middleMeaning = solve (g2 ∷ high G ∷ [])
  in
  ℚP.≤-trans coefficientBound
    (ℚP.≤-trans doubled
      (subst
        (λ left → left ≤ (two * g2) * dampingScale G)
        middleMeaning dampingStep))

lowTimesHighBelowGapHighSquared :
  (G : GapDampingGeometry) →
  low G * high G ≤ gap G * (high G * high G)
lowTimesHighBelowGapHighSquared G =
  let
    scaled =
      let instance hNN = nonNegative (highNonnegative G)
      in ℚP.*-monoʳ-≤-nonNeg (high G) (lowBelowGapHigh G)
    endpoint : (gap G * high G) * high G
      ≡ gap G * (high G * high G)
    endpoint = solve (gap G ∷ high G ∷ [])
  in
  subst
    (λ upper → low G * high G ≤ upper)
    endpoint scaled

highMinorityImprovedCoefficientHasSingleGap :
  (G : GapDampingGeometry) →
  (coefficient : ℚ) →
  coefficient ≤ two * (low G * high G) →
  coefficient ≤ (two * gap G) * dampingScale G
highMinorityImprovedCoefficientHasSingleGap G coefficient coefficientBound =
  let
    lowHigh = lowTimesHighBelowGapHighSquared G
    doubled :
      two * (low G * high G)
      ≤ two * (gap G * (high G * high G))
    doubled =
      let instance twoNN = nonNegative twoNonnegative
      in ℚP.*-monoˡ-≤-nonNeg two lowHigh

    factorNN : 0ℚ ≤ two * gap G
    factorNN =
      let instance twoNN = nonNegative twoNonnegative
          gNN = nonNegative (gapNonnegative G)
      in ℚP.nonNegative⁻¹ (two * gap G)

    dampingStep :
      (two * gap G) * (high G * high G)
      ≤ (two * gap G) * dampingScale G
    dampingStep =
      let instance fNN = nonNegative factorNN
      in ℚP.*-monoˡ-≤-nonNeg (two * gap G)
        (highSquaredBelowDamping G)

    middleMeaning :
      two * (gap G * (high G * high G))
      ≡ (two * gap G) * (high G * high G)
    middleMeaning = solve (gap G ∷ high G ∷ [])
  in
  ℚP.≤-trans coefficientBound
    (ℚP.≤-trans doubled
      (subst
        (λ left → left ≤ (two * gap G) * dampingScale G)
        middleMeaning dampingStep))

round106LowMinorityCarriesTwoGapPowers : Bool
round106LowMinorityCarriesTwoGapPowers = true

round106HighMinorityCarriesOneGapPowerAfterWaleffeImprovement : Bool
round106HighMinorityCarriesOneGapPowerAfterWaleffeImprovement = true

round106LowMinorityCarriesTwoGapPowersIsTrue :
  round106LowMinorityCarriesTwoGapPowers ≡ true
round106LowMinorityCarriesTwoGapPowersIsTrue = refl

round106HighMinorityCarriesOneGapPowerAfterWaleffeImprovementIsTrue :
  round106HighMinorityCarriesOneGapPowerAfterWaleffeImprovement ≡ true
round106HighMinorityCarriesOneGapPowerAfterWaleffeImprovementIsTrue = refl
