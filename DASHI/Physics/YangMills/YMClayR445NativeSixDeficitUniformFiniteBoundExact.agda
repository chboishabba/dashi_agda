{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayR445NativeSixDeficitUniformFiniteBoundExact where

------------------------------------------------------------------------
-- R445 FINITE NATIVE WILSON ACTION BOUND (SIDE FOUR, 256 SITES).
--
-- On the pre-existing rational unit-SU2 lattice, |ReTr(U_p)/2| <= 1
-- for EACH original positive plaquette, by the source trace theorem.
-- There are exactly six positive planes at each of 4^4=256 sites.
--
-- Therefore 0 <= SUM_{sites, six planes} (1-ReTr(U_p)/2) <= 3072.
-- This closes the old *fixed-lattice finite source majorant* only.
-- It is NOT a uniform-in-cutoff or infinite-volume R445 tail estimate.
--
-- Mathematical provenance: K. Wilson, "Confinement of Quarks",
-- Phys. Rev. D 10 (1974), 2445-2459, DOI 10.1103/PhysRevD.10.2445.
-- Reuse: existing DASHI rational SU2 trace bounds, native original
-- six-plane enumeration, rational summation and site-order owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; subst₂)

import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonTraceBoundExact as Trace
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Native
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeGlobalDefectExact as SiteOrder
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClayNativeRationalSU2SixPlaneSameSourceExact as Six
import DASHI.Physics.YangMills.YMClayNativeSixPlaneOrderedIdentityExact as Action

sixℚ : ℚ
sixℚ = Action.sixℚ

twelveℚ : ℚ
twelveℚ = sixℚ + sixℚ

threeThousandSeventyTwoℚ : ℚ
threeThousandSeventyTwoℚ = + 3072 / 1

-- A lightweight monotone induction reuses the SAME source sumMap and
-- natScale. No new finite enumeration is constructed.
sumMapLower :
  ∀ {A : Set} (values : List A) (term : A → ℚ) lower →
  (∀ value → lower ≤ term value) →
  SU2.natScale (SU2.length values) lower ≤ SU2.sumMap values term
sumMapLower [] term lower pointwise = ℚP.≤-refl
sumMapLower (value ∷ values) term lower pointwise =
  ℚP.+-mono-≤
    (pointwise value)
    (sumMapLower values term lower pointwise)

sumMapUpper :
  ∀ {A : Set} (values : List A) (term : A → ℚ) upper →
  (∀ value → term value ≤ upper) →
  SU2.sumMap values term ≤ SU2.natScale (SU2.length values) upper
sumMapUpper [] term upper pointwise = ℚP.≤-refl
sumMapUpper (value ∷ values) term upper pointwise =
  ℚP.+-mono-≤
    (pointwise value)
    (sumMapUpper values term upper pointwise)

-- Original six source plaquettes at every site; the fixed six is defined
-- by the pre-existing ownedPeriodicPlaquettes allCyclicIndices enumeration.
nativeSixLengthNegativeOne :
  ∀ site →
  SU2.natScale (SU2.length (Plaquette.ownedPeriodicPlaquettes site))
    (- 1ℚ)
  ≡ - sixℚ
nativeSixLengthNegativeOne site = ℚRing.solve-∀

nativeSixLengthPositiveOne :
  ∀ site →
  SU2.natScale (SU2.length (Plaquette.ownedPeriodicPlaquettes site))
    1ℚ
  ≡ sixℚ
nativeSixLengthPositiveOne site = ℚRing.solve-∀

nativeSixTraceLower :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three) site →
  - sixℚ ≤ Six.nativeSixPlaneTraceSumAt dataSet site
nativeSixTraceLower dataSet site =
  subst
    (λ lower → lower ≤ Six.nativeSixPlaneTraceSumAt dataSet site)
    (nativeSixLengthNegativeOne site)
    (sumMapLower
      (Plaquette.ownedPeriodicPlaquettes site)
      (λ p → SU2.realPart (Native.rationalSU2PlaquetteHolonomy dataSet p))
      (- 1ℚ)
      (λ p →
        Trace.normalizedTraceLowerBound
          (Native.rationalSU2PlaquetteHolonomy dataSet p)))

nativeSixTraceUpper :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three) site →
  Six.nativeSixPlaneTraceSumAt dataSet site ≤ sixℚ
nativeSixTraceUpper dataSet site =
  subst
    (λ upper → Six.nativeSixPlaneTraceSumAt dataSet site ≤ upper)
    (nativeSixLengthPositiveOne site)
    (sumMapUpper
      (Plaquette.ownedPeriodicPlaquettes site)
      (λ p → SU2.realPart (Native.rationalSU2PlaquetteHolonomy dataSet p))
      1ℚ
      (λ p →
        Trace.normalizedTraceUpperBound
          (Native.rationalSU2PlaquetteHolonomy dataSet p)))

-- The two pointwise inequalities make the selected native action a
-- genuinely bounded rational observable, rather than a type-only map.
nativeSixDeficitAtNonnegative :
  ∀ dataSet site → 0ℚ ≤ Action.sixPhysicalDeficitAt dataSet site
nativeSixDeficitAtNonnegative dataSet site =
  let
    x = Six.nativeSixPlaneTraceSumAt dataSet site
    step : sixℚ + (- sixℚ) ≤ sixℚ + (- x)
    step =
      ℚP.+-mono-≤ ℚP.≤-refl
        (ℚP.neg-antimono-≤ (nativeSixTraceUpper dataSet site))
  in
  subst₂ _≤_
    (ℚRing.solve-∀)
    (ℚRing.solve-∀ x)
    step

nativeSixDeficitAtMostTwelve :
  ∀ dataSet site → Action.sixPhysicalDeficitAt dataSet site ≤ twelveℚ
nativeSixDeficitAtMostTwelve dataSet site =
  let
    x = Six.nativeSixPlaneTraceSumAt dataSet site
    step : sixℚ + (- x) ≤ sixℚ + (- (- sixℚ))
    step =
      ℚP.+-mono-≤ ℚP.≤-refl
        (ℚP.neg-antimono-≤ (nativeSixTraceLower dataSet site))
  in
  subst₂ _≤_
    (ℚRing.solve-∀ x)
    (ℚRing.solve-∀)
    step

-- Both closed arithmetic totals are exact, NOT asymptotic estimates.
sideFourZeroSum :
  Hodge.sumSites (λ _ → 0ℚ) ≡ 0ℚ
sideFourZeroSum = ℚRing.solve-∀

sideFourTwelveSum :
  Hodge.sumSites (λ _ → twelveℚ) ≡ threeThousandSeventyTwoℚ
sideFourTwelveSum = ℚRing.solve-∀

nativeSixDeficitNonnegative :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three) →
  0ℚ ≤ Action.sixPhysicalDeficitAction dataSet
nativeSixDeficitNonnegative dataSet =
  subst
    (λ lower → lower ≤ Action.sixPhysicalDeficitAction dataSet)
    sideFourZeroSum
    (SiteOrder.sumSitesMonotone _ _
      (nativeSixDeficitAtNonnegative dataSet))

nativeSixDeficitAtMost3072 :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three) →
  Action.sixPhysicalDeficitAction dataSet ≤ threeThousandSeventyTwoℚ
nativeSixDeficitAtMost3072 dataSet =
  subst
    (λ upper → Action.sixPhysicalDeficitAction dataSet ≤ upper)
    sideFourTwelveSum
    (SiteOrder.sumSitesMonotone _ _
      (nativeSixDeficitAtMostTwelve dataSet))
