module DASHI.Physics.Closure.NSTriadKNEuclideanCenteredResolventScaleRelativeExact where

------------------------------------------------------------------------
-- A / CONTINUOUS SCALE-RELATIVE RESOLVENT CURVATURE
--
-- Periodic B used the lattice floor |k|^2 >= 1 to turn the exact local
-- curvature 2/a^3, a = nu |k|^2, into the global constant 2/nu^3.
--
-- Whole-space A cannot do that near xi = 0.  The correct portable statement is
-- scale-relative:
--
--   if 0 < floor <= a,
--   then 2/a^3 <= 2/floor^3.
--
-- On a continuous shell |xi| >= lambda this is consumed with
--
--   floor = nu lambda^2.
--
-- Nothing here assumes a lattice gap.  The theorem is exactly the high-output
-- half of the Euclidean low/high decomposition requested by the A roadmap.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; NonNegative; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNCenteredResolventOppositeShiftSecondOrderExact as Resolvent
import DASHI.Physics.Closure.NSTriadKNCenteredResolventSecondOrderEnvelopeExact as Envelope

scaleRelativeCurvature :
  ℚ → ℚ
scaleRelativeCurvature floor =
  Envelope.two
    * Resolvent.inv floor
    * Resolvent.inv floor
    * Resolvent.inv floor

scaleRelativeCurvatureBound :
  (floor a : ℚ) →
  (floorPositive : 0ℚ < floor) →
  (aPositive : 0ℚ < a) →
  floor ≤ a →
  Envelope.resolventTransportCurvature a
  ≤ scaleRelativeCurvature floor
scaleRelativeCurvatureBound
    floor a floorPositive aPositive floorBelowA =
  let
    triple =
      Envelope.tripleInverseBound
        floor a a a
        floorPositive aPositive aPositive aPositive
        floorBelowA floorBelowA floorBelowA

    twoNN : 0ℚ ≤ Envelope.two
    twoNN = Envelope.twoNonnegative

    instance
      twoNNI : NonNegative Envelope.two
      twoNNI = nonNegative twoNN

    scaled :
      Envelope.two
        * (Resolvent.inv a * Resolvent.inv a * Resolvent.inv a)
      ≤
      Envelope.two
        * (Resolvent.inv floor * Resolvent.inv floor * Resolvent.inv floor)
    scaled =
      ℚP.*-monoˡ-≤-nonNeg Envelope.two triple
  in
  subst
    (Envelope.resolventTransportCurvature a ≤_)
    (solve (Envelope.two ∷ Resolvent.inv floor ∷ []))
    (subst
      (λ lhs →
        lhs
        ≤
        Envelope.two
          * (Resolvent.inv floor * Resolvent.inv floor * Resolvent.inv floor))
      (solve (Envelope.two ∷ Resolvent.inv a ∷ []))
      scaled)

record EuclideanOutputScaleFloor : Set where
  constructor euclidean-output-scale-floor
  field
    outputHeatRate : ℚ
    shellHeatFloor : ℚ
    shellHeatFloorPositive : 0ℚ < shellHeatFloor
    outputHeatRatePositive : 0ℚ < outputHeatRate
    shellHeatFloorBelowOutput :
      shellHeatFloor ≤ outputHeatRate

open EuclideanOutputScaleFloor public

shellRelativeCurvatureBound :
  (S : EuclideanOutputScaleFloor) →
  Envelope.resolventTransportCurvature (outputHeatRate S)
  ≤ scaleRelativeCurvature (shellHeatFloor S)
shellRelativeCurvatureBound S =
  scaleRelativeCurvatureBound
    (shellHeatFloor S)
    (outputHeatRate S)
    (shellHeatFloorPositive S)
    (outputHeatRatePositive S)
    (shellHeatFloorBelowOutput S)

------------------------------------------------------------------------
-- Near xi = 0 we deliberately DO NOT instantiate shellHeatFloor by a fixed
-- positive number.  The low-frequency producer must instead retain the full
-- product and recover enough positive frequency power from state/commutator
-- geometry before division.
------------------------------------------------------------------------

euclideanHighFrequencyScaleRelativeCurvatureClosed : Bool
euclideanHighFrequencyScaleRelativeCurvatureClosed = true

euclideanUsesPeriodicUnitGap : Bool
euclideanUsesPeriodicUnitGap = false

euclideanLowFrequencyUniformCurvatureClaimed : Bool
euclideanLowFrequencyUniformCurvatureClaimed = false

euclideanLowFrequencyCompleteIntegrandPaymentClosedHere : Bool
euclideanLowFrequencyCompleteIntegrandPaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

euclideanHighFrequencyScaleRelativeCurvatureClosedIsTrue :
  euclideanHighFrequencyScaleRelativeCurvatureClosed ≡ true
euclideanHighFrequencyScaleRelativeCurvatureClosedIsTrue = refl

euclideanUsesPeriodicUnitGapIsFalse :
  euclideanUsesPeriodicUnitGap ≡ false
euclideanUsesPeriodicUnitGapIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
