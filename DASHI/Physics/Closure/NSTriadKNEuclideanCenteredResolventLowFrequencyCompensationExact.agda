module DASHI.Physics.Closure.NSTriadKNEuclideanCenteredResolventLowFrequencyCompensationExact where

------------------------------------------------------------------------
-- A / LOW-FREQUENCY PRODUCT COMPENSATION
--
-- The continuous resolvent curvature behaves like
--
--   2 / a^3,     a = nu |xi|^2.
--
-- Near xi = 0 this MUST NOT be bounded in isolation.  This owner proves the
-- exact algebraic compensation target for the complete integrand:
--
--   stateFactor <= a^3 M
--        =>
--   (2/a^3) stateFactor <= 2 M.
--
-- Thus three powers of the heat rate -- equivalently six powers of |xi| when
-- a = nu |xi|^2 -- neutralize the apparent low-frequency singularity exactly.
--
-- This does not assert that the physical Gram/state geometry already supplies
-- a^3.  It turns that question into the precise same-object producer required
-- from Leray/transversality/G2 geometry before Lebesgue aggregation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; NonNegative; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNCenteredResolventOppositeShiftSecondOrderExact as Resolvent
import DASHI.Physics.Closure.NSTriadKNCenteredResolventSecondOrderEnvelopeExact as Envelope
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient
import DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact as R449

heatCube : ℚ → ℚ
heatCube a = a * a * a

curvature : ℚ → ℚ
curvature a =
  Envelope.two
    * Resolvent.inv a
    * Resolvent.inv a
    * Resolvent.inv a

safeInverseTimesPositive :
  (a : ℚ) →
  (aPositive : 0ℚ < a) →
  Resolvent.inv a * a ≡ 1ℚ
safeInverseTimesPositive a aPositive =
  let
    safeToPositive =
      R449.safeReciprocalIsPositiveReciprocal a aPositive
    rightInverse =
      Quotient.positiveReciprocalRightInverse a aPositive
  in
  trans
    (cong (_* a) safeToPositive)
    (trans
      (ℚP.*-comm
        (Quotient.positiveReciprocal a aPositive) a)
      rightInverse)

curvatureTimesHeatCube :
  (a M : ℚ) →
  (aPositive : 0ℚ < a) →
  curvature a * (heatCube a * M)
  ≡ Envelope.two * M
curvatureTimesHeatCube a M aPositive =
  let
    ia = Resolvent.inv a
    inverseLaw : ia * a ≡ 1ℚ
    inverseLaw = safeInverseTimesPositive a aPositive

    rearranged :
      curvature a * (heatCube a * M)
      ≡
      Envelope.two
        * ((ia * a) * (ia * a) * (ia * a))
        * M
    rearranged =
      solve (Envelope.two ∷ ia ∷ a ∷ M ∷ [])

    collapsed :
      Envelope.two
        * ((ia * a) * (ia * a) * (ia * a))
        * M
      ≡ Envelope.two * M
    collapsed
      rewrite inverseLaw =
      solve (Envelope.two ∷ M ∷ [])
  in
  trans rearranged collapsed

record LowFrequencyStateCompensation
    (a stateFactor majorant : ℚ) : Set where
  constructor low-frequency-state-compensation
  field
    aPositive : 0ℚ < a
    stateFactorNonnegative : 0ℚ ≤ stateFactor
    majorantNonnegative : 0ℚ ≤ majorant
    stateCarriesHeatCube :
      stateFactor ≤ heatCube a * majorant

open LowFrequencyStateCompensation public

completeProductLowFrequencyBound :
  (a stateFactor majorant : ℚ) →
  (payment : LowFrequencyStateCompensation a stateFactor majorant) →
  curvature a * stateFactor
  ≤ Envelope.two * majorant
completeProductLowFrequencyBound a stateFactor majorant payment =
  let
    iaNN = Envelope.safeInvNonnegative a (aPositive payment)

    ia2NN : 0ℚ ≤ Resolvent.inv a * Resolvent.inv a
    ia2NN =
      let
        instance
          leftNN : NonNegative (Resolvent.inv a)
          leftNN = nonNegative iaNN
      in
      ℚP.*-monoˡ-≤-nonNeg
        (Resolvent.inv a)
        iaNN

    ia3NN : 0ℚ ≤ Resolvent.inv a * Resolvent.inv a * Resolvent.inv a
    ia3NN =
      let
        instance
          leftNN : NonNegative
            (Resolvent.inv a * Resolvent.inv a)
          leftNN = nonNegative ia2NN
      in
      ℚP.*-monoˡ-≤-nonNeg
        (Resolvent.inv a * Resolvent.inv a)
        iaNN

    curvatureNN : 0ℚ ≤ curvature a
    curvatureNN =
      let
        twoNN = Envelope.twoNonnegative
        instance
          twoNNI : NonNegative Envelope.two
          twoNNI = nonNegative twoNN
      in
      subst
        (0ℚ ≤_)
        (solve
          ( Envelope.two
          ∷ Resolvent.inv a
          ∷ []))
        (ℚP.*-monoˡ-≤-nonNeg Envelope.two ia3NN)

    scaled :
      curvature a * stateFactor
      ≤ curvature a * (heatCube a * majorant)
    scaled =
      let
        instance
          curvatureNNI : NonNegative (curvature a)
          curvatureNNI = nonNegative curvatureNN
      in
      ℚP.*-monoˡ-≤-nonNeg
        (curvature a)
        (stateCarriesHeatCube payment)
  in
  subst
    (curvature a * stateFactor ≤_)
    (curvatureTimesHeatCube a majorant (aPositive payment))
    scaled

euclideanLowFrequencyCubicHeatCompensationClosed : Bool
euclideanLowFrequencyCubicHeatCompensationClosed = true

requiredFrequencyPowerAtHeatRateNuXiSquared : ℚ
requiredFrequencyPowerAtHeatRateNuXiSquared = 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ

lowFrequencyUniformCurvatureClaimed : Bool
lowFrequencyUniformCurvatureClaimed = false

physicalStateSuppliesHeatCubeClosedHere : Bool
physicalStateSuppliesHeatCubeClosedHere = false

lebesgueLowFrequencySummabilityClosedHere : Bool
lebesgueLowFrequencySummabilityClosedHere = false

clayPromotion : Bool
clayPromotion = false

euclideanLowFrequencyCubicHeatCompensationClosedIsTrue :
  euclideanLowFrequencyCubicHeatCompensationClosed ≡ true
euclideanLowFrequencyCubicHeatCompensationClosedIsTrue = refl

lowFrequencyUniformCurvatureClaimedIsFalse :
  lowFrequencyUniformCurvatureClaimed ≡ false
lowFrequencyUniformCurvatureClaimedIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
