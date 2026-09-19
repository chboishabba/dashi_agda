module DASHI.Physics.Closure.NSWholeSpaceLowFrequencyCompensationExact where

------------------------------------------------------------------------
-- A / BISHOP-REAL LOW-FREQUENCY COMPENSATION
--
-- The earlier rational prototype proved the right algebraic shape but was not
-- the same scalar carrier as the literal Euclidean Fourier trajectory.  This
-- owner closes that mismatch on the canonical Bishop-real carrier.
--
-- For a > 0, write i = a^{-1}.  Then constructively
--
--   i^3 * (a^3 M) ~= M.
--
-- Hence any nonnegative state factor satisfying
--
--   state <= a^3 M
--
-- obeys
--
--   i^3 state <= M,
--
-- and after multiplication by any nonnegative coefficient c,
--
--   c i^3 state <= c M.
--
-- Taking c = 2 is exactly the centered-resolvent curvature payment.  When
-- a = nu |xi|^2, a^3 is the required |xi|^6 low-frequency compensation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal

inverse :
  (a : BishopReal.ℝ) → BishopReal._≄0 a → BishopReal.ℝ
inverse = BishopInverse._⁻¹

heatCube : BishopReal.ℝ → BishopReal.ℝ
heatCube a =
  BishopReal._*_
    (BishopReal._*_ a a)
    a

inverseCube :
  (a : BishopReal.ℝ) →
  (nonzero : BishopReal._≄0 a) →
  BishopReal.ℝ
inverseCube a nonzero =
  BishopReal._*_
    (BishopReal._*_
      (inverse a nonzero)
      (inverse a nonzero))
    (inverse a nonzero)

inverseCubePositive :
  ∀ {a} →
  (aPositive : BishopReal._<_ BishopReal.0ℝ a) →
  BishopReal.Positive
    (inverseCube a (Reciprocal.xNonzero aPositive))
inverseCubePositive {a} aPositive =
  let
    nz = Reciprocal.xNonzero aPositive
    invPos =
      BishopP.0<x⇒posx
        (BishopInverse.0<x⇒0<x⁻¹ nz aPositive)
    inv2Pos = BishopP.posx,y⇒posx*y invPos invPos
  in
  BishopP.posx,y⇒posx*y inv2Pos invPos

inverseCubeNonnegative :
  ∀ {a} →
  (aPositive : BishopReal._<_ BishopReal.0ℝ a) →
  BishopReal.NonNegative
    (inverseCube a (Reciprocal.xNonzero aPositive))
inverseCubeNonnegative aPositive =
  BishopP.pos⇒nonNeg (inverseCubePositive aPositive)

inverseCubeTimesHeatCube :
  (a M : BishopReal.ℝ) →
  (aPositive : BishopReal._<_ BishopReal.0ℝ a) →
  BishopReal._≃_
    (BishopReal._*_
      (inverseCube a (Reciprocal.xNonzero aPositive))
      (BishopReal._*_ (heatCube a) M))
    M
inverseCubeTimesHeatCube a M aPositive =
  let
    nz = Reciprocal.xNonzero aPositive
    ia = inverse a nz
    inverseLaw = BishopInverse.*-inverseˡ a nz
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 3
      (λ i a′ m →
        ((i ⊗ i) ⊗ i) ⊗ (((a′ ⊗ a′) ⊗ a′) ⊗ m)
        ⊜ ((i ⊗ a′) ⊗ (i ⊗ a′) ⊗ (i ⊗ a′)) ⊗ m)
      BishopP.≃-refl ia a M)
    (BishopP.≃-trans
      (BishopP.*-congˡ
        (BishopP.*-cong
          (BishopP.*-cong inverseLaw inverseLaw)
          inverseLaw))
      (BishopP.*-identityˡ M))

record BishopLowFrequencyStateCompensation
    (a stateFactor majorant : BishopReal.ℝ) : Set where
  constructor bishop-low-frequency-state-compensation
  field
    heatRatePositive :
      BishopReal._<_ BishopReal.0ℝ a

    stateFactorNonnegative :
      BishopReal.NonNegative stateFactor

    majorantNonnegative :
      BishopReal.NonNegative majorant

    stateCarriesHeatCube :
      BishopReal._≤_
        stateFactor
        (BishopReal._*_ (heatCube a) majorant)

open BishopLowFrequencyStateCompensation public

inverseCubeStateBound :
  (a stateFactor majorant : BishopReal.ℝ) →
  (payment : BishopLowFrequencyStateCompensation
    a stateFactor majorant) →
  BishopReal._≤_
    (BishopReal._*_
      (inverseCube a
        (Reciprocal.xNonzero (heatRatePositive payment)))
      stateFactor)
    majorant
inverseCubeStateBound a stateFactor majorant payment =
  let
    aPos = heatRatePositive payment
    nz = Reciprocal.xNonzero aPos
    inv3 = inverseCube a nz

    scaled :
      BishopReal._≤_
        (BishopReal._*_ inv3 stateFactor)
        (BishopReal._*_
          inv3
          (BishopReal._*_ (heatCube a) majorant))
    scaled =
      BishopP.*-monoˡ-≤-nonNeg
        (stateCarriesHeatCube payment)
        (inverseCubeNonnegative aPos)

    cancellation =
      inverseCubeTimesHeatCube a majorant aPos
  in
  BishopP.≤-respʳ-≃ cancellation scaled

coefficientScaledCompensation :
  (coefficient a stateFactor majorant : BishopReal.ℝ) →
  BishopReal.NonNegative coefficient →
  (payment : BishopLowFrequencyStateCompensation
    a stateFactor majorant) →
  BishopReal._≤_
    (BishopReal._*_
      coefficient
      (BishopReal._*_
        (inverseCube a
          (Reciprocal.xNonzero (heatRatePositive payment)))
        stateFactor))
    (BishopReal._*_ coefficient majorant)
coefficientScaledCompensation
    coefficient a stateFactor majorant coefficientNN payment =
  BishopP.*-monoˡ-≤-nonNeg
    (inverseCubeStateBound a stateFactor majorant payment)
    coefficientNN

------------------------------------------------------------------------
-- This is now on the same Bishop-real scalar carrier as the canonical
-- Euclidean Fourier trajectory.  The remaining physical theorem is not the
-- reciprocal algebra; it is the producer
--
--   stateFactor(xi,eta) <= a(xi)^3 M(xi,eta)
--
-- before absolute-value / Lebesgue aggregation.
------------------------------------------------------------------------

bishopRealHeatCubeCancellationClosed : Bool
bishopRealHeatCubeCancellationClosed = true

bishopRealLowFrequencyCompensationClosed : Bool
bishopRealLowFrequencyCompensationClosed = true

rationalPrototypeRequiredForA : Bool
rationalPrototypeRequiredForA = false

physicalStateSuppliesHeatCubeClosedHere : Bool
physicalStateSuppliesHeatCubeClosedHere = false

lebesgueSummabilityClosedHere : Bool
lebesgueSummabilityClosedHere = false

clayPromotion : Bool
clayPromotion = false

bishopRealLowFrequencyCompensationClosedIsTrue :
  bishopRealLowFrequencyCompensationClosed ≡ true
bishopRealLowFrequencyCompensationClosedIsTrue = refl

rationalPrototypeRequiredForAIsFalse :
  rationalPrototypeRequiredForA ≡ false
rationalPrototypeRequiredForAIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
