module DASHI.Physics.Closure.NSTriadKNCenteredResolventSecondMomentAdapterExact where

------------------------------------------------------------------------
-- CENTERED RESOLVENT SYMBOL -> EXISTING TAYLOR / SECOND-MOMENT CARRIER
--
-- We do NOT identify the R571 radial multiplier with the centered resolvent
-- symbol.  Instead we reuse the exact generic Taylor carrier on the new symbol
--
--   J_a(s) = 1/a - 1/(a+s).
--
-- Preferred linearization mirrors the existing Gate-A choice:
--
--   L := J_a(s+h) - J_a(s).
--
-- Hence the plus remainder is definitionally zero.  The minus remainder is
--
--   J_a(s-h) - J_a(s) + L
-- = J_a(s+h) + J_a(s-h) - 2 J_a(s),
--
-- which the preceding owner proves is exactly
--
--   -2 h^2 / ((a+s)(a+s+h)(a+s-h)).
--
-- Thus the resolvent correction now inhabits the SAME generic Taylor
-- second-order representation used by R571, while remaining a distinct
-- physical symbol.  No radial-symbol equality is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierTaylorDifferenceExact as Taylor
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondOrderExact as Second
import DASHI.Physics.Closure.NSTriadKNCenteredResolventOppositeShiftSecondOrderExact as Resolvent

resolventSymbol :
  ℚ → ℚ → ℚ
resolventSymbol = Resolvent.centeredResolventDefectKernel

preferredResolventLinearIncrement :
  ℚ → ℚ → ℚ → ℚ
preferredResolventLinearIncrement a s h =
  resolventSymbol a (s + h) - resolventSymbol a s

resolventTaylorPair :
  ℚ → ℚ → ℚ → Taylor.MultiplierTaylorPair
resolventTaylorPair a s h =
  Taylor.multiplier-taylor-pair
    (resolventSymbol a s)
    (preferredResolventLinearIncrement a s h)
    0ℚ
    ( resolventSymbol a (s - h)
    - resolventSymbol a s
    + preferredResolventLinearIncrement a s h)

resolventTaylorPlusValueExact :
  (a s h : ℚ) →
  Taylor.plusValue (resolventTaylorPair a s h)
  ≡ resolventSymbol a (s + h)
resolventTaylorPlusValueExact a s h =
  solve
    ( resolventSymbol a s
    ∷ resolventSymbol a (s + h)
    ∷ [])

resolventTaylorMinusValueExact :
  (a s h : ℚ) →
  Taylor.minusValue (resolventTaylorPair a s h)
  ≡ resolventSymbol a (s - h)
resolventTaylorMinusValueExact a s h =
  solve
    ( resolventSymbol a s
    ∷ resolventSymbol a (s + h)
    ∷ resolventSymbol a (s - h)
    ∷ [])

resolventTaylorPlusRemainderZero :
  (a s h : ℚ) →
  Taylor.plusRemainder (resolventTaylorPair a s h) ≡ 0ℚ
resolventTaylorPlusRemainderZero a s h = refl

resolventTaylorMinusRemainderIsCenteredSecondDifference :
  (a s h : ℚ) →
  Taylor.minusRemainder (resolventTaylorPair a s h)
  ≡ Resolvent.centeredSecondDifference a s h
resolventTaylorMinusRemainderIsCenteredSecondDifference a s h =
  solve
    ( resolventSymbol a s
    ∷ resolventSymbol a (s + h)
    ∷ resolventSymbol a (s - h)
    ∷ [])

resolventTaylorCenteredSecondDifferenceExact :
  (a s h : ℚ) →
  Taylor.centeredSecondDifference (resolventTaylorPair a s h)
  ≡ Resolvent.centeredSecondDifference a s h
resolventTaylorCenteredSecondDifferenceExact a s h =
  trans
    (Taylor.centeredSecondDifferenceCancelsLinearSymbol
      (resolventTaylorPair a s h))
    (trans
      (resolventTaylorMinusRemainderIsCenteredSecondDifference a s h)
      (solve
        (Resolvent.centeredSecondDifference a s h ∷ [])))

resolventTaylorMinusRemainderSecondOrderExact :
  (a s h : ℚ) →
  (aPositive : Positive a) →
  (centerPositive : Positive (a + s)) →
  (plusPositive : Positive (a + (s + h))) →
  (minusPositive : Positive (a + (s - h))) →
  Taylor.minusRemainder (resolventTaylorPair a s h)
  ≡
  0ℚ
    - Resolvent.two * h * h
      * Resolvent.inv (a + s)
      * Resolvent.inv (a + (s + h))
      * Resolvent.inv (a + (s - h))
resolventTaylorMinusRemainderSecondOrderExact
    a s h aPositive centerPositive plusPositive minusPositive =
  trans
    (resolventTaylorMinusRemainderIsCenteredSecondDifference a s h)
    (Resolvent.oppositeShiftCenteredResolventSecondOrder
      a s h aPositive centerPositive plusPositive minusPositive)

resolventSecondOrderSample :
  (weight plusDerivative minusDerivative a s h : ℚ) →
  Second.PairedCommutatorSample
resolventSecondOrderSample
    weight plusDerivative minusDerivative a s h =
  Second.paired-commutator-sample
    weight
    (Taylor.center (resolventTaylorPair a s h))
    (Taylor.linearIncrement (resolventTaylorPair a s h))
    (Taylor.plusRemainder (resolventTaylorPair a s h))
    (Taylor.minusRemainder (resolventTaylorPair a s h))
    plusDerivative
    minusDerivative

resolventSecondOrderIdentity :
  (weight plusDerivative minusDerivative a s h : ℚ) →
  Second.pairedCommutator
    (resolventSecondOrderSample
      weight plusDerivative minusDerivative a s h)
  ≡
  Second.pairedSecondOrderDefect
    (resolventSecondOrderSample
      weight plusDerivative minusDerivative a s h)
resolventSecondOrderIdentity
    weight plusDerivative minusDerivative a s h =
  Second.pairedCommutatorSecondOrderIdentity
    (resolventSecondOrderSample
      weight plusDerivative minusDerivative a s h)

------------------------------------------------------------------------
-- Boundary: the generic second-moment representation is now shared.  What is
-- still missing is the physical map identifying the selected R290/R503 Gram
-- data with the derivative slots of this paired sample, plus the corresponding
-- state envelopes and cutoff-uniform aggregation.
------------------------------------------------------------------------

resolventUsesExistingTaylorCarrier : Bool
resolventUsesExistingTaylorCarrier = true

resolventPreferredPlusRemainderZero : Bool
resolventPreferredPlusRemainderZero = true

resolventMinusRemainderQuadraticBeforeAbsoluteValue : Bool
resolventMinusRemainderQuadraticBeforeAbsoluteValue = true

r571RadialSymbolEqualsResolventSymbol : Bool
r571RadialSymbolEqualsResolventSymbol = false

physicalGramDerivativeSlotWeldClosedHere : Bool
physicalGramDerivativeSlotWeldClosedHere = false

cutoffUniformSecondMomentAggregationClosedHere : Bool
cutoffUniformSecondMomentAggregationClosedHere = false

clayPromotion : Bool
clayPromotion = false

resolventUsesExistingTaylorCarrierIsTrue :
  resolventUsesExistingTaylorCarrier ≡ true
resolventUsesExistingTaylorCarrierIsTrue = refl

r571RadialSymbolEqualsResolventSymbolIsFalse :
  r571RadialSymbolEqualsResolventSymbol ≡ false
r571RadialSymbolEqualsResolventSymbolIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
