module DASHI.Physics.Closure.NSWholeSpaceCenteredResolventOppositeShiftSecondOrderExact where

------------------------------------------------------------------------
-- A / BISHOP-REAL CENTERED RESOLVENT OPPOSITE-SHIFT IDENTITY
--
-- The rational periodic owner proves
--
--   J_a(s+h) + J_a(s-h) - 2 J_a(s)
--      = -2 h^2 / ((a+s)(a+s+h)(a+s-h)).
--
-- This owner proves the SAME algebra on the Bishop-real carrier used by the
-- literal Euclidean Fourier trajectory.  It consumes only positivity/nonzero
-- witnesses for the four denominators; no lattice gap, shell count, Taylor
-- theorem, or periodic transport is used.
--
-- This removes the last scalar-carrier mismatch in the domain-independent
-- opposite-shift cancellation.  The remaining A-specific theorem is now
-- genuinely physical: identify the residual shift h produced by the
-- continuous Gram/resolvent state and prove the measure-aware h^2 payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal

two : BishopReal.ℝ
two = BishopReal._+_ BishopReal.1ℝ BishopReal.1ℝ

inverse :
  (x : BishopReal.ℝ) →
  BishopReal._≄0 x →
  BishopReal.ℝ
inverse = BishopInverse._⁻¹

record PositiveDenominator : Set where
  constructor positive-denominator
  field
    value : BishopReal.ℝ
    positive : BishopReal._<_ BishopReal.0ℝ value

open PositiveDenominator public

nonzero :
  (D : PositiveDenominator) →
  BishopReal._≄0 (value D)
nonzero D = Reciprocal.xNonzero (positive D)

reciprocal :
  PositiveDenominator → BishopReal.ℝ
reciprocal D = inverse (value D) (nonzero D)

reciprocalDifference :
  (left right : PositiveDenominator) →
  BishopReal._≃_
    (BishopReal._-_
      (reciprocal right)
      (reciprocal left))
    (BishopReal._*_
      (BishopReal._*_
        (reciprocal right)
        (reciprocal left))
      (BishopReal._-_
        (value left)
        (value right)))
reciprocalDifference left right =
  let
    l = value left
    r = value right
    il = reciprocal left
    ir = reciprocal right

    lInv = BishopInverse.*-inverseˡ l (nonzero left)
    rInv = BishopInverse.*-inverseˡ r (nonzero right)

    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 4
      (λ l' r' il' ir' →
        ir' ⊖ il'
        ⊜
        (ir' ⊗ il') ⊗
          ((l' ⊗ ir') ⊖ (r' ⊗ il')))
      BishopP.≃-refl
      l r il ir)
    (BishopP.*-congˡ
      (BishopP.-cong lInv rInv))

record CenteredResolventShift : Set where
  constructor centered-resolvent-shift
  field
    a s h : BishopReal.ℝ

    basePositive :
      BishopReal._<_ BishopReal.0ℝ a
    centerPositive :
      BishopReal._<_ BishopReal.0ℝ
        (BishopReal._+_ a s)
    plusPositive :
      BishopReal._<_ BishopReal.0ℝ
        (BishopReal._+_ a (BishopReal._+_ s h))
    minusPositive :
      BishopReal._<_ BishopReal.0ℝ
        (BishopReal._+_ a (BishopReal._-_ s h))

open CenteredResolventShift public

baseD : CenteredResolventShift → PositiveDenominator
baseD D = positive-denominator (a D) (basePositive D)

centerD : CenteredResolventShift → PositiveDenominator
centerD D =
  positive-denominator
    (BishopReal._+_ (a D) (s D))
    (centerPositive D)

plusD : CenteredResolventShift → PositiveDenominator
plusD D =
  positive-denominator
    (BishopReal._+_
      (a D)
      (BishopReal._+_ (s D) (h D)))
    (plusPositive D)

minusD : CenteredResolventShift → PositiveDenominator
minusD D =
  positive-denominator
    (BishopReal._+_
      (a D)
      (BishopReal._-_ (s D) (h D)))
    (minusPositive D)

centeredResolventDefect :
  CenteredResolventShift →
  PositiveDenominator →
  BishopReal.ℝ
centeredResolventDefect D shifted =
  BishopReal._-_
    (reciprocal (baseD D))
    (reciprocal shifted)

centeredSecondDifference :
  CenteredResolventShift → BishopReal.ℝ
centeredSecondDifference D =
  BishopReal._-_
    (BishopReal._+_
      (centeredResolventDefect D (plusD D))
      (centeredResolventDefect D (minusD D)))
    (BishopReal._*_
      two
      (centeredResolventDefect D (centerD D)))

oppositeShiftSecondOrderExact :
  (D : CenteredResolventShift) →
  BishopReal._≃_
    (centeredSecondDifference D)
    (BishopReal.-_
      (BishopReal._*_
        (BishopReal._*_
          two
          (BishopReal._*_ (h D) (h D)))
        (BishopReal._*_
          (BishopReal._*_
            (reciprocal (centerD D))
            (reciprocal (plusD D)))
          (reciprocal (minusD D)))))
oppositeShiftSecondOrderExact D =
  let
    a' = a D
    s' = s D
    h' = h D

    c = reciprocal (centerD D)
    p = reciprocal (plusD D)
    m = reciprocal (minusD D)
    b = reciprocal (baseD D)

    plusDefect :
      BishopReal._≃_
        (BishopReal._-_ c p)
        (BishopReal._*_
          (BishopReal._*_ c p)
          h')
    plusDefect =
      BishopP.≃-trans
        (reciprocalDifference (plusD D) (centerD D))
        (let open BishopP.ℝ-Solver
         in solve 3
           (λ a0 s0 h0 →
             (a0 ⊕ (s0 ⊕ h0)) ⊖ (a0 ⊕ s0)
             ⊜ h0)
           BishopP.≃-refl
           a' s' h')

    minusDefect :
      BishopReal._≃_
        (BishopReal._-_ c m)
        (BishopReal.-_
          (BishopReal._*_
            (BishopReal._*_ c m)
            h'))
    minusDefect =
      BishopP.≃-trans
        (reciprocalDifference (minusD D) (centerD D))
        (let open BishopP.ℝ-Solver
         in solve 3
           (λ a0 s0 h0 →
             (a0 ⊕ (s0 ⊖ h0)) ⊖ (a0 ⊕ s0)
             ⊜ ⊝ h0)
           BishopP.≃-refl
           a' s' h')

    pairReduction :
      BishopReal._≃_
        (centeredSecondDifference D)
        (BishopReal._+_
          (BishopReal._-_ c p)
          (BishopReal._-_ c m))
    pairReduction =
      let open BishopP.ℝ-Solver
      in solve 4
        (λ b0 c0 p0 m0 →
          ((b0 ⊖ p0) ⊕ (b0 ⊖ m0))
          ⊖ ((BishopReal.1ℝ ⊕ BishopReal.1ℝ) ⊗ (b0 ⊖ c0))
          ⊜
          (c0 ⊖ p0) ⊕ (c0 ⊖ m0))
        BishopP.≃-refl
        b c p m

    firstOrderCancellation :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._-_ c p)
          (BishopReal._-_ c m))
        (BishopReal._*_
          (BishopReal._*_ c h')
          (BishopReal._-_ p m))
    firstOrderCancellation =
      BishopP.≃-trans
        (BishopP.+-cong plusDefect minusDefect)
        (let open BishopP.ℝ-Solver
         in solve 4
           (λ c0 p0 m0 h0 →
             ((c0 ⊗ p0) ⊗ h0)
             ⊕
             (⊝ ((c0 ⊗ m0) ⊗ h0))
             ⊜
             (c0 ⊗ h0) ⊗ (p0 ⊖ m0))
           BishopP.≃-refl
           c p m h')

    shiftedReciprocalDifference :
      BishopReal._≃_
        (BishopReal._-_ p m)
        (BishopReal.-_
          (BishopReal._*_
            (BishopReal._*
              two
              h')
            (BishopReal._*_ p m)))
    shiftedReciprocalDifference =
      BishopP.≃-trans
        (reciprocalDifference (minusD D) (plusD D))
        (let open BishopP.ℝ-Solver
         in solve 3
           (λ a0 s0 h0 →
             (a0 ⊕ (s0 ⊖ h0))
             ⊖
             (a0 ⊕ (s0 ⊕ h0))
             ⊜
             ⊝ ((BishopReal.1ℝ ⊕ BishopReal.1ℝ) ⊗ h0))
           BishopP.≃-refl
           a' s' h')

    finish :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._*_ c h')
          (BishopReal._-_ p m))
        (BishopReal.-_
          (BishopReal._*_
            (BishopReal._*_
              two
              (BishopReal._*_ h' h'))
            (BishopReal._*_
              (BishopReal._*_ c p)
              m)))
    finish =
      BishopP.≃-trans
        (BishopP.*-congˡ shiftedReciprocalDifference)
        (let open BishopP.ℝ-Solver
         in solve 4
           (λ c0 p0 m0 h0 →
             (c0 ⊗ h0)
             ⊗
             (⊝ (((BishopReal.1ℝ ⊕ BishopReal.1ℝ) ⊗ h0)
               ⊗ (p0 ⊗ m0)))
             ⊜
             ⊝
             (((BishopReal.1ℝ ⊕ BishopReal.1ℝ)
               ⊗ (h0 ⊗ h0))
              ⊗ ((c0 ⊗ p0) ⊗ m0)))
           BishopP.≃-refl
           c p m h')
  in
  BishopP.≃-trans
    pairReduction
    (BishopP.≃-trans
      firstOrderCancellation
      finish)

------------------------------------------------------------------------
-- Frontier: the exact second-order h^2 factor is now available on A's real
-- carrier.  A still needs a PHYSICAL residual-shift theorem relating this h to
-- the low-output geometry strongly enough for the R3 radial integrability
-- payment.  No identification h^2 ~ |xi|^2 is asserted here.
------------------------------------------------------------------------

bishopRealOppositeShiftCancellationClosed : Bool
bishopRealOppositeShiftCancellationClosed = true

linearResidualShiftCancelsBeforeAbsoluteValue : Bool
linearResidualShiftCancelsBeforeAbsoluteValue = true

physicalResidualShiftToOutputFrequencyClosedHere : Bool
physicalResidualShiftToOutputFrequencyClosedHere = false

clayPromotion : Bool
clayPromotion = false

bishopRealOppositeShiftCancellationClosedIsTrue :
  bishopRealOppositeShiftCancellationClosed ≡ true
bishopRealOppositeShiftCancellationClosedIsTrue = refl

physicalResidualShiftToOutputFrequencyClosedHereIsFalse :
  physicalResidualShiftToOutputFrequencyClosedHere ≡ false
physicalResidualShiftToOutputFrequencyClosedHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
