module DASHI.Physics.Closure.NSTriadKNCenteredResolventOppositeShiftSecondOrderExact where

------------------------------------------------------------------------
-- CENTERED RESOLVENT OPPOSITE-SHIFT SECOND-ORDER CANCELLATION
--
-- Write
--
--   J_a(s) = 1/a - 1/(a+s).
--
-- This is exactly the positive centered-resolvent kernel s/[a(a+s)] on
-- positive denominators.  For opposite residual shifts +/-h,
--
--   J_a(s+h) + J_a(s-h) - 2 J_a(s)
--
-- the first-order reciprocal defects cancel.  Three applications of the exact
-- reciprocal-difference factorization give
--
--   = -2 h^2
--       / ((a+s)(a+s+h)(a+s-h)).
--
-- This is the direct resolvent analogue of the R571 opposite-shift/Taylor
-- mechanism: the paired defect is genuinely SECOND ORDER before any absolute
-- value is taken.
--
-- No differentiability authority, asymptotic Taylor theorem, shell count,
-- cutoff factor, or Clay promotion is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; Positive; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal
import DASHI.Physics.Closure.NSTriadKNCyclicResolventDefectFactorizationBidiExact as Defect
import DASHI.Physics.Closure.NSTriadKNCenteredResolventKernelEnvelopeExact as Kernel

inv : ℚ → ℚ
inv = Reciprocal.safeRationalReciprocal

two : ℚ
two = 1ℚ + 1ℚ

centeredResolventDefectKernel :
  ℚ → ℚ → ℚ
centeredResolventDefectKernel a s =
  inv a - inv (a + s)

centeredSecondDifference :
  ℚ → ℚ → ℚ → ℚ
centeredSecondDifference a s h =
    centeredResolventDefectKernel a (s + h)
  + centeredResolventDefectKernel a (s - h)
  - two * centeredResolventDefectKernel a s

centeredResolventDefectKernelIsProduct :
  (a s : ℚ) →
  (aPositive : Positive a) →
  (aPlusSPositive : Positive (a + s)) →
  centeredResolventDefectKernel a s
  ≡ inv (a + s) * inv a * s
centeredResolventDefectKernelIsProduct
    a s aPositive aPlusSPositive =
  trans
    (Defect.reciprocalDifferenceFactorization
      (a + s) a aPlusSPositive aPositive)
    (solve (inv (a + s) ∷ inv a ∷ a ∷ s ∷ []))

oppositeShiftCenteredResolventSecondOrder :
  (a s h : ℚ) →
  (aPositive : Positive a) →
  (centerPositive : Positive (a + s)) →
  (plusPositive : Positive (a + (s + h))) →
  (minusPositive : Positive (a + (s - h))) →
  centeredSecondDifference a s h
  ≡
  0ℚ
    - two * h * h
      * inv (a + s)
      * inv (a + (s + h))
      * inv (a + (s - h))
oppositeShiftCenteredResolventSecondOrder
    a s h aPositive centerPositive plusPositive minusPositive =
  let
    x = a + s
    xp = a + (s + h)
    xm = a + (s - h)

    center = inv x
    plus = inv xp
    minus = inv xm

    plusDefect :
      center - plus
      ≡ center * plus * h
    plusDefect =
      trans
        (Defect.reciprocalDifferenceFactorization
          xp x plusPositive centerPositive)
        (solve (center ∷ plus ∷ a ∷ s ∷ h ∷ []))

    minusDefect :
      center - minus
      ≡ 0ℚ - center * minus * h
    minusDefect =
      trans
        (Defect.reciprocalDifferenceFactorization
          xm x minusPositive centerPositive)
        (solve (center ∷ minus ∷ a ∷ s ∷ h ∷ []))

    shiftedKernelPair :
      centeredSecondDifference a s h
      ≡ (center - plus) + (center - minus)
    shiftedKernelPair =
      solve
        ( inv a
        ∷ center
        ∷ plus
        ∷ minus
        ∷ [])

    afterFirstDefects :
      (center - plus) + (center - minus)
      ≡ center * h * (plus - minus)
    afterFirstDefects =
      trans
        (cong₂ _+_ plusDefect minusDefect)
        (solve (center ∷ plus ∷ minus ∷ h ∷ []))

    shiftedReciprocalDifference :
      plus - minus
      ≡ 0ℚ - two * h * plus * minus
    shiftedReciprocalDifference =
      trans
        (Defect.reciprocalDifferenceFactorization
          xm xp minusPositive plusPositive)
        (solve (plus ∷ minus ∷ a ∷ s ∷ h ∷ []))

    finish :
      center * h * (plus - minus)
      ≡
      0ℚ
        - two * h * h
          * center * plus * minus
    finish =
      trans
        (cong (center * h *_) shiftedReciprocalDifference)
        (solve (center ∷ plus ∷ minus ∷ h ∷ []))
  in
  trans shiftedKernelPair
    (trans afterFirstDefects finish)

------------------------------------------------------------------------
-- The theorem above is the exact analytic bridge we need.  In particular the
-- linear-in-h term is absent from the paired resolvent defect.  A later
-- physical producer may now feed h^2 into the existing second-moment machinery
-- without claiming that R571's radial symbol and this resolvent symbol are
-- definitionally identical.
------------------------------------------------------------------------

oppositeShiftLinearTermCancelsExactly : Bool
oppositeShiftLinearTermCancelsExactly = true

oppositeShiftResolventDefectIsSecondOrder : Bool
oppositeShiftResolventDefectIsSecondOrder = true

requiresDifferentiabilityAuthority : Bool
requiresDifferentiabilityAuthority = false

requiresAbsoluteValueBeforeCancellation : Bool
requiresAbsoluteValueBeforeCancellation = false

physicalSecondMomentWeldClosedHere : Bool
physicalSecondMomentWeldClosedHere = false

cutoffUniformCorrectionPaymentClosedHere : Bool
cutoffUniformCorrectionPaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

oppositeShiftResolventDefectIsSecondOrderIsTrue :
  oppositeShiftResolventDefectIsSecondOrder ≡ true
oppositeShiftResolventDefectIsSecondOrderIsTrue = refl

requiresAbsoluteValueBeforeCancellationIsFalse :
  requiresAbsoluteValueBeforeCancellation ≡ false
requiresAbsoluteValueBeforeCancellationIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
