module DASHI.Foundations.BishopPositiveInverseUpperFromLowerExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE BISHOP POSITIVE-INVERSE ANTITONE UPPER COMPILER.
--
-- Source law, not a new field or quotient: for d>0 and L<=d,
-- choose any U>=0 with L*U ~= 1. Then d^-1 <= U.
--
-- This is the same original Bishop reciprocal cross-multiplication
-- argument already used for the Newton denominator lower enclosure,
-- factored out ONCE for the P1.L selected p and (1-|u|) denominators.
-- Only imported Murray/Csimma Bishop inverse and ordered ring laws.
--
-- Source-written; pinned Agda 2.9 kernel check pending.
------------------------------------------------------------------------

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

positiveInverseBelowSupersolution :
  (denominator lower upper : BishopReal.ℝ) →
  (nonzero : BishopReal._≄0 denominator) →
  BishopReal._<_ BishopReal.0ℝ denominator →
  BishopReal._≤_ lower denominator →
  BishopReal.NonNegative upper →
  BishopReal._≃_ (BishopReal._*_ lower upper) BishopReal.1ℝ →
  BishopReal._≤_ (BishopInverse._⁻¹ denominator nonzero) upper
positiveInverseBelowSupersolution
    denominator lower upper nonzero denominatorPositive
    lowerBelow upperNN leftRightOne =
  let
    inverse = BishopInverse._⁻¹ denominator nonzero
    inverseNN =
      BishopP.pos⇒nonNeg
        (BishopP.0<x⇒posx
          (BishopInverse.0<x⇒0<x⁻¹ nonzero denominatorPositive))

    lowerScaled =
      BishopP.*-monoʳ-≤-nonNeg lowerBelow inverseNN

    scaledBelowOne =
      BishopP.≤-respʳ-≃
        (BishopInverse.*-inverseʳ denominator nonzero)
        lowerScaled

    scaledBelowUpper =
      BishopP.*-monoʳ-≤-nonNeg
        scaledBelowOne upperNN

    leftIsInverse =
      BishopP.≃-trans
        (let open BishopP.ℝ-Solver in
         solve 3
           (λ l x u →
             ((l ⊗ x) ⊗ u)
             ⊜ (x ⊗ (l ⊗ u)))
           BishopP.≃-refl lower inverse upper)
        (BishopP.≃-trans
          (BishopP.*-congˡ leftRightOne)
          (BishopP.*-identityʳ inverse))
  in
  BishopP.≤-respʳ-≃
    (BishopP.*-identityˡ upper)
    (BishopP.≤-respˡ-≃ leftIsInverse scaledBelowUpper)
