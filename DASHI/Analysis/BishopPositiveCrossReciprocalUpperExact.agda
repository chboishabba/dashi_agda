module DASHI.Analysis.BishopPositiveCrossReciprocalUpperExact where

------------------------------------------------------------------------
-- POSITIVE CROSS-MULTIPLICATION -> RECIPROCAL UPPER BOUND
--
-- Constructively, do not assume a global inverse-antitone theorem.
--
--   0 < a
--   0 < d
--   a <= c*d
--
-- implies
--
--   d^{-1} <= c*a^{-1}
--
-- by multiplying first by the positive inverse of d and then by the positive
-- inverse of a, cancelling only with explicit inverse laws.
------------------------------------------------------------------------

open import Data.Sum.Base using (inj₂)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

positiveNonzero :
  ∀ {x : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._≄0 x
positiveNonzero positive = inj₂ positive

positiveInverse :
  ∀ {x : BishopReal.ℝ} →
  (positive : BishopReal._<_ BishopReal.0ℝ x) →
  BishopReal.ℝ
positiveInverse {x} positive =
  BishopInverse._⁻¹ x (positiveNonzero positive)

positiveInverseNonnegative :
  ∀ {x : BishopReal.ℝ} →
  (positive : BishopReal._<_ BishopReal.0ℝ x) →
  BishopReal.NonNegative (positiveInverse positive)
positiveInverseNonnegative positive =
  BishopP.pos⇒nonNeg
    (BishopInverse.posx⇒posx⁻¹
      (positiveNonzero positive)
      (BishopP.0<x⇒posx positive))

positiveCrossReciprocalUpper :
  ∀ {a c d : BishopReal.ℝ} →
  (aPositive : BishopReal._<_ BishopReal.0ℝ a) →
  (dPositive : BishopReal._<_ BishopReal.0ℝ d) →
  BishopReal._≤_ a (BishopReal._*_ c d) →
  BishopReal._≤_
    (positiveInverse dPositive)
    (BishopReal._*_ c (positiveInverse aPositive))
positiveCrossReciprocalUpper {a} {c} {d}
    aPositive dPositive crossBound =
  let
    invA = positiveInverse aPositive
    invD = positiveInverse dPositive

    scaleByInvD :
      BishopReal._≤_
        (BishopReal._*_ a invD)
        (BishopReal._*_ (BishopReal._*_ c d) invD)
    scaleByInvD =
      BishopP.*-monoʳ-≤-nonNeg
        crossBound
        (positiveInverseNonnegative dPositive)

    cancelD :
      BishopReal._≃_
        (BishopReal._*_ (BishopReal._*_ c d) invD)
        c
    cancelD =
      BishopP.≃-trans
        (BishopP.*-assoc c d invD)
        (BishopP.≃-trans
          (BishopP.*-congˡ
            (BishopInverse.*-inverseʳ d
              (positiveNonzero dPositive)))
          (BishopP.*-identityʳ c))

    belowC :
      BishopReal._≤_
        (BishopReal._*_ a invD)
        c
    belowC =
      BishopP.≤-respʳ-≃ cancelD scaleByInvD

    scaleByInvA :
      BishopReal._≤_
        (BishopReal._*_ (BishopReal._*_ a invD) invA)
        (BishopReal._*_ c invA)
    scaleByInvA =
      BishopP.*-monoʳ-≤-nonNeg
        belowC
        (positiveInverseNonnegative aPositive)

    cancelA :
      BishopReal._≃_
        (BishopReal._*_ (BishopReal._*_ a invD) invA)
        invD
    cancelA =
      let
        inverseLaw =
          BishopInverse.*-inverseʳ a
            (positiveNonzero aPositive)
        open BishopP.ℝ-Solver
      in
      BishopP.≃-trans
        (solve 3
          (λ a′ dInv aInv →
            (a′ ⊗ dInv) ⊗ aInv
            ⊜ dInv ⊗ (a′ ⊗ aInv))
          BishopP.≃-refl a invD invA)
        (BishopP.≃-trans
          (BishopP.*-congˡ inverseLaw)
          (BishopP.*-identityʳ invD))
  in
  BishopP.≤-respˡ-≃
    cancelA
    scaleByInvA
