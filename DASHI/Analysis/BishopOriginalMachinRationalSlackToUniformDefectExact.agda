module DASHI.Analysis.BishopOriginalMachinRationalSlackToUniformDefectExact where

-- ORIGINAL, FINITE, AND SAME-CARRIER K05-PI COARSE CLOSURE.
--
-- Given only the original half-radius ONE-TERM normalization
--   qRadiusTerm(k) = 2*k / 4^k,
-- the positive Nat slack certificate computes ALL N stage sums.
-- No global upper-bound assumption or analytic limit is introduced.
--
-- Fully constructive finite pathway:
--   original K04d second power quotient
--   -> original Bishop radiusTerm (Readback.qRadiusTerm)
--   -> exact rational term shape (single producer)
--   -> original sum = positive slack finite fraction (by induction)
--   -> 8/9 order, native Bishop transport, signed second modulus
--   -> original uniform finite derivative defect.
--
-- The single shape producer is source-written in companion Lean
-- Integration/Paper9MachinSecondDefectMajorant.lean, but this Agda
-- module does NOT treat the Lean proof as a native Agda proof.
-- KERNEL PENDING.

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (ℚᵘ; _/_; _≃_; _≤_; _+_; *≡*)
import Data.Rational.Unnormalised.Properties as QP
import DASHI.Analysis.BishopOriginalMachinSecondRadiusRationalReadbackExact as Original
import DASHI.Analysis.BishopOriginalMachinPositiveSlackBudgetExact as Slack
import DASHI.Analysis.BishopOriginalMachinSharpUniformDefectConsumerExact as Consumer

-- A finite, original-Q, *per term* equation; strictly narrower than
-- the original unproved ALL-index budget order. Neither a postulate
-- nor a redefinition of the target series.
record OriginalHalfRadiusTermNormalization : Set where
  field
    normalize :
      (k : Nat) →
      Q._≃_
        (Original.qRadiusTerm k)
        (+ (2 * k) / Slack.powerFour k)

module FromTermNormalization (input : OriginalHalfRadiusTermNormalization) where
  open OriginalHalfRadiusTermNormalization input

  qRadiusBudgetEqualsPositiveSlack :
    (n : Nat) →
    Q._≃_ (Original.qRadiusBudget n) (Slack.positiveBudget n)
  qRadiusBudgetEqualsPositiveSlack zero = Q.*≡* refl
  qRadiusBudgetEqualsPositiveSlack (suc n) =
    QP.≃-trans
      (QP.+-cong
        (qRadiusBudgetEqualsPositiveSlack n)
        (normalize n))
      (QP.≃-sym (Slack.positiveBudgetStep n))

  -- Unlike the earlier OriginalRationalBudgetOrder record, there is
  -- no assumed upper bound: it is DERIVED from Nat slack positivity
  -- and the literal original per-term normalization.
  originalBudgetOrder :
    Consumer.OriginalRationalBudgetOrder
  originalBudgetOrder = record
    { radiusBudgetBelow = λ n →
        QP.≤-respˡ-≃
          (qRadiusBudgetEqualsPositiveSlack n)
          (Slack.positiveBudgetBelowEightNinths n)
    }

  module Native = Consumer.FromExactRationalOrder originalBudgetOrder

  -- The actual source-theorem Native.originalSignedSecondBelowEightNinths
  -- and Native.originalFiniteDerivativeUniformModulus are now available
  -- to clients with the ONE source-term shape producer, retaining both
  -- Machin evaluation points, signed h and the original Bishop real.
