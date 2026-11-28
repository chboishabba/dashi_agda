module DASHI.Analysis.BishopOriginalMachinSecondRadiusRationalReadbackExact where

-- ORIGINAL BISHOP --> EXACT RATIONAL RADIUS READBACK, ALL FINITE N.
-- Source-written; Agda kernel execution pending.
--
-- qZero(n) and qSecond(n) are the literal K04d polynomial recurrences
-- at the ORIGINAL half radius. Their Bishop rational embeddings agree
-- with Power.powerDifferenceQuotient(half,0,n) and with the SAME
-- Second.sourcePowerSecondQuotient(half,0,n), for EVERY finite n.
-- No isolated precision, no new real series, no coercion to Mathlib pi.
--
-- qRadiusBudget is the actual finite rational recurrence underlying
-- Original.sourceRadiusBudget. The final rational closed form
-- qRadiusBudget(N) = 8/9*(1-(3N+1)/4^N)
-- is a separate exact rational arithmetic lemma (the companion Lean
-- code carries it). It is not assumed by this module.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised as Q
  using (ℚᵘ; 0ℚᵘ; _+_; _*_; _≃_)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopOriginalFiniteLogQuotientSecondOrderExact as Second
import DASHI.Analysis.BishopOriginalMachinSignedSecondRadiusEnvelopeExact as Envelope
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Stage
import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimate

qZero : Nat → ℚᵘ
qZero zero = 0ℚᵘ
qZero (suc n) =
  (qZero n Q.* Half.half)
    Q.+ Stage.qPow Half.half n

qSecond : Nat → ℚᵘ
qSecond zero = 0ℚᵘ
qSecond (suc n) =
  (qSecond n Q.* Half.half) Q.+ qZero n

qRadiusTerm : Nat → ℚᵘ
qRadiusTerm k =
  Atan.inverseOddRational k Q.*
  qSecond (Estimate.oddExponent k)

qRadiusBudget : Nat → ℚᵘ
qRadiusBudget zero = 0ℚᵘ
qRadiusBudget (suc n) =
  qRadiusBudget n Q.+ qRadiusTerm n

-- The FIRST original native power polynomial exact readback.
qZeroEmbeds :
  (n : Nat) →
  R._≃_
    (R._⋆ (qZero n))
    (Power.powerDifferenceQuotient Half.bishopHalf R.0ℝ n)
qZeroEmbeds zero = P.≃-refl
qZeroEmbeds (suc n) =
  let
    q = qZero n
    p = Stage.qPow Half.half n
    qq = Power.powerDifferenceQuotient Half.bishopHalf R.0ℝ n
  in
  P.≃-trans
    (P.⋆-distrib-+ (q Q.* Half.half) p)
    (P.≃-trans
      (P.+-cong
        (P.≃-trans
          (P.⋆-distrib-* q Half.half)
          (P.*-cong (qZeroEmbeds n) P.≃-refl))
        (Stage.qPowEmbeds Half.half n))
      (P.+-cong
        (P.*-cong P.≃-refl
          (P.≃-symm (P.+-identityʳ Half.bishopHalf)))
        P.≃-refl))

-- The SECOND original native power polynomial exact readback;
-- its right-hand qZero is the theorem above, not an arbitrary factor.
qSecondEmbeds :
  (n : Nat) →
  R._≃_
    (R._⋆ (qSecond n))
    (Second.sourcePowerSecondQuotient Half.bishopHalf R.0ℝ n)
qSecondEmbeds zero = P.≃-refl
qSecondEmbeds (suc n) =
  let a = qSecond n
      c = qZero n
  in
  P.≃-trans
    (P.⋆-distrib-+ (a Q.* Half.half) c)
    (P.≃-trans
      (P.+-cong
        (P.≃-trans
          (P.⋆-distrib-* a Half.half)
          (P.*-cong (qSecondEmbeds n) P.≃-refl))
        (qZeroEmbeds n))
      (P.+-cong
        (P.*-cong P.≃-refl
          (P.≃-symm (P.+-identityʳ Half.bishopHalf)))
        P.≃-refl))

-- Same positive original odd-reciprocal coefficient.
qRadiusTermEmbeds :
  (k : Nat) →
  R._≃_
    (R._⋆ (qRadiusTerm k))
    (Envelope.sourceRadiusTerm k)
qRadiusTermEmbeds k =
  P.≃-trans
    (P.⋆-distrib-*
      (Atan.inverseOddRational k)
      (qSecond (Estimate.oddExponent k)))
    (P.*-cong P.≃-refl
      (qSecondEmbeds (Estimate.oddExponent k)))

-- All-index finite sum readback: a genuine identity on the ORIGINAL
-- Bishop finite source, without requiring the infinite analytic limit.
qRadiusBudgetEmbeds :
  (n : Nat) →
  R._≃_
    (R._⋆ (qRadiusBudget n))
    (Envelope.sourceRadiusBudget n)
qRadiusBudgetEmbeds zero = P.≃-refl
qRadiusBudgetEmbeds (suc n) =
  P.≃-trans
    (P.⋆-distrib-+ (qRadiusBudget n) (qRadiusTerm n))
    (P.+-cong (qRadiusBudgetEmbeds n) (qRadiusTermEmbeds n))

-- The last native inequality can therefore be obtained by the EXISTING
-- R._⋆ rational-order embedding P.p≤q⇒p⋆≤q⋆, after proving the
-- purely rational qRadiusBudget <= 8/9 (no additional analytic input).
