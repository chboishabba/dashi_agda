module DASHI.Analysis.BishopOriginalMachinHalfRadiusTermNormalizationExact where

-- FINITE EXACT ORIGINAL HALF-RADIUS TERM NORMALIZATION.
-- SOURCE-WRITTEN / Agda kernel execution pending.
--
-- Reuses *literal* qZero, qSecond, qRadiusTerm recurrences from
-- BishopOriginalMachinSecondRadiusRationalReadbackExact and the source
-- qPow(1/2,n), rather than introducing an independent atan series.
--
-- Scale both native rational recurrences by powTwo(n)=2^n.
-- Zero scaled numerator z_n=2*n.
-- Second scaled numerator s_0=0, s_(n+1)=s_n+4*n,
-- giving s_(n+1)=2*n*(n+1).
-- For m=2k+1 this cancels the actual (2k+1) odd coefficient:
-- qRadiusTerm(k) = 2*k/4^k.
-- This closes the ONLY field of OriginalHalfRadiusTermNormalization.
--
-- All polynomial equalities are integer/Nat-semiring solver proofs;
-- rational equalities use original unnormalised Q.*≡* cross-products.
-- Do not promote source to kernel acceptance before typechecking.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Integer.Solver renaming (module +-*-Solver to ℤSolver)
open ℤSolver using () renaming
  ( solve to Zsolve
  ; _:+_ to _⊕_
  ; _:*_ to _⊗_
  ; con to ZK
  ; _:=_ to _⊜_
  )
import Data.Nat.Properties as NP
open import Data.Nat.Base using (NonZero)
open import Data.Integer.Base using (+_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
open import Data.Rational.Unnormalised as Q using
  (ℚᵘ; 0ℚᵘ; 1ℚᵘ; _/_; _+_; _*_; _≃_; *≡*)
import Data.Rational.Unnormalised.Properties as QP

import DASHI.Analysis.BishopOriginalMachinSecondRadiusRationalReadbackExact as Original
import DASHI.Analysis.BishopOriginalMachinPositiveSlackBudgetExact as Slack
import DASHI.Analysis.BishopOriginalMachinRationalSlackToUniformDefectExact as Consumer
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Stage
import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimate

powerTwo : Nat → Nat
powerTwo zero = 1
powerTwo (suc n) = 2 * powerTwo n

powerTwoNonZero : (n : Nat) → NonZero (powerTwo n)
powerTwoNonZero zero = NP.m^n≢0 2 0
powerTwoNonZero (suc n) =
  NP.m*n≢0 2 (powerTwo n)
    {{_}} {{powerTwoNonZero n}}

qZeroScaled : Nat → Nat
qZeroScaled n = 2 * n

qSecondScaled : Nat → Nat
qSecondScaled zero = 0
qSecondScaled (suc n) = qSecondScaled n + 4 * n

qSecondScaledClosed : (n : Nat) →
  qSecondScaled (suc n) ≡ (2 * n) * (suc n)
qSecondScaledClosed zero = refl
qSecondScaledClosed (suc n) =
  trans
    (cong (λ z → z + 4 * suc n)
      (qSecondScaledClosed n))
    (solve 1 (λ k →
      ((con 2 :* k) :* (k :+ con 1))
        :+ (con 4 :* (k :+ con 1))
      := (con 2 :* (k :+ con 1)) :* (k :+ con 2))
      refl n)

qZeroNormal : Nat → ℚᵘ
qZeroNormal n =
  let instance
        pNZ = powerTwoNonZero n
  in (+ qZeroScaled n / powerTwo n)

qSecondNormal : Nat → ℚᵘ
qSecondNormal n =
  let instance
        pNZ = powerTwoNonZero n
  in (+ qSecondScaled n / powerTwo n)

-- Rational powers of the source 1/2 are exactly 1/powerTwo(n).
qPowHalfNormal :
  (n : Nat) →
  Q._≃_
    (Stage.qPow Half.half n)
    (+ 1 / powerTwo n)
qPowHalfNormal zero = Q.*≡* refl
qPowHalfNormal (suc n) =
  let instance
        pNZ = powerTwoNonZero n
        pnNZ = powerTwoNonZero (suc n)
  in QP.≃-trans
    (QP.*-cong (qPowHalfNormal n) QP.≃-refl)
    (Q.*≡*
      (cong +_ (solve 1
        (λ p → p :* con 2 := con 2 :* p)
        refl (powerTwo n))))

-- The original recurrence qZero(n) has numerator 2n after
-- multiplying by exactly 2^n. This is a same-source readback.
qZeroNormalizes : (n : Nat) →
  Q._≃_ (Original.qZero n) (qZeroNormal n)
qZeroNormalizes zero = Q.*≡* refl
qZeroNormalizes (suc n) =
  let instance
        pNZ = powerTwoNonZero n
        pnNZ = powerTwoNonZero (suc n)
  in QP.≃-trans
    (QP.+-cong
      (QP.*-cong (qZeroNormalizes n) QP.≃-refl)
      (qPowHalfNormal n))
    (Q.*≡* (Zsolve 2
      (λ k p →
        (((ZK (+ 2) ⊗ k) ⊗ p)
          ⊕ (p ⊗ (ZK (+ 2))))
          ⊗ (ZK (+ 2) ⊗ p)
        ⊜
        (ZK (+ 2) ⊗ (k ⊕ ZK (+ 1)))
          ⊗ ((p ⊗ ZK (+ 2)) ⊗ p))
      refl (+ n) (+ powerTwo n)))

-- The second source recurrence is also normalized without forming
-- any difference quotient or using a non-constructive reciprocal.
qSecondNormalizes : (n : Nat) →
  Q._≃_ (Original.qSecond n) (qSecondNormal n)
qSecondNormalizes zero = Q.*≡* refl
qSecondNormalizes (suc n) =
  let instance
        pNZ = powerTwoNonZero n
        pnNZ = powerTwoNonZero (suc n)
  in QP.≃-trans
    (QP.+-cong
      (QP.*-cong (qSecondNormalizes n) QP.≃-refl)
      (qZeroNormalizes n))
    (Q.*≡* (Zsolve 3
      (λ s k p →
        ((s ⊗ p) ⊕ ((ZK (+ 2) ⊗ k)
          ⊗ (p ⊗ ZK (+ 2))))
          ⊗ (ZK (+ 2) ⊗ p)
        ⊜
        (s ⊕ (ZK (+ 4) ⊗ k))
          ⊗ ((p ⊗ ZK (+ 2)) ⊗ p))
      refl (+ qSecondScaled n) (+ n) (+ powerTwo n)))

-- Two powers of the original half radius equal one quarter power:
-- 2^(2k+1) = 2*4^k. This carries the actual odd exponent index.
oddPowerTwoIsTwiceFour :
  (k : Nat) →
  powerTwo (Estimate.oddExponent k) ≡
    2 * Slack.powerFour k
oddPowerTwoIsTwiceFour zero = refl
oddPowerTwoIsTwiceFour (suc k) =
  trans
    (cong (λ p → 2 * (2 * p))
      (oddPowerTwoIsTwiceFour k))
    (solve 1 (λ p →
      con 2 :* (con 2 :* (con 2 :* p))
        := con 2 :* (con 4 :* p))
      refl (Slack.powerFour k))

-- Exact odd-index coefficient n=2k+1; its double is the original
-- qSecondScaled(odd) polynomial; no (2k+2) off-by-one.
secondScaledOdd :
  (k : Nat) →
  qSecondScaled (Estimate.oddExponent k) ≡
    (2 * (2 * k)) * (2 * k + 1)
secondScaledOdd k =
  -- oddExponent k is definitionally suc(evenExponent k).
  -- The equality of evenExponent k and 2*k is elementary Nat induction.
  trans
    (qSecondScaledClosed (Estimate.evenExponent k))
    (solve 1 (λ k →
      (con 2 :* (con 2 :* k))
        :* ((con 2 :* k) :+ con 1)
      := (con 2 :* (con 2 :* k))
        :* ((con 2 :* k) :+ con 1))
      refl k)

-- The original denominator 2k+1 is retained until cross products
-- cancel. Both 4^k and 2^(2k+1) have source Nat nonzero witnesses.
originalTermNormalizes :
  (k : Nat) →
  Q._≃_
    (Original.qRadiusTerm k)
    (+ (2 * k) / Slack.powerFour k)
originalTermNormalizes k =
  let instance
        pnNZ = powerTwoNonZero (Estimate.oddExponent k)
        fourNZ = Slack.powerFourNonZero k
  in QP.≃-trans
    (QP.*-cong QP.≃-refl
      (qSecondNormalizes (Estimate.oddExponent k)))
    (Q.*≡* (Zsolve 2
      (λ k p →
        ((ZK (+ 2) ⊗ (ZK (+ 2) ⊗ k))
          ⊗ ((ZK (+ 2) ⊗ k) ⊕ ZK (+ 1)))
          ⊗ p
        ⊜
        (ZK (+ 2) ⊗ k)
          ⊗ (((ZK (+ 2) ⊗ k) ⊕ ZK (+ 1))
            ⊗ (ZK (+ 2) ⊗ p)))
      refl (+ k) (+ Slack.powerFour k)))

-- The requested earlier one-field input is now source-written,
-- not adopted as an opaque analytic axiom.
originalTermShape :
  Consumer.OriginalHalfRadiusTermNormalization
originalTermShape = record { normalize = originalTermNormalizes }

module CompletedFinite = Consumer.FromTermNormalization originalTermShape
-- CompletedFinite.Native.originalFiniteDerivativeUniformModulus is the
-- existing ORIGINAL Bishop finite derivative-modulus theorem,
-- conditional only on the typechecking of this exact arithmetic source.
