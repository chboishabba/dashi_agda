module DASHI.Foundations.BishopChudnovskyOverlapBudgetExact where

-- Source-written, uncompiled. All-index arithmetic rate budget.
-- Only the literal CH width and cross inequalities remain inputs.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
open import Data.Nat using (_^_)
import Data.Nat.Properties as NP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using
  (ℚᵘ; _/_; _+_; _-_; _*_; _≤_; _≃_; NonNegative; nonNegative)
import Data.Rational.Unnormalised.Properties as QP
import NonReflectiveQ as QS
import Real as R
import Sequence as S
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as F
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as B
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Analysis.BishopMachinGeometricEnvelopeNatExact as CrossNat
import DASHI.Analysis.BishopMachinCrossEnvelopeBishopOrderExact as Rate
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Stage
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskySourceBoundLimitExact as Limit
import DASHI.Foundations.BishopChudnovskyRationalOverlapExact as Overlap

-- 2^k >= k+1, without logarithms or real estimates.
doubleSuccessor : (k : Nat) → suc (suc k) + k ≡ 2 * suc k
doubleSuccessor k =
  solve 1 (λ x →
    (con 1 :+ (con 1 :+ x)) :+ x :=
    con 2 :* (con 1 :+ x)) refl k

dyadicDenominator : (k : Nat) → suc k ≤ 2 ^ k
dyadicDenominator zero = NP.≤-refl
dyadicDenominator (suc k) =
  NP.≤-trans
    (subst (λ v → suc (suc k) ≤ v)
      (doubleSuccessor k) (NP.m≤m+n (suc (suc k)) k))
    (NP.*-mono-≤ NP.≤-refl (dyadicDenominator k))

-- 25^k >= 4(k+1) for k>=1. The signed margin is the
-- positive polynomial 188+96j for the step from k=j+1.
rateStepGap : (j : Nat) →
  4 * suc (suc (suc j)) + (188 + 96 * j) ≡
  25 * (4 * suc (suc j))
rateStepGap j =
  solve 1
    (λ x →
      (con 4 :* (con 3 :+ x)) :+ (con 188 :+ con 96 :* x)
      := con 25 :* (con 4 :* (con 2 :+ x)))
    refl j

machinDenominator : (j : Nat) →
  4 * suc (suc j) ≤ CrossNat.pow25 (suc j)
machinDenominator zero = NP.m≤m+n 8 17
machinDenominator (suc j) =
  NP.≤-trans
    (subst (λ v → 4 * suc (suc (suc j)) ≤ v)
      (rateStepGap j)
      (NP.m≤m+n (4 * suc (suc (suc j))) (188 + 96 * j)))
    (NP.*-mono-≤ NP.≤-refl (machinDenominator j))

dyadic : Nat → ℚᵘ
dyadic k =
  let instance nz = NP.m^n≢0 2 k
  in + 1 / (2 ^ k)

dyadicBelowReciprocal : (k : Nat) →
  dyadic k Q.≤ B.reciprocalPositiveNat k
dyadicBelowReciprocal k =
  let instance nz = NP.m^n≢0 2 k
  in F.natFractionLe (NP.*-mono-≤ NP.≤-refl (dyadicDenominator k))

positiveIndexMachinBelowReciprocal : (j : Nat) →
  Overlap.machinRadius (suc j) Q.≤ B.reciprocalPositiveNat (suc j)
positiveIndexMachinBelowReciprocal j =
  let instance nz = Rate.pow25NonZero (suc j)
      p = CrossNat.pow25 (suc j)
  in F.natFractionLe
    (subst (λ v → 4 * suc (suc j) ≤ v)
      (sym (NP.*-identityˡ p)) (machinDenominator j))

literalWidth : Nat → ℚᵘ
literalWidth k =
  CH.upper (Overlap.window k) Q.- CH.lower (Overlap.window k)

halfWidthBound : (k : Nat) →
  literalWidth k Q.≤ dyadic k →
  Overlap.halfWidth (Overlap.window k) Q.≤
    (+ 1 / 2) Q.* B.reciprocalPositiveNat k
halfWidthBound k w =
  QP.*-monoˡ-≤-nonNeg (+ 1 / 2)
    (QP.≤-trans w (dyadicBelowReciprocal k))

-- This pays the entire rate budget, including the zero-index case,
-- from the literal width inequality alone. No assumed common value.
budgetFromWidth : (k : Nat) →
  literalWidth k Q.≤ dyadic k →
  Overlap.radius (Overlap.window k) (Overlap.machinRadius k)
    Q.≤ Limit.errorQ k
budgetFromWidth zero w =
  QP.≤-trans
    (QP.+-mono-≤ (halfWidthBound zero w) QP.≤-refl)
    (toWitness {a? = QP._≤?_
      (((+ 1 / 2) Q.* B.reciprocalPositiveNat zero) Q.+
        Overlap.machinRadius zero) (Limit.errorQ zero)} _)
budgetFromWidth (suc j) w =
  let
    r = B.reciprocalPositiveNat (suc j)
    instance rNN : NonNegative r
             rNN = nonNegative (QP.nonNegative⁻¹ r)
    sumAsProduct : ((+ 1 / 2) Q.* r Q.+ r) Q.≃ ((+ 3 / 2) Q.* r)
    sumAsProduct =
      let open QS in
      solve 1 (λ x → (Κ (+ 1 / 2) ⊗ x) ⊕ x ⊜ Κ (+ 3 / 2) ⊗ x)
        QP.≃-refl r
    belowFour : (+ 3 / 2) Q.≤ M.four
    belowFour = toWitness {a? = QP._≤?_ (+ 3 / 2) M.four} _
  in QP.≤-trans
    (QP.+-mono-≤ (halfWidthBound (suc j) w)
      (positiveIndexMachinBelowReciprocal j))
    (QP.≤-respˡ-≃ (QP.≃-sym sumAsProduct)
      (QP.*-monoʳ-≤-nonNeg r belowFour))

-- End-to-end source-specific theorem reduced to exactly two families:
-- (a) actual CH fixed-schedule widths, (b) actual rational crosses.
literalConvergenceFromWidthAndCross :
  (w : ∀ k → literalWidth k Q.≤ dyadic k) →
  (c : ∀ k → Overlap.Cross (Overlap.window k)
    (Stage.qMachinStage k) (Overlap.machinRadius k)) →
  S._ConvergesTo_ (λ k → R._⋆ (CH.midpoint (Overlap.window k)))
    M.bishopMachinPi
literalConvergenceFromWidthAndCross w c =
  Overlap.literalConvergenceFromCross c (λ k → budgetFromWidth k (w k))
