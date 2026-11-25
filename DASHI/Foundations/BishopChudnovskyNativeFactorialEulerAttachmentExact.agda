module DASHI.Foundations.BishopChudnovskyNativeFactorialEulerAttachmentExact where

-- SOURCE-WRITTEN, UNCOMPILED. On the literal CM argument, the two
-- hypergeometric Euler streams are the original signed factorialTerm
-- and n*factorialTerm. Split and rejoin the actual weighted prefix,
-- retaining n=0 (H contributes 1, theta H contributes 0).
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (ℚᵘ; _/_)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import NonReflectiveQ as QS
open import Data.Product.Base using (_,_)
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _⋆)
import RealProperties as P
import Sequence as S
import DASHI.Foundations.BishopChudnovskyPrefixSemanticsExact as Raw
import DASHI.Foundations.BishopChudnovskyFactorialSourceExact as F
import DASHI.Foundations.BishopChudnovskyNativeFactorialLimitExact as Limit
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as Norm
import DASHI.Analysis.BishopMachinSignedFiniteHistoryExact as Series

hTerm jTerm : Nat → ℝ
hTerm n = F.factorialTerm n ⋆
jTerm n = ((+ n / 1) Q.* F.factorialTerm n) ⋆

-- Original source weight is A+B*n. Use the actual Raw.weight, not
-- a different power-series definition or arbitrary scalar sequence.
weightMeaning : (n : Nat) → Raw.weight n Q.≃
  ((+ 13591409 / 1) Q.+ ((+ 545140134 / 1) Q.* (+ n / 1)))
weightMeaning n = QP.≃-refl

weightedTerm : (n : Nat) →
  ((F.factorialTerm n Q.* Raw.weight n) ⋆) ≃
    (Norm.A * hTerm n + Norm.B * jTerm n)
weightedTerm n =
  P.≃-trans (P.⋆-cong (QP.*-cong QP.≃-refl (weightMeaning n)))
    (P.≃-trans (P.⋆-distrib-* (F.factorialTerm n)
      ((+ 13591409 / 1) Q.+ ((+ 545140134 / 1) Q.* (+ n / 1))))
      (P.≃-trans
        (P.*-congˡ (P.≃-trans
          (P.⋆-distrib-+ (+ 13591409 / 1) ((+ 545140134 / 1) Q.* (+ n / 1)))
          (P.+-cong P.≃-refl (P.⋆-distrib-* (+ 545140134 / 1) (+ n / 1)))))
        (P.≃-trans
          (let open P.ℝ-Solver in
            solve 2 (λ h n → h ⊗ (Κ (+ 13591409 / 1) ⊕ Κ (+ 545140134 / 1) ⊗ n)
              ⊜ Κ (+ 13591409 / 1) ⊗ h ⊕ Κ (+ 545140134 / 1) ⊗ (n ⊗ h))
              P.≃-refl (hTerm n) ((+ n / 1) ⋆))
          (P.+-cong P.≃-refl (P.*-congˡ
            (P.≃-symm (P.⋆-distrib-* (+ n / 1) (F.factorialTerm n)))))))

weightedPrefix : (n : Nat) →
  (F.factorialPrefix n ⋆) ≃
    (Norm.A * S.SeriesOf hTerm n + Norm.B * S.SeriesOf jTerm n)
weightedPrefix zero = let open P.ℝ-Solver in
  solve 0 (Κ Q.0ℚᵘ ⊜ Κ (+ 13591409 / 1) ⊗ Κ Q.0ℚᵘ ⊕
    Κ (+ 545140134 / 1) ⊗ Κ Q.0ℚᵘ) P.≃-refl
weightedPrefix (suc n) =
  P.≃-trans (P.⋆-distrib-+ (F.factorialPrefix n)
    (F.factorialTerm n Q.* Raw.weight n))
    (P.≃-trans (P.+-cong (weightedPrefix n) (weightedTerm n))
      (let open P.ℝ-Solver in
        solve 4 (λ h j u v →
          (Κ (+ 13591409 / 1) ⊗ h ⊕ Κ (+ 545140134 / 1) ⊗ j) ⊕
          (Κ (+ 13591409 / 1) ⊗ u ⊕ Κ (+ 545140134 / 1) ⊗ v)
          ⊜ Κ (+ 13591409 / 1) ⊗ (h ⊕ u) ⊕ Κ (+ 545140134 / 1) ⊗ (j ⊕ v))
          P.≃-refl (S.SeriesOf hTerm n) (S.SeriesOf jTerm n) (hTerm n) (jTerm n)))

-- Consume convergence of the original two streams, not the desired
-- weighted period equality. The finite split and limit algebra pay
-- the weighted-series attachment required by the terminal consumer.
weightedLimit : (h j : ℝ) →
  S._ConvergesTo_ (S.SeriesOf hTerm) h →
  S._ConvergesTo_ (S.SeriesOf jTerm) j →
  Limit.seriesReal ≃ (Norm.A * h + Norm.B * j)
weightedLimit h j hh hj =
  S.uniqueness-of-limits
    (S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n → weightedPrefix n) (Limit.seriesReal , Limit.factorialConverges))
    (S.xₙ+yₙ→x₀+y₀
      (Norm.A * h , S.xₙyₙ→x₀y₀ (Norm.A , Series.constantSequenceConverges Norm.A) (h , hh))
      (Norm.B * j , S.xₙyₙ→x₀y₀ (Norm.B , Series.constantSequenceConverges Norm.B) (j , hj)))
