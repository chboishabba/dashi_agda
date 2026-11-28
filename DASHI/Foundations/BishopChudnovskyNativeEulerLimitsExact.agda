module DASHI.Foundations.BishopChudnovskyNativeEulerLimitsExact where

-- SOURCE-WRITTEN, UNCOMPILED. Construct the two actual CM factorial
-- Euler limits from the original weighted defect, without assuming
-- the modular identity or any convergence of H or theta H.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _^_)
import Data.Nat.Base as N
import Data.Nat.Properties as NP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
open import Relation.Nullary.Decidable.Core using (from-yes)
open import Data.Product.Base using (proj₂)
import Data.Integer.Base as Z
import Data.Integer.Properties as ZP
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import Real as R
import RealProperties as P
import Sequence as S
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyIndexedEdgeAlgebraExact as E
import DASHI.Foundations.BishopChudnovskyPositiveGapExact as G
import DASHI.Foundations.BishopChudnovskyWidthSourceExact as D
import DASHI.Foundations.BishopChudnovskyPrefixSemanticsExact as Raw
import DASHI.Foundations.BishopChudnovskyAdjacentNestingExact as Order
import DASHI.Foundations.BishopChudnovskyNativeFactorialLimitExact as L
import DASHI.Foundations.BishopChudnovskyFactorialSourceExact as F
import DASHI.Foundations.BishopChudnovskyNativeFactorialEulerAttachmentExact as J
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as Norm
import DASHI.Foundations.BishopChudnovskyNativePeriodProductExact as End
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Emb
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as Poly
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as Maj

-- Any nonnegative multiplier k with A*k <= A+B*n inherits
-- |k*u_n| <= M^(-n). The signed numerator itself is untouched.
multiplierBound : (k n : Nat) → CH.A * k ≤ G.weight n →
  (k * D.wAbs n) * (D.M ^ n) ≤ G.qProduct (suc n)
multiplierBound k n hk = NP.*-cancelˡ-≤ CH.A
  (NP.≤-trans (NP.≤-reflexive left)
    (NP.≤-trans (NP.*-mono-≤ (NP.*-mono-≤ hk NP.≤-refl) NP.≤-refl)
      (NP.≤-trans (NP.≤-reflexive right) (D.scaledDefectBound n))))
  where
  left = solve 4 (λ a k w m →
    a :* ((k :* w) :* m) := ((a :* k) :* w) :* m)
    refl CH.A k (D.wAbs n) (D.M ^ n)
  right = solve 3 (λ v w m →
    (v :* w) :* m := m :* (w :* v))
    refl (G.weight n) (D.wAbs n) (D.M ^ n)

oneWeight : (n : Nat) → CH.A * 1 ≤ G.weight n
oneWeight n = subst (λ a → a ≤ G.weight n)
  (sym (NP.*-identityʳ CH.A)) (NP.m≤m+n CH.A (CH.B * n))

indexWeight : (n : Nat) → CH.A * n ≤ G.weight n
indexWeight n = NP.≤-trans
  (NP.*-mono-≤ (from-yes (CH.A NP.≤? CH.B)) NP.≤-refl)
  (subst (λ a → CH.B * n ≤ a) (NP.+-comm (CH.B * n) CH.A)
    (NP.m≤m+n (CH.B * n) CH.A))

budget : Nat → Q.ℚᵘ
budget n = Raw.frac (Z.+_ 1) (D.M ^ n) (NP.m^n≢0 D.M n)

ratioQ : Q.ℚᵘ
ratioQ = Z.+_ 1 Q./ D.M

ratio : R.ℝ
ratio = R._⋆ ratioQ

-- Same unreduced rational budget as the original source contraction.
-- Explicitly commute the natural power denominator at the step.
budgetStep : (n : Nat) → budget (suc n) Q.≃ (budget n Q.* ratioQ)
budgetStep n =
  QP.≃-trans sameDen
    (Raw.fracMulEdge (Z.+_ 1) (Z.+_ 1) (D.M ^ n) D.M
      (NP.m^n≢0 D.M n) N.nonZero)
  where
  sameDen : budget (suc n) Q.≃
    Raw.frac (Z.+_ 1) ((D.M ^ n) * D.M)
      (Raw.prodNZ (D.M ^ n) D.M (NP.m^n≢0 D.M n) N.nonZero)
  sameDen rewrite NP.*-comm D.M (D.M ^ n) = QP.≃-refl

budgetPow : (n : Nat) → budget n Q.≃ Emb.qPow ratioQ n
budgetPow zero = QP.≃-refl
budgetPow (suc n) = QP.≃-trans (budgetStep n)
  (QP.*-cong (budgetPow n) QP.≃-refl)

budgetReal : (n : Nat) → R._≃_ (R._⋆ (budget n)) (R.pow ratio n)
budgetReal n = P.≃-trans (P.⋆-cong (budgetPow n)) (Emb.qPowEmbeds ratioQ n)

scaledQ : Nat → Nat → Q.ℚᵘ
scaledQ k n = (Z.+_ k Q./ 1) Q.* F.factorialTerm n

rawScaled : Nat → Nat → Q.ℚᵘ
rawScaled k n = Raw.frac (Z._*_ (E.P (suc n)) (Z.+_ k))
  (G.qProduct (suc n)) (G.qProductNonZero (suc n))

rawScaledEq : (k n : Nat) → rawScaled k n Q.≃ scaledQ k n
rawScaledEq k n = QP.≃-trans
  (Raw.fracWeight (E.P (suc n)) (Z.+_ k)
    (G.qProduct (suc n)) (G.qProductNonZero (suc n)))
  (QP.≃-trans (QP.*-comm (Raw.rawProduct (suc n)) (Z.+_ k Q./ 1))
    (QP.*-cong QP.≃-refl (F.productFactorial n)))

rawMagnitude : (k n : Nat) → Q.∣ rawScaled k n ∣ Q.≃
  Raw.frac (Z.+_ (k * D.wAbs n)) (G.qProduct (suc n)) (G.qProductNonZero (suc n))
rawMagnitude k n =
  QP.≃-trans (L.absFrac (Z._*_ (E.P (suc n)) (Z.+_ k))
    (G.qProduct (suc n)) (G.qProductNonZero (suc n)))
    (subst (λ a → Raw.frac (Z.+_ (Z.∣ Z._*_ (E.P (suc n)) (Z.+_ k) ∣))
      (G.qProduct (suc n)) (G.qProductNonZero (suc n)) Q.≃
      Raw.frac (Z.+_ a) (G.qProduct (suc n)) (G.qProductNonZero (suc n)))
      mag QP.≃-refl)
  where
  mag : Z.∣ Z._*_ (E.P (suc n)) (Z.+_ k) ∣ ≡ k * D.wAbs n
  mag rewrite E.prefixPStep n = trans (ZP.abs-* (Z._*_ (E.P n) (CH.sourceP n)) (Z.+_ k))
    (NP.*-comm (D.wAbs n) k)

scaledBoundQ : (k n : Nat) → CH.A * k ≤ G.weight n →
  Q.∣ scaledQ k n ∣ Q.≤ budget n
scaledBoundQ k n hk = QP.≤-respˡ-≃ (QP.∣-∣-cong (rawScaledEq k n))
  (QP.≤-respˡ-≃ (QP.≃-sym (rawMagnitude k n))
    (Order.fracOrder (Z.+_ (k * D.wAbs n)) (Z.+_ 1)
      (G.qProduct (suc n)) (D.M ^ n)
      (G.qProductNonZero (suc n)) (NP.m^n≢0 D.M n)
      (Z.+≤+ (subst (λ q → (k * D.wAbs n) * (D.M ^ n) ≤ q)
        (sym (NP.*-identityˡ (G.qProduct (suc n)))) (multiplierBound k n hk)))))

majorant : Nat → R.ℝ
majorant = Poly.polynomialGeometricTerm ratio zero

scaledBound : (k n : Nat) → CH.A * k ≤ G.weight n →
  R._≤_ (R.∣ R._⋆ (scaledQ k n) ∣) (majorant n)
scaledBound k n hk =
  P.≤-respʳ-≃ (P.≃-trans (budgetReal n) (P.≃-symm (P.*-identityˡ (R.pow ratio n))))
    (P.≤-respˡ-≃ (P.∣p∣⋆≃∣p⋆∣ (scaledQ k n))
      (P.p≤q⇒p⋆≤q⋆ (Q.∣ scaledQ k n ∣) (budget n) (scaledBoundQ k n hk)))

hBound : (n : Nat) → R._≤_ (R.∣ J.hTerm n ∣) (majorant n)
hBound n = P.≤-respˡ-≃
  (P.∣-∣-cong (P.⋆-cong (QP.*-identityˡ (F.factorialTerm n))))
  (scaledBound 1 n (oneWeight n))

jBound : (n : Nat) → R._≤_ (R.∣ J.jTerm n ∣) (majorant n)
jBound n = scaledBound n n (indexWeight n)

majorantAbsolute : S.SeriesOf_ConvergesAbsolutely majorant
majorantAbsolute = Poly.polynomialGeometricSeriesAbsolutelyConvergent ratio zero
  (P.p≤q⇒p⋆≤q⋆ Q.0ℚᵘ ratioQ (QP.nonNegative⁻¹ ratioQ))
  (P.p<q⇒p⋆<q⋆ ratioQ Q.1ℚᵘ (Q.*<* (Z.+<+ (from-yes (2 NP.≤? D.M)))))

hAbsolute : S.SeriesOf_ConvergesAbsolutely J.hTerm
hAbsolute = Maj.absoluteSeriesFromMajorant J.hTerm majorant majorantAbsolute hBound

jAbsolute : S.SeriesOf_ConvergesAbsolutely J.jTerm
jAbsolute = Maj.absoluteSeriesFromMajorant J.jTerm majorant majorantAbsolute jBound

hCauchy : S._isConvergent (S.SeriesOf J.hTerm)
hCauchy = S.absolute⇒isConvergent hAbsolute

jCauchy : S._isConvergent (S.SeriesOf J.jTerm)
jCauchy = S.absolute⇒isConvergent jAbsolute

H J₁ : R.ℝ
H = S.lim hCauchy
J₁ = S.lim jCauchy

hConverges : S._ConvergesTo_ (S.SeriesOf J.hTerm) H
hConverges = proj₂ hCauchy

jConverges : S._ConvergesTo_ (S.SeriesOf J.jTerm) J₁
jConverges = proj₂ jCauchy

actualWeightedLimit : R._≃_ L.seriesReal (R._+_ (R._*_ Norm.A H) (R._*_ Norm.B J₁))
actualWeightedLimit = J.weightedLimit H J₁ hConverges jConverges

-- No convergence arguments remain at this consumer. Only the original
-- analytic identification of the two limits with the actual CM forms.
periodFromActualEulerLimits : (x y e : R.ℝ) → R.Positive x →
  R._≃_ (Norm.sq H) x →
  R._≃_ (Norm.sq y) (R._*_ Norm.t (Norm.cube x)) →
  R._≃_ (R._*_ (R._*_ Norm.six y) J₁) (R._*_ H (R._-_ (R._*_ e x) y)) →
  R._≃_ (R._*_ (R._*_ M.bishopMachinPi Norm.r)
    (R._-_ (R._*_ (R._*_ Norm.B x) e) (R._*_ Norm.D y)))
    (R._*_ (R._*_ Norm.six Norm.B) x) →
  End.NativePeriod
periodFromActualEulerLimits x y e px hf hy he hc =
  J.periodFromEulerCMRealSlice x y e H J₁ px hConverges jConverges hf hy he hc
