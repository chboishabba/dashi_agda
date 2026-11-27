module DASHI.Analysis.BishopOriginalMachinAtanSecondOrderExact where

-- Original signed atan, including h=0.  Reuse the finite derivative
-- and second power quotient; no new analytic carrier or derivative axiom.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)
open import Data.Integer.Base using (+_)
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _*_; _-_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopFactorDerivativeExact as F
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Q
import DASHI.Analysis.BishopOriginalFiniteLogQuotientSecondOrderExact as T
import DASHI.Analysis.BishopOriginalFiniteLogSecondQuotientPositiveExact as Pos
import DASHI.Analysis.BishopOriginalFiniteLogQuotientUniformModulusExact as Mono
import DASHI.Analysis.BishopOriginalMachinAtanFiniteDerivativeExact as D
import DASHI.Foundations.BishopMachinArctanConstructionExact as A
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as E
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Sign

coefficient : Nat → ℝ
coefficient n = (A.inverseOddRational n) ⋆

secondTerm : ℝ → ℝ → Nat → ℝ
secondTerm x h n = Sign.alternatingSign n *
  (coefficient n * T.sourcePowerSecondQuotient x h (E.oddExponent n))

secondPartial : ℝ → ℝ → Nat → ℝ
secondPartial x h zero = R.0ℝ
secondPartial x h (suc n) = secondPartial x h n + secondTerm x h n

originalQuotient : ℝ → ℝ → Nat → ℝ
originalQuotient x h n = F.quotient (D.originalMachinAtanFinitePartialFactorDerivative x n) h

termAtZero : ∀ x n →
  Sign.alternatingSign n * (coefficient n * Q.powerDifferenceQuotient x R.0ℝ (E.oddExponent n))
  ≃ D.sourceAtanDerivativeTerm x n
termAtZero x n = P.*-congˡ (P.≃-trans
  (P.*-congˡ (F.powerDifferenceQuotientAtZeroIsDerivative (E.oddExponent n) x))
  (D.sourceOddReciprocalDerivativeCancel x n))

termDefect : ∀ x h n →
  F.quotient (D.originalMachinAtanTermFactorDerivative x n) h
  ≃ (D.sourceAtanDerivativeTerm x n + h * secondTerm x h n)
termDefect x h n =
  let s = Sign.alternatingSign n
      c = coefficient n
      q = Q.powerDifferenceQuotient x R.0ℝ (E.oddExponent n)
      t = T.sourcePowerSecondQuotient x h (E.oddExponent n)
      open P.ℝ-Solver
  in P.≃-trans (P.*-congˡ (P.*-congˡ (T.originalPowerQuotientSecondOrder x h (E.oddExponent n))))
    (P.≃-trans
      (solve 5 (λ s c q h t → s ⊗ (c ⊗ (q ⊕ h ⊗ t)) ⊜
        (s ⊗ (c ⊗ q)) ⊕ h ⊗ (s ⊗ (c ⊗ t))) P.≃-refl s c q h t)
      (P.+-cong (termAtZero x n) P.≃-refl))

partialDefect : ∀ x h n → originalQuotient x h n ≃
  (D.sourceAtanDerivativeFinitePartial x n + h * secondPartial x h n)
partialDefect x h zero = let open P.ℝ-Solver in
  solve 1 (λ h → Κ 0ℚᵘ ⊜ Κ 0ℚᵘ ⊕ h ⊗ Κ 0ℚᵘ) P.≃-refl h
partialDefect x h (suc n) =
  P.≃-trans (P.+-cong (partialDefect x h n) (termDefect x h n))
    (let open P.ℝ-Solver in
      solve 5 (λ a b h s t → (a ⊕ h ⊗ s) ⊕ (b ⊕ h ⊗ t) ⊜
        (a ⊕ b) ⊕ h ⊗ (s ⊕ t)) P.≃-refl
        (D.sourceAtanDerivativeFinitePartial x n) (D.sourceAtanDerivativeTerm x n)
        h (secondPartial x h n) (secondTerm x h n))

increment : ∀ x h n →
  (D.sourceAtanFinitePartial (x + h) n - D.sourceAtanFinitePartial x n)
  ≃ (h * (D.sourceAtanDerivativeFinitePartial x n + h * secondPartial x h n))
increment x h n = P.≃-trans
  (F.incrementFactorisation (D.originalMachinAtanFinitePartialFactorDerivative x n) h)
  (P.*-congˡ (partialDefect x h n))

-- Signed coefficients cannot be treated as nonnegative.  Compare their
-- absolute values with the actual positive reciprocal-weighted odd slice.
majorantTerm : ℝ → Nat → ℝ
majorantTerm r n = coefficient n * T.sourcePowerSecondQuotient r R.0ℝ (E.oddExponent n)

majorant : ℝ → Nat → ℝ
majorant r zero = R.0ℝ
majorant r (suc n) = majorant r n + majorantTerm r n

termBound : ∀ x h r → R.NonNegative x → R.NonNegative (x + h) →
  x ≤ r → (x + h) ≤ r → ∀ n → ∣ secondTerm x h n ∣ ≤ majorantTerm r n
termBound x h r xn yn xr yr n =
  let k = E.oddExponent n
      c = coefficient n
      t = T.sourcePowerSecondQuotient x h k
      nn = Pos.originalPowerSecondQuotientNonnegative x h xn yn k
      absLaw = P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ (Sign.alternatingSign n) (c * t))
        (P.≃-trans (P.*-cong (A.alternatingSignAbsOne n)
          (P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ c t)
            (P.*-cong (A.embeddedInverseOddAbs n) (P.nonNegx⇒∣x∣≃x nn))))
          (P.*-identityˡ (c * t)))
  in P.≤-respˡ-≃ absLaw (P.*-monoˡ-≤-nonNeg
    (Mono.sourcePowerSecondQuotientMonotone x h r xn yn xr yr k)
    (A.embeddedInverseOddNonnegative n))

partialBound : ∀ x h r → R.NonNegative x → R.NonNegative (x + h) →
  x ≤ r → (x + h) ≤ r → ∀ n → ∣ secondPartial x h n ∣ ≤ majorant r n
partialBound x h r xn yn xr yr zero =
  P.≤-reflexive (P.nonNegx⇒∣x∣≃x P.nonNeg0)
partialBound x h r xn yn xr yr (suc n) =
  P.≤-trans (P.∣x+y∣≤∣x∣+∣y∣ (secondPartial x h n) (secondTerm x h n))
    (P.+-mono-≤ (partialBound x h r xn yn xr yr n) (termBound x h r xn yn xr yr n))
