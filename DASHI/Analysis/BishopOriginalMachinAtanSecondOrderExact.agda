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

-- A finite potential pays every power second quotient on [0,1/2].
-- B_n = 2 T_n + 4 Q_n + 8 (1/2)^n.
-- B_n = T_n + B_(n+1), exactly. The odd slice consumes at
-- most the same budget, with no exchange of infinite sums.
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import Data.Rational.Unnormalised as Rat
import Data.Rational.Unnormalised.Properties as RatP

half : ℝ
half = Half.bishopHalf

two four eight : ℝ
two = (+ 2 / 1) ⋆
four = (+ 4 / 1) ⋆
eight = (+ 8 / 1) ⋆

halfNN : R.NonNegative half
halfNN = P.0≤x⇒nonNegx (P.p≤q⇒p⋆≤q⋆ Rat.0ℚᵘ (+ 1 / 2) (RatP.nonNegative⁻¹ (+ 1 / 2)))

halfPlusZeroNN : R.NonNegative (half + R.0ℝ)
halfPlusZeroNN = P.nonNeg-cong (P.≃-symm (P.+-identityʳ half)) halfNN

qHalf tHalf pHalf : Nat → ℝ
qHalf = Q.powerDifferenceQuotient half R.0ℝ
tHalf = T.sourcePowerSecondQuotient half R.0ℝ
pHalf = R.pow half

qNN : ∀ n → R.NonNegative (qHalf n)
qNN = Pos.originalPowerZeroStepQuotientNonnegative half halfNN

tNN : ∀ n → R.NonNegative (tHalf n)
tNN = Pos.originalPowerSecondQuotientNonnegative half R.0ℝ halfNN halfPlusZeroNN

budget : Nat → ℝ
budget n = (two * tHalf n + four * qHalf n) + eight * pHalf n

budgetNN : ∀ n → R.NonNegative (budget n)
budgetNN n = P.nonNegx,y⇒nonNegx+y
  (P.nonNegx,y⇒nonNegx+y
    (P.nonNegx,y⇒nonNegx*y
      (P.0≤x⇒nonNegx (P.p≤q⇒p⋆≤q⋆ Rat.0ℚᵘ (+ 2 / 1) (RatP.nonNegative⁻¹ (+ 2 / 1)))) (tNN n))
    (P.nonNegx,y⇒nonNegx*y
      (P.0≤x⇒nonNegx (P.p≤q⇒p⋆≤q⋆ Rat.0ℚᵘ (+ 4 / 1) (RatP.nonNegative⁻¹ (+ 4 / 1)))) (qNN n)))
  (P.nonNegx,y⇒nonNegx*y
    (P.0≤x⇒nonNegx (P.p≤q⇒p⋆≤q⋆ Rat.0ℚᵘ (+ 8 / 1) (RatP.nonNegative⁻¹ (+ 8 / 1))))
    (Seq.nonNegx⇒nonNegxⁿ halfNN n))

budgetStep : ∀ n → (tHalf n + budget (suc n)) ≃ budget n
budgetStep n =
  let q = qHalf n
      t = tHalf n
      p = pHalf n
      qStep = P.+-cong (P.*-congˡ (P.+-identityʳ half)) P.≃-refl
      tStep = P.+-cong (P.*-congˡ (P.+-identityʳ half)) P.≃-refl
      open P.ℝ-Solver
  in P.≃-trans
    (P.+-cong P.≃-refl
      (P.+-cong (P.+-cong (P.*-congˡ tStep) (P.*-congˡ qStep)) P.≃-refl))
    (solve 3 (λ t q p →
      t ⊕ ((Κ (+ 2 / 1) ⊗ (t ⊗ Κ (+ 1 / 2) ⊕ q) ⊕
      Κ (+ 4 / 1) ⊗ (q ⊗ Κ (+ 1 / 2) ⊕ p)) ⊕
      Κ (+ 8 / 1) ⊗ (p ⊗ Κ (+ 1 / 2))) ⊜
      (Κ (+ 2 / 1) ⊗ t ⊕ Κ (+ 4 / 1) ⊗ q) ⊕ Κ (+ 8 / 1) ⊗ p)
      P.≃-refl t q p)

budgetZero : budget zero ≃ eight
budgetZero = let open P.ℝ-Solver in
  solve 0 ((Κ (+ 2 / 1) ⊗ Κ 0ℚᵘ ⊕ Κ (+ 4 / 1) ⊗ Κ 0ℚᵘ) ⊕
    Κ (+ 8 / 1) ⊗ Κ 1ℚᵘ ⊜ Κ (+ 8 / 1)) P.≃-refl

coefficientBelowOne : ∀ n → coefficient n ≤ R.1ℝ
coefficientBelowOne zero = P.≤-refl
coefficientBelowOne (suc n) = P.≤-trans (A.embeddedInverseOddStep n) (coefficientBelowOne n)

oddTermBelow : ∀ n → majorantTerm half n ≤ tHalf (E.oddExponent n)
oddTermBelow n = P.≤-respʳ-≃ (P.*-identityˡ (tHalf (E.oddExponent n)))
  (P.*-monoʳ-≤-nonNeg (coefficientBelowOne n) (tNN (E.oddExponent n)))

budgetPair : ∀ k → (tHalf k + budget (suc (suc k))) ≤ budget k
budgetPair k = P.≤-respʳ-≃ (budgetStep k)
  (P.+-monoˡ-≤ (tHalf k)
    (P.≤-respʳ-≃ (budgetStep (suc k))
      (P.≤-respʳ-≃ (P.+-comm (budget (suc (suc k))) (tHalf (suc k)))
        (Seq.0≤x⇒y≤y+x (budget (suc (suc k))) (P.nonNegx⇒0≤x (tNN (suc k)))))))

oddBudget : ∀ n → (majorant half n + budget (E.oddExponent n)) ≤ eight
oddBudget zero = P.≤-respˡ-≃ (P.≃-symm (P.+-identityˡ (budget 1)))
  (P.≤-reflexive (P.≃-trans
    (P.≃-symm (P.+-identityˡ (budget 1)))
    (P.≃-trans (budgetStep zero) budgetZero)))
oddBudget (suc n) =
  let k = E.oddExponent n
      s = majorant half n
      t = majorantTerm half n
      b = budget (suc (suc k))
      open P.ℝ-Solver
  in P.≤-respˡ-≃ (P.≃-symm
    (solve 3 (λ s t b → (s ⊕ t) ⊕ b ⊜ s ⊕ (t ⊕ b)) P.≃-refl s t b))
    (P.≤-trans
      (P.+-monoˡ-≤ s
        (P.≤-trans (P.+-mono-≤ (oddTermBelow n) P.≤-refl) (budgetPair k)))
      (oddBudget n))

majorantBelowEight : ∀ n → majorant half n ≤ eight
majorantBelowEight n = P.≤-trans
  (Seq.0≤x⇒y≤y+x (majorant half n) (P.nonNegx⇒0≤x (budgetNN (E.oddExponent n))))
  (oddBudget n)

uniformSecondBound : ∀ x h → R.NonNegative x → R.NonNegative (x + h) →
  x ≤ half → (x + h) ≤ half → ∀ n → ∣ secondPartial x h n ∣ ≤ eight
uniformSecondBound x h xn yn xr yr n =
  P.≤-trans (partialBound x h half xn yn xr yr n) (majorantBelowEight n)
