module DASHI.Analysis.BishopOriginalMachinSharpUniformDefectConsumerExact where

-- ORIGINAL BISHOP ALL-NAT FINITE DERIVATIVE DEFECT.
-- Source-written, not native kernel checked. NO NEW ATAN FUNCTION.
--
-- Input is a SINGLE *purely rational* all-N inequality, for the
-- literal qRadiusBudget recurrence from the exact readback module.
-- It is not a generic analytic uniform-bound assumption, and it is
-- already represented by companion Lean rational proofs:
--   sourceHalfRadiusBudget_le.
--
-- The output is the actual original Bishop finite quotient bound:
--   |S_N(x,h)| <= 8/9,
--   |Q_N(x,h) - A'_N(x)| <= |h|*(8/9),
-- for all N with |x|,|x+h| <= 1/2, including h=0.
-- The source of A'_N is the original geometric derivative polynomial.
-- Remaining: native Agda proof/transport of the rational inequality
-- AND actual Bishop derivative-of-limit interchange/ODE uniqueness.
-- This is an explicit proof dependency, not an axiom or postulate.

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (ℚᵘ; _/_; _≤_)
import Real as R
import RealProperties as P
import DASHI.Analysis.BishopOriginalMachinAtanQuotientSecondOrderExact as Original
import DASHI.Analysis.BishopOriginalMachinSignedSecondRadiusEnvelopeExact as Envelope
import DASHI.Analysis.BishopOriginalMachinSecondRadiusRationalReadbackExact as Readback
import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half

eightNinths : ℚᵘ
eightNinths = + 8 / 9

record OriginalRationalBudgetOrder : Set where
  field
    radiusBudgetBelow :
      (n : Nat) →
      Q._≤_ (Readback.qRadiusBudget n) eightNinths

module FromExactRationalOrder (order : OriginalRationalBudgetOrder) where
  open OriginalRationalBudgetOrder order

  originalBishopRadiusBudgetBelow :
    (n : Nat) →
    R._≤_ (Envelope.sourceRadiusBudget n) (R._⋆ eightNinths)
  originalBishopRadiusBudgetBelow n =
    P.≤-respˡ-≃
      (P.≃-symm (Readback.qRadiusBudgetEmbeds n))
      (P.p≤q⇒p⋆≤q⋆
        (Readback.qRadiusBudget n) eightNinths
        (radiusBudgetBelow n))

  originalSignedSecondBelowEightNinths :
    (x h : R.ℝ) →
    (xInside : R._≤_ (R.∣ x ∣) Half.bishopHalf) →
    (yInside : R._≤_ (R.∣ R._+_ x h ∣) Half.bishopHalf) →
    (n : Nat) →
    R._≤_ (R.∣ Original.finiteSecond x h n ∣)
      (R._⋆ eightNinths)
  originalSignedSecondBelowEightNinths x h xInside yInside n =
    P.≤-trans
      (Envelope.originalSignedFiniteSecondBelowRadius
        x h xInside yInside n)
      (originalBishopRadiusBudgetBelow n)

  originalFiniteDerivativeDefectEqualsStep :
    (x h : R.ℝ) (n : Nat) →
    R._≃_
      (R._-_ (Original.finiteQuotient x h n)
        (Geo.arctanDerivativePolynomial x n))
      (R._*_ h (Original.finiteSecond x h n))
  originalFiniteDerivativeDefectEqualsStep x h n =
    let
      derivative = Geo.arctanDerivativePolynomial x n
      product = R._*_ h (Original.finiteSecond x h n)
      open P.ℝ-Solver
    in
    P.≃-trans
      (P.-‿cong
        (Original.originalAtanFiniteQuotientExactDefect x h n))
      (solve 2
        (λ d p → (d ⊕ p) ⊖ d ⊜ p)
        P.≃-refl derivative product)

  originalFiniteDerivativeUniformModulus :
    (x h : R.ℝ) →
    (xInside : R._≤_ (R.∣ x ∣) Half.bishopHalf) →
    (yInside : R._≤_ (R.∣ R._+_ x h ∣) Half.bishopHalf) →
    (n : Nat) →
    R._≤_
      (R.∣ R._-_ (Original.finiteQuotient x h n)
        (Geo.arctanDerivativePolynomial x n) ∣)
      (R._*_ (R.∣ h ∣) (R._⋆ eightNinths))
  originalFiniteDerivativeUniformModulus x h xInside yInside n =
    P.≤-respˡ-≃
      (P.≃-trans
        (P.∣-∣-cong
          (originalFiniteDerivativeDefectEqualsStep x h n))
        (P.∣x*y∣≃∣x∣*∣y∣
          h (Original.finiteSecond x h n)))
      (P.*-monoˡ-≤-nonNeg
        (originalSignedSecondBelowEightNinths
          x h xInside yInside n)
        (P.nonNeg∣x∣ h))
