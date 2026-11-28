module DASHI.Analysis.BishopOriginalMachinAtanQuotientSecondOrderExact where

-- SOURCE-WRITTEN / NOT YET KERNEL CHECKED.
-- All N, all x,h: exact division-FREE quotient of the ORIGINAL Bishop
-- Machin atan partial A_N(x)=sum_{k<N}(-1)^k*x^(2k+1)/(2k+1).
--
-- A_N(x+h)-A_N(x) = h*Q_N(x,h)
-- Q_N(x,h) = A'_N(x)+h*S_N(x,h)
--
-- Q_N and S_N are literal source finite polynomials, with all signs
-- and original reciprocal odd weights retained. No new inverse h or
-- selected classical atan derivative. The pending analytic step is a
-- compact half-ball bound on S_N uniform in N,x,h.
--
-- Reuses the original log second quotient (same power spine) rather
-- than writing another polynomial derivative or uniform convergence
-- authority. This is the source bridge for both 1/5 and 1/239.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopSetoidPowerDerivativeNormalisationExact as Derivative
import DASHI.Analysis.BishopOriginalFiniteLogQuotientSecondOrderExact as Second
import DASHI.Analysis.BishopOriginalMachinAtanFiniteDerivativeExact as Original
import DASHI.Analysis.BishopOriginalMachinAtanDerivativeGeometricWeldExact as Weld
import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geo
import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Sign
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimate

-- This literal coefficient is the signed source reciprocal odd factor.
coefficient : Nat → R.ℝ
coefficient k = R._*_ (Sign.alternatingSign k)
  (R._⋆ (Atan.inverseOddRational k))

termQuotient : R.ℝ → R.ℝ → Nat → R.ℝ
termQuotient x h k = R._*_ (coefficient k)
  (Power.powerDifferenceQuotient x h (Estimate.oddExponent k))

finiteQuotient : R.ℝ → R.ℝ → Nat → R.ℝ
finiteQuotient x h zero = R.0ℝ
finiteQuotient x h (suc n) =
  R._+_ (finiteQuotient x h n) (termQuotient x h n)

-- Polynomial quotient without inverting h, even for h=0.
termDifference :
  (x h : R.ℝ) (k : Nat) →
  R._≃_
    (R._-_ (Atan.atanSignedTerm (R._+_ x h) k)
      (Atan.atanSignedTerm x k))
    (R._*_ h (termQuotient x h k))
termDifference x h k =
  let
    a = Sign.alternatingSign k
    c = R._⋆ (Atan.inverseOddRational k)
    y = R.pow (R._+_ x h) (Estimate.oddExponent k)
    z = R.pow x (Estimate.oddExponent k)
    q = Power.powerDifferenceQuotient x h (Estimate.oddExponent k)
    open P.ℝ-Solver
  in
  P.≃-trans
    (solve 4 (λ a c y z →
      (a ⊗ (c ⊗ y)) ⊖ (a ⊗ (c ⊗ z))
      ⊜ (a ⊗ c) ⊗ (y ⊖ z))
      P.≃-refl a c y z)
    (P.≃-trans
      (P.*-congˡ (Power.powerDifferenceFactorisation x h
        (Estimate.oddExponent k)))
      (solve 4 (λ a c h q →
        (a ⊗ c) ⊗ (h ⊗ q)
        ⊜ h ⊗ ((a ⊗ c) ⊗ q))
        P.≃-refl a c h q))

finiteDifference :
  (x h : R.ℝ) (n : Nat) →
  R._≃_
    (R._-_ (Original.sourceAtanFinitePartial (R._+_ x h) n)
      (Original.sourceAtanFinitePartial x n))
    (R._*_ h (finiteQuotient x h n))
finiteDifference x h zero =
  let open P.ℝ-Solver in
  solve 1 (λ h → Κ 0ℚᵘ ⊖ Κ 0ℚᵘ ⊜ h ⊗ Κ 0ℚᵘ)
    P.≃-refl h
finiteDifference x h (suc n) =
  let
    a = Original.sourceAtanFinitePartial (R._+_ x h) n
    b = Original.sourceAtanFinitePartial x n
    y = Atan.atanSignedTerm (R._+_ x h) n
    z = Atan.atanSignedTerm x n
    q = finiteQuotient x h n
    t = termQuotient x h n
    open P.ℝ-Solver
  in P.≃-trans
    (solve 4 (λ a b y z →
      (a ⊕ y) ⊖ (b ⊕ z)
      ⊜ (a ⊖ b) ⊕ (y ⊖ z))
      P.≃-refl a b y z)
    (P.≃-trans
      (P.+-cong (finiteDifference x h n) (termDifference x h n))
      (solve 3 (λ h q t →
        (h ⊗ q) ⊕ (h ⊗ t) ⊜ h ⊗ (q ⊕ t))
        P.≃-refl h q t))

-- Same *original* power second quotient already paid by K04d LOG.
termSecond : R.ℝ → R.ℝ → Nat → R.ℝ
termSecond x h k = R._*_ (coefficient k)
  (Second.sourcePowerSecondQuotient x h (Estimate.oddExponent k))

finiteSecond : R.ℝ → R.ℝ → Nat → R.ℝ
finiteSecond x h zero = R.0ℝ
finiteSecond x h (suc n) =
  R._+_ (finiteSecond x h n) (termSecond x h n)

termSecondOrder :
  (x h : R.ℝ) (k : Nat) →
  R._≃_ (termQuotient x h k)
    (R._+_ (termQuotient x R.0ℝ k)
      (R._*_ h (termSecond x h k)))
termSecondOrder x h k =
  let
    c = coefficient k
    q = Power.powerDifferenceQuotient x R.0ℝ (Estimate.oddExponent k)
    s = Second.sourcePowerSecondQuotient x h (Estimate.oddExponent k)
    open P.ℝ-Solver
  in P.≃-trans
    (P.*-congˡ
      (Second.originalPowerQuotientSecondOrder x h
        (Estimate.oddExponent k)))
    (solve 4 (λ c q h s →
      c ⊗ (q ⊕ (h ⊗ s))
      ⊜ (c ⊗ q) ⊕ (h ⊗ (c ⊗ s)))
      P.≃-refl c q h s)

finiteSecondOrder :
  (x h : R.ℝ) (n : Nat) →
  R._≃_ (finiteQuotient x h n)
    (R._+_ (finiteQuotient x R.0ℝ n)
      (R._*_ h (finiteSecond x h n)))
finiteSecondOrder x h zero =
  let open P.ℝ-Solver in
  solve 1 (λ h → Κ 0ℚᵘ ⊜ Κ 0ℚᵘ ⊕ h ⊗ Κ 0ℚᵘ)
    P.≃-refl h
finiteSecondOrder x h (suc n) =
  let
    q = finiteQuotient x R.0ℝ n
    s = finiteSecond x h n
    u = termQuotient x R.0ℝ n
    t = termSecond x h n
    open P.ℝ-Solver
  in P.≃-trans
    (P.+-cong (finiteSecondOrder x h n) (termSecondOrder x h n))
    (solve 5 (λ q s h u t →
      (q ⊕ (h ⊗ s)) ⊕ (u ⊕ (h ⊗ t))
      ⊜ (q ⊕ u) ⊕ (h ⊗ (s ⊕ t)))
      P.≃-refl q s h u t)

-- No arbitrary derivative: at h=0 the exact finite quotient reduces
-- to the original signed atan derivative sequence owned by Original.
termAtZero :
  (x : R.ℝ) (k : Nat) →
  R._≃_ (termQuotient x R.0ℝ k)
    (Original.sourceAtanDerivativeTerm x k)
termAtZero x k rewrite Original.oddExponentIsSuccessorEven k =
  let
    sign = Sign.alternatingSign k
    coeff = R._⋆ (Atan.inverseOddRational k)
    derivative = Derivative.powerDerivative
      (suc (Estimate.evenExponent k)) x
    open P.ℝ-Solver
  in P.≃-trans
    (P.*-congˡ
      (P.≃-symm (Power.powerDerivativeIsDifferenceQuotientAtZero
        x (Estimate.evenExponent k))))
    (P.≃-trans
      (solve 3 (λ a b d → (a ⊗ b) ⊗ d ⊜ a ⊗ (b ⊗ d))
        P.≃-refl sign coeff derivative)
      (P.*-congˡ (Original.sourceOddReciprocalDerivativeCancel x k)))

finiteAtZero :
  (x : R.ℝ) (n : Nat) →
  R._≃_ (finiteQuotient x R.0ℝ n)
    (Original.sourceAtanDerivativeFinitePartial x n)
finiteAtZero x zero = P.≃-refl
finiteAtZero x (suc n) =
  P.+-cong (finiteAtZero x n) (termAtZero x n)

-- Crucial original source weld: all N, uniform in x,h BEFORE taking a
-- limit. The only still-unpaid analytic bound is |finiteSecond| ≤ C
-- on the ORIGINAL half-ball; no second derivative or mean-value theorem.
originalAtanFiniteQuotientExactDefect :
  (x h : R.ℝ) (n : Nat) →
  R._≃_ (finiteQuotient x h n)
    (R._+_ (Geo.arctanDerivativePolynomial x n)
      (R._*_ h (finiteSecond x h n)))
originalAtanFiniteQuotientExactDefect x h n =
  P.≃-trans (finiteSecondOrder x h n)
    (P.+-cong
      (P.≃-trans (finiteAtZero x n)
        (Weld.originalAtanFiniteDerivedSumIsGeometricPartial x n))
      P.≃-refl)
