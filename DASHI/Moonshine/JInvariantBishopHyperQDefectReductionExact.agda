module DASHI.Moonshine.JInvariantBishopHyperQDefectReductionExact where

-- SOURCE-WRITTEN, UNCOMPILED. Reduce the actual hypergeometric
-- coefficient endpoint to one signed first-order defect. The formal
-- operator identity remains an explicit source-attachment premise.
-- No binomial candidate, square-root convergence or new branch choice.
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Integer.Base using (+_)
import Data.Integer.Base as Z
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import Real as R
open R using (ℝ; _≃_; _⋆)
import RealProperties as P
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as Ring
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Mathematics.NumberTheory.FiniteDivisorSumExact as Div
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopEulerDefectUniquenessExact as ZU
open U using (Series; _⊕s_; _⊖s_; _⊗s_; scale; D; X; Y; X2; Y2; disc;
  mul0; x20; y20; unitMul; disc0; sub0; right0; D0; mulR0)

E : Series
E zero = R.1ℝ
E (suc n) = R.- (NR.natReal (24 * Div.sigma1 (suc n)))

two thirtySix negThirtySix fifteenHalf : ℝ
two = (+ 2 / 1) ⋆
thirtySix = (+ 36 / 1) ⋆
negThirtySix = (Z.-_ (+ 36) / 1) ⋆
fifteenHalf = (+ 15 / 2) ⋆

r : Series
r = (E ⊗s X) ⊖s Y

Q2 Q1 Q0 : Series
Q2 = scale thirtySix (X2 ⊗s Y2)
Q1 = scale negThirtySix ((X ⊗s Y2) ⊗s r)
Q0 = scale fifteenHalf (Y2 ⊗s ((r ⊗s r) ⊖s disc))

defect : Series → Series
defect f = scale two (X ⊗s D 1 f) ⊖s (D 1 X ⊗s f)

q20 : Q2 zero ≃ thirtySix
q20 = P.≃-trans
  (P.*-congˡ (P.≃-trans (mul0 {f = X2} {g = Y2} x20 y20) unitMul))
  (P.*-identityʳ thirtySix)

q2Positive : R.Positive (Q2 zero)
q2Positive = P.pos-cong (P.≃-symm q20)
  (P.posp⇒posp⋆ (+ 36 / 1) (QP.positive⁻¹ (+ 36 / 1)))

r0 : r zero ≃ R.0ℝ
r0 = P.≃-trans
  (P.+-cong (P.≃-trans (Row.cauchyCoefficientZero E X) unitMul) P.≃-refl)
  (let open P.ℝ-Solver in
    solve 0 (Κ Q.1ℚᵘ ⊖ Κ Q.1ℚᵘ ⊜ Κ Q.0ℚᵘ) P.≃-refl)

q10 : Q1 zero ≃ R.0ℝ
q10 = right0 (mulR0 (X ⊗s Y2) r r0)

q00 : Q0 zero ≃ R.0ℝ
q00 = right0 (mulR0 Y2 ((r ⊗s r) ⊖s disc)
  (sub0 (mulR0 r r r0) disc0))

defect0 : (f : Series) → defect f zero ≃ R.0ℝ
defect0 f = sub0 (right0 (mulR0 X (D 1 f) (D0 f)))
  (P.≃-trans (Row.cauchyCoefficientZero (D 1 X) f)
    (P.≃-trans (P.*-congʳ (D0 X)) (P.*-zeroˡ (f zero))))

Factorization : Series → Set
Factorization f = ∀ n →
  U.residual f n ≃ ZU.operator 2 Q2 Q1 Q0 (defect f) n

defectFromODE : (f : Series) → Factorization f → U.Solution f →
  ∀ n → defect f n ≃ R.0ℝ
defectFromODE f factor solve =
  ZU.allZero 2 Q2 Q1 Q0 (defect f) q2Positive q10 q00
    (λ n → P.≃-trans (P.≃-symm (factor n)) (solve n)) (defect0 f)

-- Algebra on actual rows, with the signed scalar subtraction retained.
rowSubRight : (a b c : Series) (n : Nat) →
  (a ⊗s (b ⊖s c)) n ≃ ((a ⊗s b) ⊖s (a ⊗s c)) n
rowSubRight a b c n =
  let
    x = (a ⊗s (b ⊖s c)) n
    y = (a ⊗s b) n
    z = (a ⊗s c) n
    h : R._≃_ (R._+_ x z) y
    h = P.≃-trans (P.≃-symm (Ring.rowAddRight a (b ⊖s c) c n))
      (Ring.rowCong a ((b ⊖s c) ⊕s c) a b (λ _ → P.≃-refl)
        (λ k → let open P.ℝ-Solver in
          solve 2 (λ b c → (b ⊖ c) ⊕ c ⊜ b) P.≃-refl (b k) (c k)) n)
    open P.ℝ-Solver
  in P.≃-trans
    (solve 2 (λ x z → x ⊜ (x ⊕ z) ⊖ z) P.≃-refl x z)
    (P.+-congˡ (R.- z) h)

rowSubLeft : (a b c : Series) (n : Nat) →
  ((a ⊖s b) ⊗s c) n ≃ ((a ⊗s c) ⊖s (b ⊗s c)) n
rowSubLeft a b c n =
  P.≃-trans (Ring.rowComm (a ⊖s b) c n)
    (P.≃-trans (rowSubRight c a b n)
      (P.+-cong (Ring.rowComm c a n) (P.-‿cong (Ring.rowComm c b n))))

dSub : (a b : Series) (n : Nat) →
  D 1 (a ⊖s b) n ≃ ((D 1 a) ⊖s (D 1 b)) n
dSub a b n = let open P.ℝ-Solver in
  solve 3 (λ d a b → d ⊗ (a ⊖ b) ⊜ d ⊗ a ⊖ d ⊗ b)
    P.≃-refl (R.pow (NR.natReal n) 1) (a n) (b n)

-- Swap the outer two axes of the SAME Cauchy simplex.
swapOuter : (a b c : Series) (n : Nat) →
  (a ⊗s (b ⊗s c)) n ≃ (b ⊗s (a ⊗s c)) n
swapOuter a b c n =
  P.≃-trans (P.≃-symm (Ring.rowAssoc a b c n))
    (P.≃-trans (Ring.rowCong (a ⊗s b) c (b ⊗s a) c
      (Ring.rowComm a b) (λ _ → P.≃-refl) n) (Ring.rowAssoc b a c n))

squareDerivative : (f : Series) (n : Nat) →
  D 1 (f ⊗s f) n ≃ scale two (f ⊗s D 1 f) n
squareDerivative f n =
  P.≃-trans (U.eulerLeibniz f f n)
    (P.≃-trans (P.+-cong (Ring.rowComm (D 1 f) f n) P.≃-refl)
      (let open P.ℝ-Solver in
        solve 1 (λ a → a ⊕ a ⊜ Κ (+ 2 / 1) ⊗ a) P.≃-refl
          ((f ⊗s D 1 f) n)))

squareOperator : Series → Series
squareOperator g = (X ⊗s D 1 g) ⊖s (D 1 X ⊗s g)

squareFromDefectProduct : (f : Series) (n : Nat) →
  squareOperator (f ⊗s f) n ≃ (f ⊗s defect f) n
squareFromDefectProduct f n =
  let
    first : (X ⊗s D 1 (f ⊗s f)) n ≃ (f ⊗s scale two (X ⊗s D 1 f)) n
    first = P.≃-trans
      (Ring.rowCong X (D 1 (f ⊗s f)) X (scale two (f ⊗s D 1 f))
        (λ _ → P.≃-refl) (squareDerivative f) n)
      (P.≃-trans (Ring.rowScaleRight two X (f ⊗s D 1 f) n)
        (P.≃-trans (P.*-congˡ (swapOuter X f (D 1 f) n))
          (P.≃-symm (Ring.rowScaleRight two f (X ⊗s D 1 f) n))))
    second : (D 1 X ⊗s (f ⊗s f)) n ≃ (f ⊗s (D 1 X ⊗s f)) n
    second = swapOuter (D 1 X) f f n
  in P.≃-trans (P.+-cong first (P.-‿cong second))
    (P.≃-symm (rowSubRight f (scale two (X ⊗s D 1 f)) (D 1 X ⊗s f) n))

squareOperatorLinear : (a b : Series) (n : Nat) →
  squareOperator (a ⊖s b) n ≃ ((squareOperator a) ⊖s (squareOperator b)) n
squareOperatorLinear a b n =
  P.≃-trans (P.+-cong
    (P.≃-trans (Ring.rowCong X (D 1 (a ⊖s b)) X ((D 1 a) ⊖s (D 1 b))
      (λ _ → P.≃-refl) (dSub a b) n)
      (rowSubRight X (D 1 a) (D 1 b) n))
    (P.-‿cong (rowSubRight (D 1 X) a b n)))
    (let open P.ℝ-Solver in
      solve 4 (λ a b c d → (a ⊖ b) ⊖ (c ⊖ d) ⊜ (a ⊖ c) ⊖ (b ⊖ d))
        P.≃-refl ((X ⊗s D 1 a) n) ((X ⊗s D 1 b) n)
          ((D 1 X ⊗s a) n) ((D 1 X ⊗s b) n))

squareXZero : (n : Nat) → squareOperator X n ≃ R.0ℝ
squareXZero n = P.≃-trans (P.+-cong (Ring.rowComm X (D 1 X) n) P.≃-refl)
  (let open P.ℝ-Solver in
    solve 1 (λ a → a ⊖ a ⊜ Κ Q.0ℚᵘ) P.≃-refl ((D 1 X ⊗s X) n))

negOne : ℝ
negOne = R.- R.1ℝ

negativeDX : Series
negativeDX = scale negOne (D 1 X)

asTriangular : (g : Series) (n : Nat) →
  ZU.operator 1 X H.zeroSeries negativeDX g n ≃ squareOperator g n
asTriangular g n =
  P.≃-trans (P.+-cong
    (P.≃-trans (P.+-cong P.≃-refl (Ring.rowZeroLeft (D 1 g) n))
      (P.+-identityʳ ((X ⊗s D 1 g) n)))
    (Ring.rowScaleLeft negOne (D 1 X) g n))
    (let open P.ℝ-Solver in
      solve 2 (λ a b → a ⊕ (⊝ Κ Q.1ℚᵘ) ⊗ b ⊜ a ⊖ b)
        P.≃-refl ((X ⊗s D 1 g) n) ((D 1 X ⊗s g) n))

-- The first-order equation for G=F^2-X has cusp diagonal n.
-- Thus the SAME triangular uniqueness proof kills G. No binomial
-- root needs to be constructed or shown to satisfy the third-order ODE.
squareFromDefect : (f : Series) → f zero ≃ R.1ℝ →
  (∀ n → defect f n ≃ R.0ℝ) →
  ∀ n → (f ⊗s f) n ≃ X n
squareFromDefect f hf hs n =
  let
    g = (f ⊗s f) ⊖s X
    g0 : g zero ≃ R.0ℝ
    g0 = P.≃-trans (P.+-cong
      (P.≃-trans (mul0 {f = f} {g = f} hf hf) unitMul) P.≃-refl)
      (let open P.ℝ-Solver in
        solve 0 (Κ Q.1ℚᵘ ⊖ Κ Q.1ℚᵘ ⊜ Κ Q.0ℚᵘ) P.≃-refl)
    sf : (k : Nat) → squareOperator (f ⊗s f) k ≃ R.0ℝ
    sf k = P.≃-trans (squareFromDefectProduct f k)
      (P.≃-trans (Ring.rowCong f (defect f) f H.zeroSeries
        (λ _ → P.≃-refl) hs k) (H.zeroRow f k))
    opZero : (k : Nat) → ZU.operator 1 X H.zeroSeries negativeDX g k ≃ R.0ℝ
    opZero k = P.≃-trans (asTriangular g k)
      (P.≃-trans (squareOperatorLinear (f ⊗s f) X k)
        (sub0 (sf k) (squareXZero k)))
    gz : g n ≃ R.0ℝ
    gz = ZU.allZero 1 X H.zeroSeries negativeDX g
      (P.posp⇒posp⋆ Q.1ℚᵘ (QP.positive⁻¹ Q.1ℚᵘ)) P.≃-refl
      (right0 (D0 X)) opZero g0 n
    a = (f ⊗s f) n
    b = X n
    open P.ℝ-Solver
  in P.≃-trans (solve 2 (λ a b → a ⊜ (a ⊖ b) ⊕ b) P.≃-refl a b)
    (P.≃-trans (P.+-cong gz P.≃-refl) (P.+-identityˡ b))

-- Literal hypergeometric consumer: one Solution and the operator
-- attachment, rather than two Solutions plus a binomial-square proof.
hyperSquareFromFactor : Factorization H.hyperCandidate →
  U.Solution H.hyperCandidate →
  ∀ n → (H.hyperCandidate ⊗s H.hyperCandidate) n ≃ X n
hyperSquareFromFactor factor h =
  squareFromDefect H.hyperCandidate H.hyperConstant
    (defectFromODE H.hyperCandidate factor h)
