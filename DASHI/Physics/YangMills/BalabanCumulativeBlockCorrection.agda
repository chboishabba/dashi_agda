module DASHI.Physics.YangMills.BalabanCumulativeBlockCorrection where

-- Exact cumulative correction associated with the simultaneous block route.
--
-- Rather than postulating shellwise J-terms, define the correction on an
-- interval as the difference between the complete beta prefix and the endpoint
-- determinant increment:
--
--   J_{k:n} := Σ β - (D_{k+n} - D_k).
--
-- From the proved interval decomposition this module shows that J_{k:n} is
-- exactly the sum of the explicit penalty correction and nonlinear interaction
-- terms.  This is the algebraic target consumed by the future block-Cholesky
-- calculation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; suc; _+_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; +-identityˡ
  ; +-identityʳ
  ; +-assoc
  ; subSelf
  ; subAddDistributes
  ; cong
  ; trans
  )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( InverseSquareBudgetArithmetic
  ; sub-zero
  )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum
  ; betaIntervalEquality
  )

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

cancelLeadingAdd :
  (arith : InverseSquareBudgetArithmetic) →
  ∀ leading remainder →
  (leading +ℝ remainder) -ℝ leading
    ≡ remainder
cancelLeadingAdd arith leading remainder =
  let
    p1 = cong
      (λ denominator → (leading +ℝ remainder) -ℝ denominator)
      (sym (+-identityʳ leading))
    p2 = subAddDistributes leading remainder leading 0ℝ
    p3 = cong
      (λ left → left +ℝ (remainder -ℝ 0ℝ))
      (subSelf leading)
    p4 = cong
      (λ right → 0ℝ +ℝ right)
      (sub-zero arith remainder)
    p5 = +-identityˡ remainder
  in
    trans p1 (trans p2 (trans p3 (trans p4 p5)))

cumulativeBlockCorrection :
  (beta endpoint : ℕ → ℝ) →
  ℕ → ℕ → ℝ
cumulativeBlockCorrection beta endpoint k n =
  intervalSum beta k n
    -ℝ (endpoint (n + k) -ℝ endpoint k)

cumulativeBlockCorrectionEquality :
  (arith : InverseSquareBudgetArithmetic) →
  (beta gaussian correction interaction endpoint : ℕ → ℝ) →
  (totalBeta :
    ∀ j →
    beta (suc j)
      ≡ gaussian (suc j) +ℝ interaction (suc j)) →
  (shellDecomposition :
    ∀ j →
    gaussian (suc j)
      ≡ (endpoint (suc j) -ℝ endpoint j)
          +ℝ correction (suc j)) →
  ∀ k n →
  cumulativeBlockCorrection beta endpoint k n
    ≡ intervalSum correction k n
        +ℝ intervalSum interaction k n
cumulativeBlockCorrectionEquality
  arith beta gaussian correction interaction endpoint
  totalBeta shellDecomposition k n =
  let
    endpointTerm = endpoint (n + k) -ℝ endpoint k
    correctionTerm = intervalSum correction k n
    interactionTerm = intervalSum interaction k n
    decomposition = betaIntervalEquality
      beta gaussian correction interaction endpoint
      totalBeta shellDecomposition k n
    p1 = cong (λ total → total -ℝ endpointTerm) decomposition
    p2 = cong
      (λ total → total -ℝ endpointTerm)
      (+-assoc endpointTerm correctionTerm interactionTerm)
    p3 = cancelLeadingAdd
      arith endpointTerm (correctionTerm +ℝ interactionTerm)
  in
    trans p1 (trans p2 p3)
