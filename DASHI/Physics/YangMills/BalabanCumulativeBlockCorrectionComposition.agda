module DASHI.Physics.YangMills.BalabanCumulativeBlockCorrectionComposition where

-- Additivity of the exact cumulative block correction under an interval split.
--
-- Once J_{k:n} is defined as total beta minus the endpoint determinant
-- increment, the shell decomposition proves that it is the correction prefix
-- plus the interaction prefix.  Their finite-sum concatenation then gives
--
--   J_{k:m+n} = J_{k:n} + J_{k+n:m}.
--
-- This is the cocycle law required for continuation and scale-by-scale control.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; suc; _+_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; cong
  ; trans
  )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( InverseSquareBudgetArithmetic )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum
  ; rearrangeAdd4
  )
open import DASHI.Physics.YangMills.BalabanIntervalCompositionAlgebra using
  ( intervalSumAppend )
open import DASHI.Physics.YangMills.BalabanCumulativeBlockCorrection using
  ( cumulativeBlockCorrection
  ; cumulativeBlockCorrectionEquality
  )

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

cumulativeBlockCorrectionAppend :
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
  ∀ k n m →
  cumulativeBlockCorrection beta endpoint k (m + n)
    ≡ cumulativeBlockCorrection beta endpoint k n
        +ℝ cumulativeBlockCorrection beta endpoint (n + k) m
cumulativeBlockCorrectionAppend
  arith beta gaussian correction interaction endpoint
  totalBeta shellDecomposition k n m =
  let
    correctionFirst = intervalSum correction k n
    correctionSecond = intervalSum correction (n + k) m
    interactionFirst = intervalSum interaction k n
    interactionSecond = intervalSum interaction (n + k) m

    totalEquality = cumulativeBlockCorrectionEquality
      arith beta gaussian correction interaction endpoint
      totalBeta shellDecomposition k (m + n)
    correctionSplit = intervalSumAppend correction k n m
    interactionSplit = intervalSumAppend interaction k n m
    firstEquality = cumulativeBlockCorrectionEquality
      arith beta gaussian correction interaction endpoint
      totalBeta shellDecomposition k n
    secondEquality = cumulativeBlockCorrectionEquality
      arith beta gaussian correction interaction endpoint
      totalBeta shellDecomposition (n + k) m

    p1 = totalEquality
    p2 = cong
      (λ x → x +ℝ intervalSum interaction k (m + n))
      correctionSplit
    p3 = cong
      (λ x → (correctionFirst +ℝ correctionSecond) +ℝ x)
      interactionSplit
    p4 = rearrangeAdd4
      correctionFirst correctionSecond interactionFirst interactionSecond
    p5 = cong
      (λ x → x +ℝ (correctionSecond +ℝ interactionSecond))
      (sym firstEquality)
    p6 = cong
      (λ x → cumulativeBlockCorrection beta endpoint k n +ℝ x)
      (sym secondEquality)
  in
    trans p1 (trans p2 (trans p3 (trans p4 (trans p5 p6))))
