{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayBishopSetoidFiniteAdjointTraceExact where

------------------------------------------------------------------------
-- ACTUAL VENDORED BISHOP REAL + COMPLEX FINITE MATRIX ADJOINT TRACE.
--
-- Prior owners: BishopConstructedRealBackendExact (Murray/Bishop vendor),
-- BishopSetoidComplexExact (DASHI) and existing complex conjugation.
--
-- This is *not* an axiomatic ℝ proof. It uses the native Bishop real
-- equivalence _≃_ and actual BishopP.+-cong / *-cong.
-- Re Tr(A†) ≃ Re Tr(A) and its normalized version are proved for every n.
--
-- An identification of Bishop setoid equivalence with Agda propositional
-- equality, or with legacy RealAnalysisAxioms.ℝ, is NOT asserted.
-- Nor is a special-unitary determinant/compact Haar construction claimed.
--
-- Sources: Bishop & Bridges (1985); Zachary Murray (2022);
-- vendored Bishop maintainer Viktor Csimma; DASHI setoid complex owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Fin.Base as Fin
import Real as BishopReal
import RealProperties as BishopP
import DASHI.Analysis.BishopSetoidComplexExact as Complex

BishopFiniteComplexMatrix : Nat → Set
BishopFiniteComplexMatrix n =
  Fin.Fin n → Fin.Fin n → Complex.BishopComplex

bishopComplexMatrixAdjoint :
  ∀ {n} →
  BishopFiniteComplexMatrix n → BishopFiniteComplexMatrix n
bishopComplexMatrixAdjoint A row column =
  Complex.conjugate (A column row)

bishopSumDiagonalReal :
  (n : Nat) →
  (Fin.Fin n → BishopReal.ℝ) → BishopReal.ℝ
bishopSumDiagonalReal zero values = BishopReal.0ℝ
bishopSumDiagonalReal (suc n) values =
  BishopReal._+_ (values Fin.zero)
    (bishopSumDiagonalReal n (λ k → values (Fin.suc k)))

bishopRealMatrixTrace :
  (n : Nat) → BishopFiniteComplexMatrix n → BishopReal.ℝ
bishopRealMatrixTrace n A =
  bishopSumDiagonalReal n (λ k → Complex.re (A k k))

bishopRealMatrixAdjointTrace :
  ∀ (n : Nat) (A : BishopFiniteComplexMatrix n) →
  BishopReal._≃_
    (bishopRealMatrixTrace n (bishopComplexMatrixAdjoint A))
    (bishopRealMatrixTrace n A)
bishopRealMatrixAdjointTrace zero A = BishopP.≃-refl
bishopRealMatrixAdjointTrace (suc n) A =
  BishopP.+-cong
    BishopP.≃-refl
    (bishopRealMatrixAdjointTrace n
      (λ row column → A (Fin.suc row) (Fin.suc column)))

bishopNormalizedRealTrace :
  (n : Nat) →
  BishopReal.ℝ →
  BishopFiniteComplexMatrix n → BishopReal.ℝ
bishopNormalizedRealTrace n normalizer A =
  BishopReal._*_ normalizer (bishopRealMatrixTrace n A)

bishopNormalizedRealTraceAdjoint :
  ∀ (n : Nat) (normalizer : BishopReal.ℝ)
    (A : BishopFiniteComplexMatrix n) →
  BishopReal._≃_
    (bishopNormalizedRealTrace n normalizer
      (bishopComplexMatrixAdjoint A))
    (bishopNormalizedRealTrace n normalizer A)
bishopNormalizedRealTraceAdjoint n normalizer A =
  BishopP.*-cong BishopP.≃-refl
    (bishopRealMatrixAdjointTrace n A)
