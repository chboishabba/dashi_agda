{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayConstructedComplexFiniteAdjointTraceExact where

------------------------------------------------------------------------
-- CONCRETE FINITE COMPLEX MATRIX: REAL TRACE OF ADJOINT IS REAL TRACE.
--
-- Reuse DASHI.Analysis.ConcreteComplex (constructive complex pairs and
-- explicit conjugation) and ConstructiveRealSpine (its genuine ordered
-- real carrier). No imaginary numerical proxy, quaternion second jet,
-- generic matrix axiom or real global postulate is introduced here.
--
-- For all n, a concrete matrix is Fin n -> Fin n -> ComplexPair R.
-- The real diagonal trace is summed by finite recursion. The real part
-- of conjugation is definitionally unchanged. Thus Re Tr(A†)=Re Tr(A),
-- and the same holds after multiplication by any selected normalizer
-- (in particular the physically required factor 1/N).
--
-- The actual matrix theory and trace-data instance must identify their
-- source operators with these concrete operations. This module does
-- NOT construct finite complex-matrix multiplication/determinant laws,
-- a complete complex ordered real, compact Haar or a continuum theory.
--
-- Elementary matrix identity, previously named SUNMatrixCarrier theory;
-- existing DASHI constructive-real/complex authors retain ownership.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import Data.Fin.Base as Fin
import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeInversePlaquetteRealTraceExact as Inverse

ConcreteComplexMatrix :
  (R : Real.ConstructedOrderedCompleteReal) → Nat → Set
ConcreteComplexMatrix R n =
  Fin.Fin n → Fin.Fin n → Complex.ComplexPair R

concreteComplexAdjoint :
  ∀ {R n} →
  ConcreteComplexMatrix R n → ConcreteComplexMatrix R n
concreteComplexAdjoint A row column =
  Complex.conjugateC (A column row)

realConjugateUnchanged :
  ∀ {R} (value : Complex.ComplexPair R) →
  Complex.re (Complex.conjugateC value) ≡ Complex.re value
realConjugateUnchanged (Complex.complex realPart imaginaryPart) = refl

sumDiagonalReal :
  (R : Real.ConstructedOrderedCompleteReal)
  (n : Nat) →
  (Fin.Fin n → Real.Real R) →
  Real.Real R
sumDiagonalReal R zero values = Real.zero R
sumDiagonalReal R (suc n) values =
  Real._+_ R (values Fin.zero)
    (sumDiagonalReal R n (λ k → values (Fin.suc k)))

realComplexMatrixTrace :
  ∀ {R} (n : Nat) →
  ConcreteComplexMatrix R n → Real.Real R
realComplexMatrixTrace {R} n A =
  sumDiagonalReal R n (λ k → Complex.re (A k k))

realComplexMatrixAdjointTrace :
  ∀ {R} (n : Nat) (A : ConcreteComplexMatrix R n) →
  realComplexMatrixTrace n (concreteComplexAdjoint A)
  ≡ realComplexMatrixTrace n A
realComplexMatrixAdjointTrace zero A = refl
realComplexMatrixAdjointTrace {R} (suc n) A =
  cong₂ (Real._+_ R)
    (realConjugateUnchanged (A Fin.zero Fin.zero))
    (realComplexMatrixAdjointTrace n
      (λ row column → A (Fin.suc row) (Fin.suc column)))

-- Scale the real trace by the chosen factor, without assuming its value.
-- For a physical SU(N), that factor must actually be the inverse of N.
concreteNormalizedRealTrace :
  ∀ {R} (n : Nat) →
  Real.Real R →
  ConcreteComplexMatrix R n → Real.Real R
concreteNormalizedRealTrace {R} n normalizer A =
  Real._*_ R normalizer (realComplexMatrixTrace n A)

concreteNormalizedRealTraceAdjoint :
  ∀ {R} (n : Nat) (normalizer : Real.Real R)
    (A : ConcreteComplexMatrix R n) →
  concreteNormalizedRealTrace n normalizer (concreteComplexAdjoint A)
  ≡ concreteNormalizedRealTrace n normalizer A
concreteNormalizedRealTraceAdjoint {R} n normalizer A =
  cong (Real._*_ R normalizer) (realComplexMatrixAdjointTrace n A)

------------------------------------------------------------------------
-- Exact same-object connector into the ORIGINAL certified SU(N) theory.
-- Only the two definitional/operator correspondences are required here;
-- the adjoint real-trace equality itself is proved by the finite recursion.
------------------------------------------------------------------------

record CertifiedSUNConcreteComplexTraceAgreement
    {R : Real.ConstructedOrderedCompleteReal} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N
      (ConcreteComplexMatrix R N) (Complex.ComplexPair R))
    (traceData : Trace.SUNMatrixRealTrace
      {Scalar = Real.Real R} theory)
    (normalizer : Real.Real R) : Set₁ where
  field
    actualAdjointIsConjugateTranspose : ∀ A →
      SUN.daggerM (SUN.operations theory) A
      ≡ concreteComplexAdjoint A

    actualNormalizedRealTraceIsDiagonal : ∀ A →
      Trace.normalizedRealTrace traceData A
      ≡ concreteNormalizedRealTrace N normalizer A

open CertifiedSUNConcreteComplexTraceAgreement public

concreteSUNAdjointRealTrace :
  ∀ {R N}
    (theory : SUN.CertifiedSUNMatrixTheory N
      (ConcreteComplexMatrix R N) (Complex.ComplexPair R))
    (traceData : Trace.SUNMatrixRealTrace
      {Scalar = Real.Real R} theory)
    (normalizer : Real.Real R) →
    CertifiedSUNConcreteComplexTraceAgreement theory traceData normalizer →
    Inverse.SUNMatrixAdjointRealTraceLaw theory traceData
concreteSUNAdjointRealTrace {N = N} theory traceData normalizer agreement =
  record
    { Inverse.SUNMatrixAdjointRealTraceLaw.matrixAdjointRealTrace =
        λ A →
          trans
            (cong (Trace.normalizedRealTrace traceData)
              (actualAdjointIsConjugateTranspose agreement A))
            (trans
              (actualNormalizedRealTraceIsDiagonal agreement
                (concreteComplexAdjoint A))
              (trans
                (concreteNormalizedRealTraceAdjoint N normalizer A)
                (sym (actualNormalizedRealTraceIsDiagonal agreement A))))
    }
