module DASHI.Physics.YangMills.YMClaySUNConcreteUnitaryTraceBridgeExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym; subst; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 1ℝ; _*ℝ_; _≤ℝ_; absℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceCoreExact as Trace
import DASHI.Physics.YangMills.YMClaySUNConcreteUnitaryTraceRangeExact as Concrete

record CertifiedSUNConcreteUnitaryTraceAgreement
    {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N
      (Concrete.ConcreteMatrix N) Concrete.C.ComplexPair)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (normalizer : ℝ) : Set₁ where
  field
    identityIsConcrete :
      SUN.identityM (SUN.operations theory) ≡ Concrete.concreteIdentityMatrix
    multiplyIsConcrete :
      ∀ A B →
      SUN.multiplyM (SUN.operations theory) A B ≡ Concrete.concreteMultiply A B
    daggerIsConcrete :
      ∀ A →
      SUN.daggerM (SUN.operations theory) A ≡ Concrete.concreteDagger A
    traceIsConcreteDiagonal :
      ∀ A →
      Trace.normalizedRealTrace traceData A
      ≡ normalizer *ℝ Concrete.sumFin (λ i → Concrete.C.re (A i i))
    normalizerBound :
      absℝ normalizer *ℝ Concrete.natToReal N ≤ℝ 1ℝ

open CertifiedSUNConcreteUnitaryTraceAgreement public

concreteUnitaryLeftFromSpecial :
  ∀ {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N
      (Concrete.ConcreteMatrix N) Concrete.C.ComplexPair)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (normalizer : ℝ) →
  CertifiedSUNConcreteUnitaryTraceAgreement theory traceData normalizer →
  ∀ (U : SUN.SUNMatrixElement theory) →
  Concrete.concreteMultiply
    (Concrete.concreteDagger (SUN.matrix U)) (SUN.matrix U)
    ≡ Concrete.concreteIdentityMatrix
concreteUnitaryLeftFromSpecial theory traceData normalizer agreement U =
  let M = SUN.matrix U
      ops = SUN.operations theory
      hConcreteFromSunDagger =
        trans
          (sym (agreement .multiplyIsConcrete (SUN.daggerM ops M) M))
          (trans
            (SUN.IsSpecialUnitary.unitaryLeft (SUN.specialUnitary U))
            (agreement .identityIsConcrete))
  in subst
       (λ X → Concrete.concreteMultiply X M ≡ Concrete.concreteIdentityMatrix)
       (agreement .daggerIsConcrete M)
       hConcreteFromSunDagger

concreteSUNMatrixTraceRange :
  ∀ {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N
      (Concrete.ConcreteMatrix N) Concrete.C.ComplexPair)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (normalizer : ℝ) →
  CertifiedSUNConcreteUnitaryTraceAgreement theory traceData normalizer →
  ∀ (U : SUN.SUNMatrixElement theory) →
  absℝ (Trace.matrixWilsonValue traceData U) ≤ℝ 1ℝ
concreteSUNMatrixTraceRange theory traceData normalizer agreement U =
  subst
    (λ t → absℝ t ≤ℝ 1ℝ)
    (sym (agreement .traceIsConcreteDiagonal (SUN.matrix U)))
    (Concrete.concreteNormalizedRealTraceRange
      (SUN.matrix U)
      (concreteUnitaryLeftFromSpecial theory traceData normalizer agreement U)
      normalizer
      (agreement .normalizerBound))
