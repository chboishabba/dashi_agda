module DASHI.Algebra.Quantum.QutritPermutationUnitary where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import DASHI.Algebra.Quantum.TernaryCircuit
open import DASHI.Algebra.Quantum.QutritAmplitude

------------------------------------------------------------------------
-- Coordinate permutations are unitary over every complex-star scalar whose
-- addition is associative and commutative.  No analytic transcendental facts
-- are needed for this finite theorem.

record ScalarAdditiveCommutativeLaws
  (A : ComplexStarSemiring) : Set₁ where
  field
    addAssoc : ∀ a b c →
      _+S_ A (_+S_ A a b) c ≡ _+S_ A a (_+S_ A b c)
    addComm : ∀ a b → _+S_ A a b ≡ _+S_ A b a

open ScalarAdditiveCommutativeLaws public

rotateSumLeft :
  ∀ {A : ComplexStarSemiring} →
  ScalarAdditiveCommutativeLaws A →
  ∀ a b c →
  _+S_ A (_+S_ A c a) b ≡ _+S_ A (_+S_ A a b) c
rotateSumLeft {A} laws a b c =
  trans
    (addAssoc laws c a b)
    (addComm laws c (_+S_ A a b))

rotateSumRight :
  ∀ {A : ComplexStarSemiring} →
  ScalarAdditiveCommutativeLaws A →
  ∀ a b c →
  _+S_ A (_+S_ A b c) a ≡ _+S_ A (_+S_ A a b) c
rotateSumRight {A} laws a b c =
  trans
    (addComm laws (_+S_ A b c) a)
    (sym (addAssoc laws a b c))

cyclePreservesInner :
  ∀ {A : ComplexStarSemiring} →
  ScalarAdditiveCommutativeLaws A →
  ∀ x y →
  innerQutrit
    (applyAmplitudeGate cycleGate x)
    (applyAmplitudeGate cycleGate y)
  ≡ innerQutrit x y
cyclePreservesInner {A} laws
  (qstate a b c)
  (qstate x y z) =
  rotateSumLeft laws
    (_*S_ A (conjugate A a) x)
    (_*S_ A (conjugate A b) y)
    (_*S_ A (conjugate A c) z)

inverseCyclePreservesInner :
  ∀ {A : ComplexStarSemiring} →
  ScalarAdditiveCommutativeLaws A →
  ∀ x y →
  innerQutrit
    (applyAmplitudeGate inverseCycleGate x)
    (applyAmplitudeGate inverseCycleGate y)
  ≡ innerQutrit x y
inverseCyclePreservesInner {A} laws
  (qstate a b c)
  (qstate x y z) =
  rotateSumRight laws
    (_*S_ A (conjugate A a) x)
    (_*S_ A (conjugate A b) y)
    (_*S_ A (conjugate A c) z)

qutritPermutationInnerProductAuthority :
  ∀ {A : ComplexStarSemiring} →
  ScalarAdditiveCommutativeLaws A →
  PermutationGateInnerProductAuthority A
qutritPermutationInnerProductAuthority laws =
  record
    { permutationPreservesInner = preserves
    }
  where
    preserves : ∀ gate x y →
      innerQutrit (applyAmplitudeGate gate x) (applyAmplitudeGate gate y)
      ≡ innerQutrit x y
    preserves identityGate x y = refl
    preserves cycleGate x y = cyclePreservesInner laws x y
    preserves inverseCycleGate x y = inverseCyclePreservesInner laws x y

qutritPermutationUnitary :
  ∀ {A : ComplexStarSemiring} →
  ScalarAdditiveCommutativeLaws A →
  (gate : QutritGate) →
  QutritUnitary A (applyAmplitudeGate gate)
qutritPermutationUnitary laws =
  permutationGateUnitary (qutritPermutationInnerProductAuthority laws)
