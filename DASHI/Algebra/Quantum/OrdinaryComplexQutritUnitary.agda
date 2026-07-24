module DASHI.Algebra.Quantum.OrdinaryComplexQutritUnitary where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex
open import DASHI.Algebra.Quantum.TernaryCircuit
open import DASHI.Algebra.Quantum.QutritAmplitude
open import DASHI.Algebra.Quantum.ConcreteQutritScalar
open import DASHI.Algebra.Quantum.OrdinaryComplexQutrit
open import DASHI.Algebra.Quantum.QutritPermutationUnitary

complexAddAssoc :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ∀ a b c →
  _+C_ (_+C_ a b) c ≡ _+C_ a (_+C_ b c)
complexAddAssoc {R}
  (complex ar ai)
  (complex br bi)
  (complex cr ci)
  rewrite addAssoc R ar br cr
        | addAssoc R ai bi ci = refl

complexAddComm :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ∀ a b →
  _+C_ a b ≡ _+C_ b a
complexAddComm {R}
  (complex ar ai)
  (complex br bi)
  rewrite addComm R ar br
        | addComm R ai bi = refl

ordinaryComplexAdditiveLaws :
  ∀ {R : ConstructedOrderedCompleteReal}
    (C : ComplexAlgebraLaws R)
    (Z : RealZeroMultiplicationLaws R) →
  ScalarAdditiveCommutativeLaws
    (scalarSemiring (ordinaryQutritScalarPackage C Z))
ordinaryComplexAdditiveLaws C Z =
  record
    { addAssoc = complexAddAssoc
    ; addComm = complexAddComm
    }

ordinaryQutritPermutationUnitary :
  ∀ {R : ConstructedOrderedCompleteReal}
    (C : ComplexAlgebraLaws R)
    (Z : RealZeroMultiplicationLaws R) →
  (gate : QutritGate) →
  QutritUnitary
    (scalarSemiring (ordinaryQutritScalarPackage C Z))
    (applyAmplitudeGate gate)
ordinaryQutritPermutationUnitary C Z =
  qutritPermutationUnitary (ordinaryComplexAdditiveLaws C Z)

record OrdinaryPermutationMatrixUnitaryReceipt
  {R : ConstructedOrderedCompleteReal}
  (C : ComplexAlgebraLaws R)
  (Z : RealZeroMultiplicationLaws R) : Set₁ where

  A : ComplexStarSemiring
  A = scalarSemiring (ordinaryQutritScalarPackage C Z)

  field
    gate : QutritGate
    matrixAction : QutritState A → QutritState A
    matrixAgreesWithPermutation : ∀ state →
      matrixAction state ≡ applyAmplitudeGate gate state

  permutationUnitary :
    QutritUnitary A (applyAmplitudeGate gate)
  permutationUnitary = ordinaryQutritPermutationUnitary C Z gate

open OrdinaryPermutationMatrixUnitaryReceipt public
