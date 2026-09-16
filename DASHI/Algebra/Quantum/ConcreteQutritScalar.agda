module DASHI.Algebra.Quantum.ConcreteQutritScalar where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex
open import DASHI.Algebra.Quantum.QutritAmplitude

record ComplexPairStarSemiringLaws
  (R : ConstructedOrderedCompleteReal) : Set₁ where
  field
    addZeroLeftC : ∀ (z : ComplexPair R) → _+C_ (zeroC {R}) z ≡ z
    addZeroRightC : ∀ (z : ComplexPair R) → _+C_ z (zeroC {R}) ≡ z
    mulOneLeftC : ∀ (z : ComplexPair R) → _*C_ (oneC {R}) z ≡ z
    mulOneRightC : ∀ (z : ComplexPair R) → _*C_ z (oneC {R}) ≡ z
    conjugateInvolutiveLaw : ∀ (z : ComplexPair R) → conjugateC (conjugateC z) ≡ z

open ComplexPairStarSemiringLaws public

complexPairStarSemiring :
  ∀ {R} →
  ComplexPairStarSemiringLaws R →
  ComplexStarSemiring
complexPairStarSemiring {R} laws =
  record
    { Scalar = ComplexPair R
    ; zeroS = zeroC {R}
    ; oneS = oneC {R}
    ; _+S_ = _+C_ {R}
    ; _*S_ = _*C_ {R}
    ; conjugate = conjugateC {R}
    ; normSq = λ (z : ComplexPair R) → complex (normSqC {R} z) (zero R)
    ; +-identityLeft = addZeroLeftC laws
    ; +-identityRight = addZeroRightC laws
    ; *-identityLeft = mulOneLeftC laws
    ; *-identityRight = mulOneRightC laws
    ; conjugateInvolutive = conjugateInvolutiveLaw laws
    }


record ConcreteQutritScalarPackage : Set₁ where
  field
    real : ConstructedOrderedCompleteReal
    complexLaws : ComplexPairStarSemiringLaws real

  scalarSemiring : ComplexStarSemiring
  scalarSemiring = complexPairStarSemiring complexLaws

  State : Set
  State = QutritState scalarSemiring

open ConcreteQutritScalarPackage public

record ConcreteQutritBornPackage
  (P : ConcreteQutritScalarPackage) : Set₁ where
  field
    NonnegativeReal : Set
    fromNormSquare : Real (real P) → NonnegativeReal
    probabilityOne : NonnegativeReal
    addProbability : NonnegativeReal → NonnegativeReal → NonnegativeReal

    bornNormalization : ∀ state →
      Normalized {A = scalarSemiring P} state →
      addProbability
        (addProbability
          (fromNormSquare (normSqC (ampNeg state)))
          (fromNormSquare (normSqC (ampZero state))))
        (fromNormSquare (normSqC (ampPos state)))
      ≡ probabilityOne

open ConcreteQutritBornPackage public
