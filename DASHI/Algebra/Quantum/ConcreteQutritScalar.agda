module DASHI.Algebra.Quantum.ConcreteQutritScalar where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex
open import DASHI.Algebra.Quantum.QutritAmplitude

record ComplexPairStarSemiringLaws
  (R : ConstructedOrderedCompleteReal) : Set₁ where
  field
    addZeroLeftC : ∀ z → _+C_ zeroC z ≡ z
    addZeroRightC : ∀ z → _+C_ z zeroC ≡ z
    mulOneLeftC : ∀ z → _*C_ oneC z ≡ z
    mulOneRightC : ∀ z → _*C_ z oneC ≡ z
    conjugateInvolutiveLaw : ∀ z → conjugateC (conjugateC z) ≡ z

open ComplexPairStarSemiringLaws public

complexPairStarSemiring :
  ∀ {R} →
  ComplexPairStarSemiringLaws R →
  ComplexStarSemiring
complexPairStarSemiring {R} laws =
  record
    { Scalar = ComplexPair R
    ; zeroS = zeroC
    ; oneS = oneC
    ; _+S_ = _+C_
    ; _*S_ = _*C_
    ; conjugate = conjugateC
    ; normSq = λ z → complex (normSqC z) (zero R)
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
