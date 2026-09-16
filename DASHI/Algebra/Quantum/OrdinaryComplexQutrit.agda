module DASHI.Algebra.Quantum.OrdinaryComplexQutrit where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex
open import DASHI.Algebra.Quantum.TernaryCircuit
open import DASHI.Algebra.Quantum.QutritAmplitude
open import DASHI.Algebra.Quantum.ConcreteQutritScalar
open import DASHI.Algebra.Quantum.QutritMatrixGates

------------------------------------------------------------------------
-- Finite complex algebra derived from the constructed real carrier.

record RealZeroMultiplicationLaws
  (R : ConstructedOrderedCompleteReal) : Set₁ where
  field
    mulZeroLeft : ∀ x → _*_ R (zero R) x ≡ zero R
    mulZeroRight : ∀ x → _*_ R x (zero R) ≡ zero R

open RealZeroMultiplicationLaws public

complexAddZeroLeft :
  ∀ {R : ConstructedOrderedCompleteReal} →
  (z : ComplexPair R) →
  _+C_ zeroC z ≡ z
complexAddZeroLeft {R} (complex a b)
  rewrite addZeroLeft R a
        | addZeroLeft R b = refl

complexAddZeroRight :
  ∀ {R : ConstructedOrderedCompleteReal} →
  (z : ComplexPair R) →
  _+C_ z zeroC ≡ z
complexAddZeroRight {R} (complex a b)
  rewrite addZeroRight R a
        | addZeroRight R b = refl

complexMulZeroLeft :
  ∀ {R : ConstructedOrderedCompleteReal} →
  RealZeroMultiplicationLaws R →
  (z : ComplexPair R) →
  _*C_ zeroC z ≡ zeroC
complexMulZeroLeft {R} Z (complex a b)
  rewrite mulZeroLeft Z a
        | mulZeroLeft Z b
        | subSelf R (zero R)
        | addZeroLeft R (zero R) = refl

complexMulZeroRight :
  ∀ {R : ConstructedOrderedCompleteReal} →
  RealZeroMultiplicationLaws R →
  (z : ComplexPair R) →
  _*C_ z zeroC ≡ zeroC
complexMulZeroRight {R} Z (complex a b)
  rewrite mulZeroRight Z a
        | mulZeroRight Z b
        | subSelf R (zero R)
        | addZeroLeft R (zero R) = refl

complexMulOneLeft :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ComplexAlgebraLaws R →
  RealZeroMultiplicationLaws R →
  (z : ComplexPair R) →
  _*C_ oneC z ≡ z
complexMulOneLeft {R} C Z (complex a b)
  rewrite mulOneLeft R a
        | mulZeroLeft Z b
        | subZeroRight C a
        | mulOneLeft R b
        | mulZeroLeft Z a
        | addZeroRight R b = refl

complexMulOneRight :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ComplexAlgebraLaws R →
  RealZeroMultiplicationLaws R →
  (z : ComplexPair R) →
  _*C_ z oneC ≡ z
complexMulOneRight {R} C Z (complex a b)
  rewrite mulOneRight R a
        | mulZeroRight Z b
        | subZeroRight C a
        | mulZeroRight Z a
        | mulOneRight R b
        | addZeroLeft R b = refl

ordinaryComplexPairStarLaws :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ComplexAlgebraLaws R →
  RealZeroMultiplicationLaws R →
  ComplexPairStarSemiringLaws R
ordinaryComplexPairStarLaws C Z =
  record
    { addZeroLeftC = complexAddZeroLeft
    ; addZeroRightC = complexAddZeroRight
    ; mulOneLeftC = complexMulOneLeft C Z
    ; mulOneRightC = complexMulOneRight C Z
    ; conjugateInvolutiveLaw = conjugateInvolutiveC C
    }

ordinaryQutritScalarPackage :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ComplexAlgebraLaws R →
  RealZeroMultiplicationLaws R →
  ConcreteQutritScalarPackage
ordinaryQutritScalarPackage {R} C Z =
  record
    { real = R
    ; complexLaws = ordinaryComplexPairStarLaws C Z
    }

------------------------------------------------------------------------
-- Computational-basis Born probabilities are the real norm squares.

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

ordinaryQutritBornAuthority :
  ∀ {R : ConstructedOrderedCompleteReal}
    (C : ComplexAlgebraLaws R)
    (Z : RealZeroMultiplicationLaws R) →
  QutritBornAuthority
    (scalarSemiring (ordinaryQutritScalarPackage C Z))
ordinaryQutritBornAuthority {R} C Z =
  record
    { Probability = Real R
    ; probabilityOfScalar = re
    ; totalOne = one R
    ; _+P_ = _+_ R
    ; bornTotal = bornTotalReal
    }
  where
    P : ConcreteQutritScalarPackage
    P = ordinaryQutritScalarPackage C Z

    bornTotalReal : ∀ state →
      Normalized {A = scalarSemiring P} state →
      _+_ R
        (_+_ R
          (normSqC {R} (ampNeg state))
          (normSqC {R} (ampZero state)))
        (normSqC {R} (ampPos state))
      ≡ one R
    bornTotalReal (qstate a b c) normalized = cong re normalized

record PhysicalProbabilityLaws
  {R : ConstructedOrderedCompleteReal}
  (C : ComplexAlgebraLaws R)
  (Z : RealZeroMultiplicationLaws R) : Set₁ where
  field
    normSquareNonnegative : ∀ z → _≤_ R (zero R) (normSqC {R} z)
    probabilityOneNonnegative : _≤_ R (zero R) (one R)
    addNonnegative : ∀ {x y} →
      _≤_ R (zero R) x →
      _≤_ R (zero R) y →
      _≤_ R (zero R) (_+_ R x y)

open PhysicalProbabilityLaws public

------------------------------------------------------------------------
-- Matrix realization of the existing single-qutrit permutation gates.

ordinaryMatrixSimplification :
  ∀ {R : ConstructedOrderedCompleteReal}
    (C : ComplexAlgebraLaws R)
    (Z : RealZeroMultiplicationLaws R) →
  MatrixSimplificationAuthority
    (scalarSemiring (ordinaryQutritScalarPackage C Z))
ordinaryMatrixSimplification {R} C Z =
  record
    { matrixCycleAgrees = cycleAgrees
    ; matrixInverseCycleAgrees = inverseCycleAgrees
    }
  where
    P : ConcreteQutritScalarPackage
    P = ordinaryQutritScalarPackage C Z

    A : ComplexStarSemiring
    A = scalarSemiring P

    elim001 :
      ∀ x y u v z w →
      _+_ R (_+_ R (_-_ R (_*_ R (zero R) x) (_*_ R (zero R) y))
                   (_-_ R (_*_ R (zero R) u) (_*_ R (zero R) v)))
            (_-_ R (_*_ R (one R) z) (_*_ R (zero R) w))
      ≡ z
    elim001 x y u v z w
      rewrite mulZeroLeft Z x
            | mulZeroLeft Z y
            | mulZeroLeft Z u
            | mulZeroLeft Z v
            | mulZeroLeft Z w
            | mulOneLeft R z
            | subSelf R (zero R)
            | subZeroRight C z
            | addZeroLeft R (zero R)
            | addZeroLeft R z = refl

    elim001-add :
      ∀ x y u v z w →
      _+_ R (_+_ R (_+_ R (_*_ R (zero R) x) (_*_ R (zero R) y))
                   (_+_ R (_*_ R (zero R) u) (_*_ R (zero R) v)))
            (_+_ R (_*_ R (one R) z) (_*_ R (zero R) w))
      ≡ z
    elim001-add x y u v z w
      rewrite mulZeroLeft Z x
            | mulZeroLeft Z y
            | mulZeroLeft Z u
            | mulZeroLeft Z v
            | mulZeroLeft Z w
            | mulOneLeft R z
            | addZeroLeft R (zero R)
            | addZeroRight R z
            | addZeroLeft R (zero R)
            | addZeroLeft R z = refl

    elim100 :
      ∀ x y u v z w →
      _+_ R (_+_ R (_-_ R (_*_ R (one R) x) (_*_ R (zero R) y))
                   (_-_ R (_*_ R (zero R) u) (_*_ R (zero R) v)))
            (_-_ R (_*_ R (zero R) z) (_*_ R (zero R) w))
      ≡ x
    elim100 x y u v z w
      rewrite mulOneLeft R x
            | mulZeroLeft Z y
            | mulZeroLeft Z u
            | mulZeroLeft Z v
            | mulZeroLeft Z z
            | mulZeroLeft Z w
            | subZeroRight C x
            | subSelf R (zero R)
            | addZeroRight R x
            | addZeroRight R x = refl

    elim100-add :
      ∀ x y u v z w →
      _+_ R (_+_ R (_+_ R (_*_ R (one R) x) (_*_ R (zero R) y))
                   (_+_ R (_*_ R (zero R) u) (_*_ R (zero R) v)))
            (_+_ R (_*_ R (zero R) z) (_*_ R (zero R) w))
      ≡ x
    elim100-add x y u v z w
      rewrite mulOneLeft R x
            | mulZeroLeft Z y
            | mulZeroLeft Z u
            | mulZeroLeft Z v
            | mulZeroLeft Z z
            | mulZeroLeft Z w
            | addZeroRight R x
            | addZeroLeft R (zero R)
            | addZeroRight R x
            | addZeroRight R x = refl

    elim010 :
      ∀ x y u v z w →
      _+_ R (_+_ R (_-_ R (_*_ R (zero R) x) (_*_ R (zero R) y))
                   (_-_ R (_*_ R (one R) u) (_*_ R (zero R) v)))
            (_-_ R (_*_ R (zero R) z) (_*_ R (zero R) w))
      ≡ u
    elim010 x y u v z w
      rewrite mulZeroLeft Z x
            | mulZeroLeft Z y
            | mulOneLeft R u
            | mulZeroLeft Z v
            | mulZeroLeft Z z
            | mulZeroLeft Z w
            | subZeroRight C u
            | subSelf R (zero R)
            | addZeroLeft R u
            | addZeroRight R u = refl

    elim010-add :
      ∀ x y u v z w →
      _+_ R (_+_ R (_+_ R (_*_ R (zero R) x) (_*_ R (zero R) y))
                   (_+_ R (_*_ R (one R) u) (_*_ R (zero R) v)))
            (_+_ R (_*_ R (zero R) z) (_*_ R (zero R) w))
      ≡ u
    elim010-add x y u v z w
      rewrite mulZeroLeft Z x
            | mulZeroLeft Z y
            | mulOneLeft R u
            | mulZeroLeft Z v
            | mulZeroLeft Z z
            | mulZeroLeft Z w
            | addZeroRight R u
            | addZeroLeft R (zero R)
            | addZeroLeft R u
            | addZeroRight R u = refl

    cycleAgrees : ∀ state →
      applyMatrix3 (cycleMatrix3 {A}) state
      ≡ applyAmplitudeGate cycleGate state
    cycleAgrees (qstate (complex ar ai) (complex br bi) (complex cr ci))
      rewrite elim001 ar ai br bi cr ci
            | elim001-add ai ar bi br ci cr
            | elim100 ar ai br bi cr ci
            | elim100-add ai ar bi br ci cr
            | elim010 ar ai br bi cr ci
            | elim010-add ai ar bi br ci cr = refl

    inverseCycleAgrees : ∀ state →
      applyMatrix3 (inverseCycleMatrix3 {A}) state
      ≡ applyAmplitudeGate inverseCycleGate state
    inverseCycleAgrees (qstate (complex ar ai) (complex br bi) (complex cr ci))
      rewrite elim010 ar ai br bi cr ci
            | elim010-add ai ar bi br ci cr
            | elim001 ar ai br bi cr ci
            | elim001-add ai ar bi br ci cr
            | elim100 ar ai br bi cr ci
            | elim100-add ai ar bi br ci cr = refl

------------------------------------------------------------------------
-- Analytic roots of unity promote directly to the finite qutrit gate package.

record OrdinaryQutritRootData
  {R : ConstructedOrderedCompleteReal}
  (C : ComplexAlgebraLaws R)
  (Z : RealZeroMultiplicationLaws R) : Set₁ where

  P : ConcreteQutritScalarPackage
  P = ordinaryQutritScalarPackage C Z

  A : ComplexStarSemiring
  A = scalarSemiring P

  field
    omega omegaSquared : ComplexPair R
    omegaCubedIsOne : _*C_ {R} (_*C_ {R} omega omega) omega ≡ oneC {R}
    rootSumZero : _+C_ {R} (_+C_ {R} (oneC {R}) omega) omegaSquared ≡ zeroC {R}
    omegaNormOne : complex (normSqC {R} omega) (zero R) ≡ oneC {R}

open OrdinaryQutritRootData public hiding (P; A)

ordinaryQutritRootOfUnity :
  ∀ {R : ConstructedOrderedCompleteReal}
    {C : ComplexAlgebraLaws R}
    {Z : RealZeroMultiplicationLaws R} →
  OrdinaryQutritRootData C Z →
  QutritRootOfUnity
    (scalarSemiring (ordinaryQutritScalarPackage C Z))
ordinaryQutritRootOfUnity {R} {C} {Z} W =
  record
    { omega = omega W
    ; omegaSquared = omegaSquared W
    ; omegaCubedIsOne = omegaCubedIsOne W
    ; rootSumZero = rootSumZero W
    ; omegaNormOne = omegaNormOne W
    }

------------------------------------------------------------------------
-- The ternary SUM gate as an amplitude permutation on C^9.

applyControlledCycleAmplitude :
  ∀ {A : ComplexStarSemiring} →
  TwoQutritState A →
  TwoQutritState A
applyControlledCycleAmplitude
  (twoQutritState nn nz np zn zz zp pn pz pp) =
  twoQutritState
    nn nz np
    zp zn zz
    pz pp pn

applyInverseControlledCycleAmplitude :
  ∀ {A : ComplexStarSemiring} →
  TwoQutritState A →
  TwoQutritState A
applyInverseControlledCycleAmplitude
  (twoQutritState nn nz np zn zz zp pn pz pp) =
  twoQutritState
    nn nz np
    zz zp zn
    pp pn pz

controlledCycleAmplitudeInverseLeft :
  ∀ {A : ComplexStarSemiring}
    (state : TwoQutritState A) →
  applyInverseControlledCycleAmplitude
    (applyControlledCycleAmplitude state)
  ≡ state
controlledCycleAmplitudeInverseLeft
  (twoQutritState nn nz np zn zz zp pn pz pp) = refl

controlledCycleAmplitudeInverseRight :
  ∀ {A : ComplexStarSemiring}
    (state : TwoQutritState A) →
  applyControlledCycleAmplitude
    (applyInverseControlledCycleAmplitude state)
  ≡ state
controlledCycleAmplitudeInverseRight
  (twoQutritState nn nz np zn zz zp pn pz pp) = refl
