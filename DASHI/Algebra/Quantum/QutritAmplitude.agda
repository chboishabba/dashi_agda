module DASHI.Algebra.Quantum.QutritAmplitude where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Algebra.Quantum.TernaryCircuit

record ComplexStarSemiring : Set₁ where
  field
    Scalar : Set
    zeroS oneS : Scalar
    _+S_ _*S_ : Scalar → Scalar → Scalar
    conjugate : Scalar → Scalar
    normSq : Scalar → Scalar

    +-identityLeft : ∀ x → zeroS +S x ≡ x
    +-identityRight : ∀ x → x +S zeroS ≡ x
    *-identityLeft : ∀ x → oneS *S x ≡ x
    *-identityRight : ∀ x → x *S oneS ≡ x
    conjugateInvolutive : ∀ x → conjugate (conjugate x) ≡ x

open ComplexStarSemiring public

record QutritState (A : ComplexStarSemiring) : Set where
  constructor qstate
  field
    ampNeg : Scalar A
    ampZero : Scalar A
    ampPos : Scalar A

open QutritState public

basisState :
  (A : ComplexStarSemiring) →
  QutritBasis →
  QutritState A
basisState A qNeg = qstate (oneS A) (zeroS A) (zeroS A)
basisState A qZero = qstate (zeroS A) (oneS A) (zeroS A)
basisState A qPos = qstate (zeroS A) (zeroS A) (oneS A)

scaleState :
  ∀ {A} →
  Scalar A →
  QutritState A →
  QutritState A
scaleState {A} scalar (qstate a b c) =
  qstate (_*S_ A scalar a) (_*S_ A scalar b) (_*S_ A scalar c)

addState :
  ∀ {A} →
  QutritState A →
  QutritState A →
  QutritState A
addState {A} (qstate a b c) (qstate x y z) =
  qstate (_+S_ A a x) (_+S_ A b y) (_+S_ A c z)

innerQutrit :
  ∀ {A} →
  QutritState A →
  QutritState A →
  Scalar A
innerQutrit {A} (qstate a b c) (qstate x y z) =
  _+S_ A
    (_+S_ A
      (_*S_ A (conjugate A a) x)
      (_*S_ A (conjugate A b) y))
    (_*S_ A (conjugate A c) z)

stateNormSq :
  ∀ {A} →
  QutritState A →
  Scalar A
stateNormSq {A} (qstate a b c) =
  _+S_ A (_+S_ A (normSq A a) (normSq A b)) (normSq A c)

Normalized :
  ∀ {A} →
  QutritState A →
  Set
Normalized {A} state = stateNormSq state ≡ oneS A

applyAmplitudeGate :
  ∀ {A} →
  QutritGate →
  QutritState A →
  QutritState A
applyAmplitudeGate identityGate state = state
applyAmplitudeGate cycleGate (qstate a b c) = qstate c a b
applyAmplitudeGate inverseCycleGate (qstate a b c) = qstate b c a

amplitudeInverseLeft :
  ∀ {A} gate (state : QutritState A) →
  applyAmplitudeGate (inverseGate gate)
    (applyAmplitudeGate gate state)
  ≡ state
amplitudeInverseLeft identityGate state = refl
amplitudeInverseLeft cycleGate (qstate a b c) = refl
amplitudeInverseLeft inverseCycleGate (qstate a b c) = refl

amplitudeInverseRight :
  ∀ {A} gate (state : QutritState A) →
  applyAmplitudeGate gate
    (applyAmplitudeGate (inverseGate gate) state)
  ≡ state
amplitudeInverseRight identityGate state = refl
amplitudeInverseRight cycleGate (qstate a b c) = refl
amplitudeInverseRight inverseCycleGate (qstate a b c) = refl

record QutritMatrix (A : ComplexStarSemiring) : Set where
  constructor qmatrix
  field
    rowNeg : QutritState A
    rowZero : QutritState A
    rowPos : QutritState A

open QutritMatrix public

record QutritUnitary
  (A : ComplexStarSemiring)
  (U : QutritState A → QutritState A)
  : Set₁ where

  field
    inverseU : QutritState A → QutritState A
    inverseLeftU : ∀ state → inverseU (U state) ≡ state
    inverseRightU : ∀ state → U (inverseU state) ≡ state
    preservesInner : ∀ x y → innerQutrit (U x) (U y) ≡ innerQutrit x y

open QutritUnitary public

record PermutationGateInnerProductAuthority
  (A : ComplexStarSemiring)
  : Set₁ where

  field
    permutationPreservesInner :
      ∀ gate x y →
      innerQutrit (applyAmplitudeGate gate x)
        (applyAmplitudeGate gate y)
      ≡ innerQutrit x y

open PermutationGateInnerProductAuthority public

permutationGateUnitary :
  ∀ {A} →
  PermutationGateInnerProductAuthority A →
  (gate : QutritGate) →
  QutritUnitary A (applyAmplitudeGate gate)
permutationGateUnitary authority gate =
  record
    { inverseU = applyAmplitudeGate (inverseGate gate)
    ; inverseLeftU = amplitudeInverseLeft gate
    ; inverseRightU = amplitudeInverseRight gate
    ; preservesInner = permutationPreservesInner authority gate
    }

record QutritBornAuthority (A : ComplexStarSemiring) : Set₁ where
  field
    Probability : Set
    probabilityOfScalar : Scalar A → Probability
    totalOne : Probability
    _+P_ : Probability → Probability → Probability

    bornTotal :
      ∀ state →
      Normalized state →
      _+P_
        (_+P_
          (probabilityOfScalar (normSq A (ampNeg state)))
          (probabilityOfScalar (normSq A (ampZero state))))
        (probabilityOfScalar (normSq A (ampPos state)))
      ≡ totalOne

open QutritBornAuthority public

record QutritMeasurement
  {A : ComplexStarSemiring}
  (B : QutritBornAuthority A)
  (state : QutritState A)
  : Set₁ where

  field
    normalized : Normalized state

  probabilityNeg : Probability B
  probabilityNeg = probabilityOfScalar B (normSq A (ampNeg state))

  probabilityZero : Probability B
  probabilityZero = probabilityOfScalar B (normSq A (ampZero state))

  probabilityPos : Probability B
  probabilityPos = probabilityOfScalar B (normSq A (ampPos state))

  probabilitiesSumToOne :
    _+P_ B (_+P_ B probabilityNeg probabilityZero) probabilityPos
    ≡ totalOne B
  probabilitiesSumToOne = bornTotal B state normalized

open QutritMeasurement public

record TwoQutritState (A : ComplexStarSemiring) : Set where
  constructor twoQutritState
  field
    ampNN ampNZ ampNP : Scalar A
    ampZN ampZZ ampZP : Scalar A
    ampPN ampPZ ampPP : Scalar A

open TwoQutritState public

tensorQutrit :
  ∀ {A} →
  QutritState A →
  QutritState A →
  TwoQutritState A
tensorQutrit {A} (qstate a b c) (qstate x y z) =
  twoQutritState
    (_*S_ A a x) (_*S_ A a y) (_*S_ A a z)
    (_*S_ A b x) (_*S_ A b y) (_*S_ A b z)
    (_*S_ A c x) (_*S_ A c y) (_*S_ A c z)
