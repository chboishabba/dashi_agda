module DASHI.Algebra.Quantum.QutritAmplitude where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Algebra.Quantum.TernaryCircuit

------------------------------------------------------------------------
-- Exact amplitude-level qutrit interface.  Scalar analysis remains parameterized
-- by an explicit complex-star-semiring authority; this module contributes no
-- hidden postulates and is reusable by finite exact, algebraic, or analytic models.

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
  qstate (scalar *S a) (scalar *S b) (scalar *S c)
  where open ComplexStarSemiring A

addState :
  ∀ {A} →
  QutritState A →
  QutritState A →
  QutritState A
addState {A} (qstate a b c) (qstate x y z) =
  qstate (a +S x) (b +S y) (c +S z)
  where open ComplexStarSemiring A

innerQutrit :
  ∀ {A} →
  QutritState A →
  QutritState A →
  Scalar A
innerQutrit {A} (qstate a b c) (qstate x y z) =
  ((conjugate a *S x) +S (conjugate b *S y)) +S
  (conjugate c *S z)
  where open ComplexStarSemiring A

stateNormSq :
  ∀ {A} →
  QutritState A →
  Scalar A
stateNormSq {A} (qstate a b c) =
  (normSq a +S normSq b) +S normSq c
  where open ComplexStarSemiring A

Normalized :
  ∀ {A} →
  QutritState A →
  Set
Normalized {A} state = stateNormSq state ≡ oneS A

------------------------------------------------------------------------
-- Concrete amplitude actions of the basis permutation gates.

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

------------------------------------------------------------------------
-- Matrix and unitary interfaces.

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

------------------------------------------------------------------------
-- Projective measurement.  `Probability` and normalization of the three Born
-- weights are supplied by the selected scalar/probability authority.

record QutritBornAuthority (A : ComplexStarSemiring) : Set₁ where
  field
    Probability : Set
    probabilityOfScalar : Scalar A → Probability
    totalOne : Probability
    _+P_ : Probability → Probability → Probability

    bornTotal :
      ∀ state →
      Normalized state →
      (probabilityOfScalar (normSq A (ampNeg state)) +P
       probabilityOfScalar (normSq A (ampZero state))) +P
       probabilityOfScalar (normSq A (ampPos state))
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
    (probabilityNeg +P probabilityZero) +P probabilityPos
    ≡ totalOne B
  probabilitiesSumToOne = bornTotal B state normalized

  where open QutritBornAuthority B

open QutritMeasurement public

------------------------------------------------------------------------
-- Tensor-product carrier for two qutrits.  The nine amplitudes are explicit,
-- avoiding an unproved finite-index implementation.

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
    (a *S x) (a *S y) (a *S z)
    (b *S x) (b *S y) (b *S z)
    (c *S x) (c *S y) (c *S z)
  where open ComplexStarSemiring A
