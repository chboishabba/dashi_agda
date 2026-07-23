module DASHI.Algebra.Quantum.QutritMatrixGates where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Algebra.Quantum.TernaryCircuit
open import DASHI.Algebra.Quantum.QutritAmplitude

record Matrix3 (A : ComplexStarSemiring) : Set where
  constructor matrix3
  field
    mNN mNZ mNP : Scalar A
    mZN mZZ mZP : Scalar A
    mPN mPZ mPP : Scalar A

open Matrix3 public

applyMatrix3 :
  ∀ {A} →
  Matrix3 A →
  QutritState A →
  QutritState A
applyMatrix3 {A} M (qstate x y z) =
  qstate
    (_+S_ A (_+S_ A (_*S_ A (mNN M) x) (_*S_ A (mNZ M) y)) (_*S_ A (mNP M) z))
    (_+S_ A (_+S_ A (_*S_ A (mZN M) x) (_*S_ A (mZZ M) y)) (_*S_ A (mZP M) z))
    (_+S_ A (_+S_ A (_*S_ A (mPN M) x) (_*S_ A (mPZ M) y)) (_*S_ A (mPP M) z))

identityMatrix3 : ∀ {A} → Matrix3 A
identityMatrix3 {A} =
  matrix3
    (oneS A) (zeroS A) (zeroS A)
    (zeroS A) (oneS A) (zeroS A)
    (zeroS A) (zeroS A) (oneS A)

cycleMatrix3 : ∀ {A} → Matrix3 A
cycleMatrix3 {A} =
  matrix3
    (zeroS A) (zeroS A) (oneS A)
    (oneS A) (zeroS A) (zeroS A)
    (zeroS A) (oneS A) (zeroS A)

inverseCycleMatrix3 : ∀ {A} → Matrix3 A
inverseCycleMatrix3 {A} =
  matrix3
    (zeroS A) (oneS A) (zeroS A)
    (zeroS A) (zeroS A) (oneS A)
    (oneS A) (zeroS A) (zeroS A)

record MatrixSimplificationAuthority (A : ComplexStarSemiring) : Set₁ where
  field
    matrixCycleAgrees : ∀ state →
      applyMatrix3 (cycleMatrix3 {A}) state
      ≡ applyAmplitudeGate cycleGate state

    matrixInverseCycleAgrees : ∀ state →
      applyMatrix3 (inverseCycleMatrix3 {A}) state
      ≡ applyAmplitudeGate inverseCycleGate state

open MatrixSimplificationAuthority public

cycleMatrixAgreesWithBasisGate :
  ∀ {A} →
  MatrixSimplificationAuthority A →
  ∀ q →
  applyMatrix3 (cycleMatrix3 {A}) (basisState A q)
  ≡ basisState A (cycleQutrit q)
cycleMatrixAgreesWithBasisGate authority q
  rewrite matrixCycleAgrees authority (basisState _ q) = refl

record QutritRootOfUnity (A : ComplexStarSemiring) : Set₁ where
  field
    omega : Scalar A
    omegaSquared : Scalar A
    omegaCubedIsOne : _*S_ A (_*S_ A omega omega) omega ≡ oneS A
    rootSumZero : _+S_ A (_+S_ A (oneS A) omega) omegaSquared ≡ zeroS A
    omegaNormOne : normSq A omega ≡ oneS A

open QutritRootOfUnity public

phaseMatrix3 :
  ∀ {A} →
  QutritRootOfUnity A →
  Matrix3 A
phaseMatrix3 {A} W =
  matrix3
    (oneS A) (zeroS A) (zeroS A)
    (zeroS A) (omega W) (zeroS A)
    (zeroS A) (zeroS A) (omegaSquared W)

record QutritFourierAuthority (A : ComplexStarSemiring) : Set₁ where
  field
    root : QutritRootOfUnity A
    inverseSqrtThree : Scalar A
    fourier : Matrix3 A
    fourierInverse : Matrix3 A
    fourierInverseLeft : ∀ state →
      applyMatrix3 fourierInverse (applyMatrix3 fourier state) ≡ state
    fourierInverseRight : ∀ state →
      applyMatrix3 fourier (applyMatrix3 fourierInverse state) ≡ state

open QutritFourierAuthority public
