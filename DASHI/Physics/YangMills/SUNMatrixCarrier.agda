{-# OPTIONS --irrelevant-projections #-}

module DASHI.Physics.YangMills.SUNMatrixCarrier where

------------------------------------------------------------------------
-- A concrete matrix presentation of SU(N), separated from any particular
-- implementation of finite complex matrices. The finite-matrix laws are
-- standard imported mathematics; once supplied, the SU(N) group laws below
-- are ordinary machine-checked record assembly.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieGroupCore
open import DASHI.Physics.YangMills.CompactLieProofLevel

record ComplexMatrixOperations {m c : Level}
    (Matrix : Set m) (Complex : Set c) : Set (lsuc (m ⊔ c)) where
  field
    identityM : Matrix
    multiplyM : Matrix → Matrix → Matrix
    daggerM : Matrix → Matrix
    determinant : Matrix → Complex
    oneC : Complex

open ComplexMatrixOperations public

record IsUnitDeterminant
    {m c : Level} {Matrix : Set m} {Complex : Set c}
    (ops : ComplexMatrixOperations Matrix Complex)
    (U : Matrix) : Set (m ⊔ c) where
  field
    determinantOne : determinant ops U ≡ oneC ops

record IsSpecialUnitary
    {m c : Level} {Matrix : Set m} {Complex : Set c}
    (ops : ComplexMatrixOperations Matrix Complex)
    (U : Matrix) : Set (m ⊔ c) where
  field
    unitaryLeft :
      multiplyM ops (daggerM ops U) U ≡ identityM ops
    unitaryRight :
      multiplyM ops U (daggerM ops U) ≡ identityM ops
    specialDeterminant : IsUnitDeterminant ops U

private
  proofIrrelevant : ∀ {a} {A : Set a} {x y : A} (p1 p2 : x ≡ y) → p1 ≡ p2
  proofIrrelevant refl refl = refl

  cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
  cong f refl = refl

  isSpecialUnitaryExt :
    ∀ {m c} {Matrix : Set m} {Complex : Set c}
      {ops : ComplexMatrixOperations Matrix Complex} {M : Matrix}
      (s1 s2 : IsSpecialUnitary ops M) → s1 ≡ s2
  isSpecialUnitaryExt
    (record { unitaryLeft = uL1 ; unitaryRight = uR1 ; specialDeterminant = record { determinantOne = d1 } })
    (record { unitaryLeft = uL2 ; unitaryRight = uR2 ; specialDeterminant = record { determinantOne = d2 } })
    with proofIrrelevant uL1 uL2 | proofIrrelevant uR1 uR2 | proofIrrelevant d1 d2
  ... | refl | refl | refl = refl

record CertifiedSUNMatrixTheory
    {m c : Level} (N : Nat)
    (Matrix : Set m) (Complex : Set c) : Set (lsuc (m ⊔ c)) where
  field
    operations : ComplexMatrixOperations Matrix Complex

    multiplyAssociative : ∀ A B C →
      multiplyM operations (multiplyM operations A B) C ≡
      multiplyM operations A (multiplyM operations B C)
    identityLeft : ∀ A →
      multiplyM operations (identityM operations) A ≡ A
    identityRight : ∀ A →
      multiplyM operations A (identityM operations) ≡ A
    daggerInvolutive : ∀ A → daggerM operations (daggerM operations A) ≡ A

    identitySpecial : IsSpecialUnitary operations (identityM operations)
    multiplySpecial : ∀ {A B} →
      IsSpecialUnitary operations A →
      IsSpecialUnitary operations B →
      IsSpecialUnitary operations (multiplyM operations A B)
    daggerSpecial : ∀ {A} →
      IsSpecialUnitary operations A →
      IsSpecialUnitary operations (daggerM operations A)

open CertifiedSUNMatrixTheory public

record SUNMatrixElement
    {m c : Level} {N : Nat}
    {Matrix : Set m} {Complex : Set c}
    (theory : CertifiedSUNMatrixTheory N Matrix Complex) : Set (m ⊔ c) where
  constructor sunMatrix
  field
    matrix : Matrix
    specialUnitary : IsSpecialUnitary (operations theory) matrix

open SUNMatrixElement public

sunMatrixExt :
  ∀ {m c N} {Matrix : Set m} {Complex : Set c}
    {theory : CertifiedSUNMatrixTheory N Matrix Complex}
    {A B : SUNMatrixElement theory} →
  matrix A ≡ matrix B → A ≡ B
sunMatrixExt {A = sunMatrix M s1} {B = sunMatrix .M s2} refl =
  cong (sunMatrix M) (isSpecialUnitaryExt s1 s2)

sunIdentity :
  ∀ {m c N} {Matrix : Set m} {Complex : Set c}
    (theory : CertifiedSUNMatrixTheory N Matrix Complex) →
  SUNMatrixElement theory
sunIdentity theory =
  sunMatrix (identityM (operations theory)) (identitySpecial theory)

sunMultiply :
  ∀ {m c N} {Matrix : Set m} {Complex : Set c}
    (theory : CertifiedSUNMatrixTheory N Matrix Complex) →
  SUNMatrixElement theory → SUNMatrixElement theory → SUNMatrixElement theory
sunMultiply theory A B =
  sunMatrix
    (multiplyM (operations theory) (matrix A) (matrix B))
    (multiplySpecial theory (specialUnitary A) (specialUnitary B))

sunInverse :
  ∀ {m c N} {Matrix : Set m} {Complex : Set c}
    (theory : CertifiedSUNMatrixTheory N Matrix Complex) →
  SUNMatrixElement theory → SUNMatrixElement theory
sunInverse theory A =
  sunMatrix
    (daggerM (operations theory) (matrix A))
    (daggerSpecial theory (specialUnitary A))

sunMatrixGroup :
  ∀ {m c N} {Matrix : Set m} {Complex : Set c} →
  (theory : CertifiedSUNMatrixTheory N Matrix Complex) →
  Group (SUNMatrixElement theory)
sunMatrixGroup theory = record
  { identity = sunIdentity theory
  ; multiply = sunMultiply theory
  ; inverse = sunInverse theory
  ; multiplyAssociative = λ A B C →
      sunMatrixExt (multiplyAssociative theory (matrix A) (matrix B) (matrix C))
  ; identityLeft = λ A → sunMatrixExt (identityLeft theory (matrix A))
  ; identityRight = λ A → sunMatrixExt (identityRight theory (matrix A))
  ; inverseLeft = λ A → sunMatrixExt (IsSpecialUnitary.unitaryLeft (specialUnitary A))
  ; inverseRight = λ A → sunMatrixExt (IsSpecialUnitary.unitaryRight (specialUnitary A))
  }

sunMatrixCarrierLevel : ProofLevel
sunMatrixCarrierLevel = machineChecked

finiteComplexMatrixAuthorityLevel : ProofLevel
finiteComplexMatrixAuthorityLevel = standardImported
