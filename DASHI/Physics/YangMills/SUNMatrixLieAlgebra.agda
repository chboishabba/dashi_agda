module DASHI.Physics.YangMills.SUNMatrixLieAlgebra where

------------------------------------------------------------------------
-- Traceless anti-Hermitian matrices with the commutator bracket. Raw finite
-- matrix identities are isolated in a certified theory record; closure and the
-- Lie-algebra carrier are then assembled without SU(2)-specific coordinates.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieGroupCore
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.SUNMatrixCarrier

record SUNMatrixLieOperations
    {m c : Level} {Matrix : Set m} {Complex : Set c}
    (matrixOps : ComplexMatrixOperations Matrix Complex) :
    Set (lsuc (m ⊔ c)) where
  field
    zeroM : Matrix
    addM : Matrix → Matrix → Matrix
    negateM : Matrix → Matrix
    traceM : Matrix → Complex
    zeroC : Complex

open SUNMatrixLieOperations public

commutator :
  ∀ {m c} {Matrix : Set m} {Complex : Set c}
    {matrixOps : ComplexMatrixOperations Matrix Complex} →
  SUNMatrixLieOperations matrixOps → Matrix → Matrix → Matrix
commutator lieOps X Y =
  addM lieOps
    (multiplyM _ X Y)
    (negateM lieOps (multiplyM _ Y X))

record IsSUNLieElement
    {m c : Level} {Matrix : Set m} {Complex : Set c}
    {matrixOps : ComplexMatrixOperations Matrix Complex}
    (lieOps : SUNMatrixLieOperations matrixOps)
    (X : Matrix) : Set (m ⊔ c) where
  field
    antiHermitian : daggerM matrixOps X ≡ negateM lieOps X
    traceZero : traceM lieOps X ≡ zeroC lieOps

open IsSUNLieElement public

record CertifiedSUNMatrixLieTheory
    {m c : Level} (N : Nat)
    {Matrix : Set m} {Complex : Set c}
    (groupTheory : CertifiedSUNMatrixTheory N Matrix Complex) :
    Set (lsuc (m ⊔ c)) where
  field
    lieOperations : SUNMatrixLieOperations (operations groupTheory)

    zeroClosed : IsSUNLieElement lieOperations (zeroM lieOperations)
    addClosed : ∀ {X Y} →
      IsSUNLieElement lieOperations X →
      IsSUNLieElement lieOperations Y →
      IsSUNLieElement lieOperations (addM lieOperations X Y)
    negateClosed : ∀ {X} →
      IsSUNLieElement lieOperations X →
      IsSUNLieElement lieOperations (negateM lieOperations X)
    commutatorClosed : ∀ {X Y} →
      IsSUNLieElement lieOperations X →
      IsSUNLieElement lieOperations Y →
      IsSUNLieElement lieOperations (commutator lieOperations X Y)

    addAssociativeRaw : ∀ X Y Z →
      addM lieOperations (addM lieOperations X Y) Z ≡
      addM lieOperations X (addM lieOperations Y Z)
    addCommutativeRaw : ∀ X Y →
      addM lieOperations X Y ≡ addM lieOperations Y X
    zeroLeftRaw : ∀ X → addM lieOperations (zeroM lieOperations) X ≡ X
    additiveInverseRaw : ∀ X →
      addM lieOperations (negateM lieOperations X) X ≡ zeroM lieOperations

    bracketAlternatingRaw : ∀ X →
      commutator lieOperations X X ≡ zeroM lieOperations
    bracketAddLeftRaw : ∀ X Y Z →
      commutator lieOperations (addM lieOperations X Y) Z ≡
      addM lieOperations
        (commutator lieOperations X Z)
        (commutator lieOperations Y Z)
    bracketAddRightRaw : ∀ X Y Z →
      commutator lieOperations X (addM lieOperations Y Z) ≡
      addM lieOperations
        (commutator lieOperations X Y)
        (commutator lieOperations X Z)
    jacobiRaw : ∀ X Y Z →
      addM lieOperations
        (commutator lieOperations X (commutator lieOperations Y Z))
        (addM lieOperations
          (commutator lieOperations Y (commutator lieOperations Z X))
          (commutator lieOperations Z (commutator lieOperations X Y)))
      ≡ zeroM lieOperations

open CertifiedSUNMatrixLieTheory public

record SUNMatrixLieElement
    {m c : Level} {N : Nat}
    {Matrix : Set m} {Complex : Set c}
    {groupTheory : CertifiedSUNMatrixTheory N Matrix Complex}
    (lieTheory : CertifiedSUNMatrixLieTheory N groupTheory) : Set (m ⊔ c) where
  constructor sunLieMatrix
  field
    lieMatrix : Matrix
    .isSUNLie : IsSUNLieElement (lieOperations lieTheory) lieMatrix

open SUNMatrixLieElement public

sunLieMatrixExt :
  ∀ {m c N} {Matrix : Set m} {Complex : Set c}
    {groupTheory : CertifiedSUNMatrixTheory N Matrix Complex}
    {lieTheory : CertifiedSUNMatrixLieTheory N groupTheory}
    {X Y : SUNMatrixLieElement lieTheory} →
  lieMatrix X ≡ lieMatrix Y → X ≡ Y
sunLieMatrixExt {X = sunLieMatrix X xLie} {Y = sunLieMatrix .X yLie} refl = refl

sunMatrixLieAlgebra :
  ∀ {m c N} {Matrix : Set m} {Complex : Set c}
    {groupTheory : CertifiedSUNMatrixTheory N Matrix Complex} →
  (lieTheory : CertifiedSUNMatrixLieTheory N groupTheory) →
  LieAlgebra (SUNMatrixLieElement lieTheory)
sunMatrixLieAlgebra lieTheory = record
  { zero = sunLieMatrix
      (zeroM (lieOperations lieTheory))
      (zeroClosed lieTheory)
  ; add = λ X Y → sunLieMatrix
      (addM (lieOperations lieTheory) (lieMatrix X) (lieMatrix Y))
      (addClosed lieTheory (isSUNLie X) (isSUNLie Y))
  ; negate = λ X → sunLieMatrix
      (negateM (lieOperations lieTheory) (lieMatrix X))
      (negateClosed lieTheory (isSUNLie X))
  ; bracket = λ X Y → sunLieMatrix
      (commutator (lieOperations lieTheory) (lieMatrix X) (lieMatrix Y))
      (commutatorClosed lieTheory (isSUNLie X) (isSUNLie Y))
  ; addAssociative = λ X Y Z →
      sunLieMatrixExt (addAssociativeRaw lieTheory (lieMatrix X) (lieMatrix Y) (lieMatrix Z))
  ; addCommutative = λ X Y →
      sunLieMatrixExt (addCommutativeRaw lieTheory (lieMatrix X) (lieMatrix Y))
  ; zeroLeft = λ X → sunLieMatrixExt (zeroLeftRaw lieTheory (lieMatrix X))
  ; additiveInverse = λ X →
      sunLieMatrixExt (additiveInverseRaw lieTheory (lieMatrix X))
  ; bracketAlternating = λ X →
      sunLieMatrixExt (bracketAlternatingRaw lieTheory (lieMatrix X))
  ; bracketAddLeft = λ X Y Z →
      sunLieMatrixExt (bracketAddLeftRaw lieTheory (lieMatrix X) (lieMatrix Y) (lieMatrix Z))
  ; bracketAddRight = λ X Y Z →
      sunLieMatrixExt (bracketAddRightRaw lieTheory (lieMatrix X) (lieMatrix Y) (lieMatrix Z))
  ; jacobi = λ X Y Z →
      sunLieMatrixExt (jacobiRaw lieTheory (lieMatrix X) (lieMatrix Y) (lieMatrix Z))
  }

sunMatrixLieAlgebraLevel : ProofLevel
sunMatrixLieAlgebraLevel = machineChecked

finiteMatrixLieIdentityAuthorityLevel : ProofLevel
finiteMatrixLieIdentityAuthorityLevel = standardImported
