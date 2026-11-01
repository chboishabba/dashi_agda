module DASHI.Foundations.PhysicsLinearAnalysisParity where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List)
import Data.List.Base as ListBase
open import Data.Nat.Base using (ℕ; suc)

open import DASHI.Foundations.RealAnalysisAxioms renaming (absMul to realAbsMul)

infixr 4 _,_

record Sigma {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : A → Set ℓ₂) :
  Set (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    fst :
      A

    snd :
      B fst

open Sigma public

postulate
  ScalarCauchy :
    {Carrier : Set} →
    (Carrier → Carrier → Set) →
    (ℕ → Carrier) →
    Set

  ScalarConvergesTo :
    {Carrier : Set} →
    (Carrier → Carrier → Set) →
    (ℕ → Carrier) →
    Carrier →
    Set

  ScalarSequenceConvergesTo :
    (ℕ → ℝ) →
    ℝ →
    Set

------------------------------------------------------------------------
-- Fail-closed PhysLean parity surface for linear algebra and analysis.
--
-- This module deliberately exposes names and receipts, not local promotion
-- proofs.  It is a parity layer over the smaller real-analysis axiom socket.
-- Anything that would require a serious linear algebra, spectral theory, or
-- ODE development is represented as a named authority boundary and is marked
-- false in the canonical receipt below.

data ScalarDiscipline : Set where
  realScalars :
    ScalarDiscipline

  complexScalarsExternal :
    ScalarDiscipline

record ScalarFieldLawShape
  (Carrier : Set)
  (zero one : Carrier)
  (_+_ _*_ _-_ : Carrier → Carrier → Carrier)
  (-_ abs : Carrier → Carrier) :
  Set₁ where
  field
    addComm :
      (x y : Carrier) →
      Set

    addAssoc :
      (x y z : Carrier) →
      Set

    addZeroL :
      (x : Carrier) →
      Set

    addInvL :
      (x : Carrier) →
      Set

    mulComm :
      (x y : Carrier) →
      Set

    mulAssoc :
      (x y z : Carrier) →
      Set

    distL :
      (x y z : Carrier) →
      Set

    mulOneL :
      (x : Carrier) →
      Set

open ScalarFieldLawShape public

record ScalarOrderOrModulusLawShape
  (Carrier : Set)
  (zero : Carrier)
  (_+_ _*_ : Carrier → Carrier → Carrier)
  (abs : Carrier → Carrier)
  (_≤_ _<_ : Carrier → Carrier → Set) :
  Set₁ where
  field
    absNonneg :
      (x : Carrier) →
      Set

    absMul :
      (x y : Carrier) →
      Set

    absTriangle :
      (x y : Carrier) →
      Set

open ScalarOrderOrModulusLawShape public

record ScalarCompletenessLawShape
  (Carrier : Set)
  (_≤_ : Carrier → Carrier → Set) :
  Set₁ where
  field
    cauchyLimit :
      (xs : ℕ → Carrier) →
      ScalarCauchy _≤_ xs →
      Set

open ScalarCompletenessLawShape public

record ScalarAuthoritySocket : Set₁ where
  field
    scalarDiscipline :
      ScalarDiscipline

    scalarCarrier :
      Set

    scalarZero scalarOne :
      scalarCarrier

    scalarAdd scalarMul scalarSub :
      scalarCarrier →
      scalarCarrier →
      scalarCarrier

    scalarNeg scalarAbs :
      scalarCarrier →
      scalarCarrier

    scalarLe scalarLt :
      scalarCarrier →
      scalarCarrier →
      Set

    scalarFieldLawShape :
      ScalarFieldLawShape
        scalarCarrier
        scalarZero
        scalarOne
        scalarAdd
        scalarMul
        scalarSub
        scalarNeg
        scalarAbs

    scalarOrderOrModulusLawShape :
      ScalarOrderOrModulusLawShape
        scalarCarrier
        scalarZero
        scalarAdd
        scalarMul
        scalarAbs
        scalarLe
        scalarLt

    scalarCompletenessLawShape :
      ScalarCompletenessLawShape scalarCarrier scalarLe

    scalarFieldLawsAuthority :
      Set

    scalarOrderOrModulusAuthority :
      Set

    scalarCompletenessAuthority :
      Set

open ScalarAuthoritySocket public

canonicalRealScalarAuthoritySocket :
  ScalarAuthoritySocket
canonicalRealScalarAuthoritySocket =
  record
    { scalarDiscipline =
        realScalars
    ; scalarCarrier =
        ℝ
    ; scalarZero =
        0ℝ
    ; scalarOne =
        1ℝ
    ; scalarAdd =
        _+ℝ_
    ; scalarMul =
        _*ℝ_
    ; scalarSub =
        _-ℝ_
    ; scalarNeg =
        -ℝ_
    ; scalarAbs =
        absℝ
    ; scalarLe =
        _≤ℝ_
    ; scalarLt =
        _<ℝ_
    ; scalarFieldLawShape =
        record
          { addComm =
              λ x y → x +ℝ y ≡ y +ℝ x
          ; addAssoc =
              λ x y z → (x +ℝ y) +ℝ z ≡ x +ℝ (y +ℝ z)
          ; addZeroL =
              λ x → 0ℝ +ℝ x ≡ x
          ; addInvL =
              λ x → (-ℝ x) +ℝ x ≡ 0ℝ
          ; mulComm =
              λ x y → x *ℝ y ≡ y *ℝ x
          ; mulAssoc =
              λ x y z → (x *ℝ y) *ℝ z ≡ x *ℝ (y *ℝ z)
          ; distL =
              λ x y z → x *ℝ (y +ℝ z) ≡ (x *ℝ y) +ℝ (x *ℝ z)
          ; mulOneL =
              λ x → 1ℝ *ℝ x ≡ x
          }
    ; scalarOrderOrModulusLawShape =
        record
          { absNonneg =
              λ x → 0ℝ ≤ℝ absℝ x
          ; absMul =
              λ x y → absℝ (x *ℝ y) ≡ absℝ x *ℝ absℝ y
          ; absTriangle =
              λ x y → absℝ (x +ℝ y) ≤ℝ (absℝ x +ℝ absℝ y)
          }
    ; scalarCompletenessLawShape =
        record
          { cauchyLimit =
              λ xs _ →
                Sigma ℝ (λ limit → ScalarConvergesTo _≤ℝ_ xs limit)
          }
    ; scalarFieldLawsAuthority =
        RealScalarSocket.realFieldLawsAxiom canonicalRealScalarSocket
    ; scalarOrderOrModulusAuthority =
        RealScalarSocket.realOrderLawsAxiom canonicalRealScalarSocket
    ; scalarCompletenessAuthority =
        RealScalarSocket.realCompletenessLawsAxiom canonicalRealScalarSocket
    }

record VectorSpace
  (ℓ : Level)
  (S : ScalarAuthoritySocket) :
  Set (lsuc ℓ) where
  field
    Carrier :
      Set ℓ

    zero :
      Carrier

    _+_ _-_ :
      Carrier →
      Carrier →
      Carrier

    scalarMul :
      ScalarAuthoritySocket.scalarCarrier S →
      Carrier →
      Carrier

    vectorSpaceLawsAuthority :
      Set ℓ

open VectorSpace public

record VectorSpaceEightAxiomShape
  {ℓ : Level}
  (S : ScalarAuthoritySocket)
  (V : VectorSpace ℓ S) :
  Set (lsuc ℓ) where
  field
    vectorAddComm :
      (u v : VectorSpace.Carrier V) →
      VectorSpace._+_ V u v
      ≡
      VectorSpace._+_ V v u

    vectorAddAssoc :
      (u v w : VectorSpace.Carrier V) →
      VectorSpace._+_ V (VectorSpace._+_ V u v) w
      ≡
      VectorSpace._+_ V u (VectorSpace._+_ V v w)

    vectorAddZeroL :
      (v : VectorSpace.Carrier V) →
      VectorSpace._+_ V (VectorSpace.zero V) v ≡ v

    vectorAddInvL :
      (v : VectorSpace.Carrier V) →
      VectorSpace._+_ V
        (VectorSpace._-_ V (VectorSpace.zero V) v)
        v
      ≡
      VectorSpace.zero V

    scalarOneL :
      (v : VectorSpace.Carrier V) →
      VectorSpace.scalarMul V
        (ScalarAuthoritySocket.scalarOne S)
        v
      ≡
      v

    scalarAssoc :
      (a b : ScalarAuthoritySocket.scalarCarrier S) →
      (v : VectorSpace.Carrier V) →
      VectorSpace.scalarMul V
        (ScalarAuthoritySocket.scalarMul S a b)
        v
      ≡
      VectorSpace.scalarMul V a (VectorSpace.scalarMul V b v)

    distVectorAdd :
      (a : ScalarAuthoritySocket.scalarCarrier S) →
      (u v : VectorSpace.Carrier V) →
      VectorSpace.scalarMul V a (VectorSpace._+_ V u v)
      ≡
      VectorSpace._+_ V (VectorSpace.scalarMul V a u) (VectorSpace.scalarMul V a v)

    distScalarAdd :
      (a b : ScalarAuthoritySocket.scalarCarrier S) →
      (v : VectorSpace.Carrier V) →
      VectorSpace.scalarMul V (ScalarAuthoritySocket.scalarAdd S a b) v
      ≡
      VectorSpace._+_ V (VectorSpace.scalarMul V a v) (VectorSpace.scalarMul V b v)

open VectorSpaceEightAxiomShape public

data SizedVec {ℓ : Level} (A : Set ℓ) : ℕ → Set ℓ where
  [] :
    SizedVec A 0

  _∷_ :
    {n : ℕ} →
    A →
    SizedVec A n →
    SizedVec A (suc n)

data Fin : ℕ → Set where
  fzero :
    {n : ℕ} →
    Fin (suc n)

  fsuc :
    {n : ℕ} →
    Fin n →
    Fin (suc n)

lookupSized :
  {ℓ : Level} →
  {A : Set ℓ} →
  {n : ℕ} →
  SizedVec A n →
  Fin n →
  A
lookupSized (x ∷ xs) fzero =
  x
lookupSized (x ∷ xs) (fsuc i) =
  lookupSized xs i

sizedToList :
  {ℓ : Level} →
  {A : Set ℓ} →
  {n : ℕ} →
  SizedVec A n →
  List A
sizedToList [] =
  ListBase.[]
sizedToList (x ∷ xs) =
  ListBase._∷_ x (sizedToList xs)

listLength :
  {ℓ : Level} →
  {A : Set ℓ} →
  List A →
  ℕ
listLength ListBase.[] =
  0
listLength (ListBase._∷_ x xs) =
  suc (listLength xs)

foldr2 :
  {ℓ₁ ℓ₂ ℓ₃ : Level} →
  {A : Set ℓ₁} →
  {B : Set ℓ₂} →
  {C : Set ℓ₃} →
  (A → B → C → C) →
  C →
  List A →
  List B →
  C
foldr2 f z ListBase.[] ys =
  z
foldr2 f z xs ListBase.[] =
  z
foldr2 f z (ListBase._∷_ x xs) (ListBase._∷_ y ys) =
  f x y (foldr2 f z xs ys)

record FiniteDimensionalVectorSpace
  (ℓ : Level)
  (S : ScalarAuthoritySocket) :
  Set (lsuc ℓ) where
  field
    vectorSpace :
      VectorSpace ℓ S

    dimension :
      ℕ

    sizedBasis :
      SizedVec (VectorSpace.Carrier vectorSpace) dimension

    basis :
      List (VectorSpace.Carrier vectorSpace)

    vectorSpaceEightAxioms :
      VectorSpaceEightAxiomShape S vectorSpace

    basisHasDimensionAuthority :
      Set ℓ

    basisSpansAuthority :
      Set ℓ

    basisLinearIndependentAuthority :
      Set ℓ

open FiniteDimensionalVectorSpace public

record FiniteDimensionalBasisShape
  {ℓ : Level}
  {S : ScalarAuthoritySocket}
  (F : FiniteDimensionalVectorSpace ℓ S) :
  Set (lsuc ℓ) where
  field
    length :
      ℕ

    lengthIsDimension :
      length ≡ FiniteDimensionalVectorSpace.dimension F

    basisVector :
      SizedVec
        (VectorSpace.Carrier
          (FiniteDimensionalVectorSpace.vectorSpace F))
        length

    basisVectorIsSocketBasis :
      sizedToList basisVector
      ≡
      FiniteDimensionalVectorSpace.basis F

    basisListLength :
      listLength (FiniteDimensionalVectorSpace.basis F) ≡ length

    spanningCoefficients :
      VectorSpace.Carrier
        (FiniteDimensionalVectorSpace.vectorSpace F) →
      List (ScalarAuthoritySocket.scalarCarrier S)

    spanning :
      (v :
        VectorSpace.Carrier
          (FiniteDimensionalVectorSpace.vectorSpace F)) →
      foldr2
        (λ scalar basisElement accumulator →
          VectorSpace._+_
            (FiniteDimensionalVectorSpace.vectorSpace F)
            (VectorSpace.scalarMul
              (FiniteDimensionalVectorSpace.vectorSpace F)
              scalar
              basisElement)
            accumulator)
        (VectorSpace.zero (FiniteDimensionalVectorSpace.vectorSpace F))
        (spanningCoefficients v)
        (FiniteDimensionalVectorSpace.basis F)
      ≡
      v

    independence :
      (coefficients :
        SizedVec (ScalarAuthoritySocket.scalarCarrier S) length) →
      foldr2
        (λ scalar basisElement accumulator →
          VectorSpace._+_
            (FiniteDimensionalVectorSpace.vectorSpace F)
            (VectorSpace.scalarMul
              (FiniteDimensionalVectorSpace.vectorSpace F)
              scalar
              basisElement)
            accumulator)
        (VectorSpace.zero (FiniteDimensionalVectorSpace.vectorSpace F))
        (sizedToList coefficients)
        (sizedToList basisVector)
      ≡
      VectorSpace.zero (FiniteDimensionalVectorSpace.vectorSpace F) →
      (index : Fin length) →
      lookupSized coefficients index ≡ ScalarAuthoritySocket.scalarZero S

open FiniteDimensionalBasisShape public

record NormedVectorSpace
  (ℓ : Level) :
  Set (lsuc ℓ) where
  field
    normedSpace :
      NormedSpace ℓ

    vectorSpaceOverReals :
      VectorSpace ℓ canonicalRealScalarAuthoritySocket

    normedCarrierMatchesVectorCarrier :
      NormedSpace.Carrier normedSpace
      ≡
      VectorSpace.Carrier vectorSpaceOverReals

    normedOperationsMatchAuthority :
      Set ℓ

    vectorSpaceEightAxioms :
      VectorSpaceEightAxiomShape
        canonicalRealScalarAuthoritySocket
        vectorSpaceOverReals

open NormedVectorSpace public

record InnerProductSpace
  (ℓ : Level) :
  Set (lsuc ℓ) where
  field
    normedVectorSpace :
      NormedVectorSpace ℓ

    innerProduct :
      NormedSpace.Carrier (NormedVectorSpace.normedSpace normedVectorSpace) →
      NormedSpace.Carrier (NormedVectorSpace.normedSpace normedVectorSpace) →
      ℝ

    innerProductLinearityAuthority :
      Set ℓ

    innerProductSymmetryAuthority :
      Set ℓ

    innerProductPositiveDefiniteAuthority :
      Set ℓ

    normInducedByInnerProductAuthority :
      Set ℓ

open InnerProductSpace public

record InnerProductLawShape
  {ℓ : Level}
  (H : InnerProductSpace ℓ) :
  Set (lsuc ℓ) where
  field
    innerAddL :
      (u v w :
        NormedSpace.Carrier
          (NormedVectorSpace.normedSpace
            (InnerProductSpace.normedVectorSpace H))) →
      InnerProductSpace.innerProduct H
        (NormedSpace._+_
          (NormedVectorSpace.normedSpace
            (InnerProductSpace.normedVectorSpace H))
          u
          v)
        w
      ≡
      InnerProductSpace.innerProduct H u w
      +ℝ
      InnerProductSpace.innerProduct H v w

    innerScalarL :
      (a : ℝ) →
      (u v :
        NormedSpace.Carrier
          (NormedVectorSpace.normedSpace
            (InnerProductSpace.normedVectorSpace H))) →
      InnerProductSpace.innerProduct H
        (NormedSpace.scalarMul
          (NormedVectorSpace.normedSpace
            (InnerProductSpace.normedVectorSpace H))
          a
          u)
        v
      ≡
      a *ℝ InnerProductSpace.innerProduct H u v

    innerSym :
      (u v :
        NormedSpace.Carrier
          (NormedVectorSpace.normedSpace
            (InnerProductSpace.normedVectorSpace H))) →
      InnerProductSpace.innerProduct H u v
      ≡
      InnerProductSpace.innerProduct H v u

    innerPositive :
      (v :
        NormedSpace.Carrier
          (NormedVectorSpace.normedSpace
            (InnerProductSpace.normedVectorSpace H))) →
      0ℝ ≤ℝ InnerProductSpace.innerProduct H v v

    innerDefinite :
      (v :
        NormedSpace.Carrier
          (NormedVectorSpace.normedSpace
            (InnerProductSpace.normedVectorSpace H))) →
      InnerProductSpace.innerProduct H v v ≡ 0ℝ →
      v
      ≡
      NormedSpace.zero
        (NormedVectorSpace.normedSpace
          (InnerProductSpace.normedVectorSpace H))

    inducedNorm :
      (v :
        NormedSpace.Carrier
          (NormedVectorSpace.normedSpace
            (InnerProductSpace.normedVectorSpace H))) →
      NormedSpace.‖_‖
        (NormedVectorSpace.normedSpace
          (InnerProductSpace.normedVectorSpace H))
        v
      *ℝ
      NormedSpace.‖_‖
        (NormedVectorSpace.normedSpace
          (InnerProductSpace.normedVectorSpace H))
        v
      ≡
      InnerProductSpace.innerProduct H v v

open InnerProductLawShape public

record HilbertSpace
  (ℓ : Level) :
  Set (lsuc ℓ) where
  field
    innerProductSpace :
      InnerProductSpace ℓ

    banachSpace :
      BanachSpace ℓ

    banachNormedSpaceMatches :
      BanachSpace.normedSpace banachSpace
      ≡
      NormedVectorSpace.normedSpace
        (InnerProductSpace.normedVectorSpace innerProductSpace)

    hilbertCompletenessAuthority :
      Set ℓ

    innerProductLaws :
      InnerProductLawShape innerProductSpace

open HilbertSpace public

record HilbertCompletionLawShape
  {ℓ : Level}
  (H : HilbertSpace ℓ) :
  Set (lsuc ℓ) where
  field
    cauchyCompleteness :
      (xs :
        ℕ →
        NormedSpace.Carrier
          (NormedVectorSpace.normedSpace
            (InnerProductSpace.normedVectorSpace
              (HilbertSpace.innerProductSpace H)))) →
      IsCauchy
        (NormedVectorSpace.normedSpace
          (InnerProductSpace.normedVectorSpace
            (HilbertSpace.innerProductSpace H)))
        xs →
      Sigma
        (NormedSpace.Carrier
          (NormedVectorSpace.normedSpace
            (InnerProductSpace.normedVectorSpace
              (HilbertSpace.innerProductSpace H))))
        (λ limit →
          ConvergesTo
            (NormedVectorSpace.normedSpace
              (InnerProductSpace.normedVectorSpace
                (HilbertSpace.innerProductSpace H)))
            xs
            limit)

    limitPreservesInnerProduct :
      (xs ys :
        ℕ →
        NormedSpace.Carrier
          (NormedVectorSpace.normedSpace
            (InnerProductSpace.normedVectorSpace
              (HilbertSpace.innerProductSpace H)))) →
      (x y :
        NormedSpace.Carrier
          (NormedVectorSpace.normedSpace
            (InnerProductSpace.normedVectorSpace
              (HilbertSpace.innerProductSpace H)))) →
      ConvergesTo
        (NormedVectorSpace.normedSpace
          (InnerProductSpace.normedVectorSpace
            (HilbertSpace.innerProductSpace H)))
        xs
        x →
      ConvergesTo
        (NormedVectorSpace.normedSpace
          (InnerProductSpace.normedVectorSpace
            (HilbertSpace.innerProductSpace H)))
        ys
        y →
      ScalarSequenceConvergesTo
        (λ n →
          InnerProductSpace.innerProduct
            (HilbertSpace.innerProductSpace H)
            (xs n)
            (ys n))
        (InnerProductSpace.innerProduct (HilbertSpace.innerProductSpace H) x y)

    banachCompatibility :
      BanachSpace.normedSpace (HilbertSpace.banachSpace H)
      ≡
      NormedVectorSpace.normedSpace
        (InnerProductSpace.normedVectorSpace
          (HilbertSpace.innerProductSpace H))

    completionAuthorityExternal :
      Set ℓ

open HilbertCompletionLawShape public

postulate
  TensorProductCarrier :
    ∀ {ℓ₁ ℓ₂}
    (V : VectorSpace ℓ₁ canonicalRealScalarAuthoritySocket)
    (W : VectorSpace ℓ₂ canonicalRealScalarAuthoritySocket) →
    Set (ℓ₁ ⊔ ℓ₂)

  tensorPure :
    ∀ {ℓ₁ ℓ₂}
    {V : VectorSpace ℓ₁ canonicalRealScalarAuthoritySocket}
    {W : VectorSpace ℓ₂ canonicalRealScalarAuthoritySocket} →
    VectorSpace.Carrier V →
    VectorSpace.Carrier W →
    TensorProductCarrier V W

record TensorProductSpace
  {ℓ₁ ℓ₂ : Level}
  (V : VectorSpace ℓ₁ canonicalRealScalarAuthoritySocket)
  (W : VectorSpace ℓ₂ canonicalRealScalarAuthoritySocket) :
  Set (lsuc (lsuc (ℓ₁ ⊔ ℓ₂))) where
  field
    tensorCarrier :
      Set (ℓ₁ ⊔ ℓ₂)

    tensorCarrierIsAuthorityCarrier :
      tensorCarrier
      ≡
      TensorProductCarrier V W

    pureTensor :
      VectorSpace.Carrier V →
      VectorSpace.Carrier W →
      tensorCarrier

    tensorBilinearAuthority :
      Set (ℓ₁ ⊔ ℓ₂)

    tensorUniversalPropertyAuthority :
      Set (lsuc (ℓ₁ ⊔ ℓ₂))

open TensorProductSpace public

record AdjointableOperator
  {ℓ : Level}
  (H : InnerProductSpace ℓ) :
  Set (lsuc ℓ) where
  field
    boundedOperator :
      BoundedLinearOperator
        (NormedVectorSpace.normedSpace
          (InnerProductSpace.normedVectorSpace H))
        (NormedVectorSpace.normedSpace
          (InnerProductSpace.normedVectorSpace H))

    adjointOperator :
      BoundedLinearOperator
        (NormedVectorSpace.normedSpace
          (InnerProductSpace.normedVectorSpace H))
        (NormedVectorSpace.normedSpace
          (InnerProductSpace.normedVectorSpace H))

    adjointIdentityAuthority :
      Set ℓ

    adjointExistenceAuthority :
      Set ℓ

open AdjointableOperator public

record OperatorAdjointLawShape
  {ℓ : Level}
  {H : InnerProductSpace ℓ}
  (T : AdjointableOperator H) :
  Set (lsuc ℓ) where
  field
    adjointIdentity :
      (x y :
        NormedSpace.Carrier
          (NormedVectorSpace.normedSpace
            (InnerProductSpace.normedVectorSpace H))) →
      InnerProductSpace.innerProduct H
        (LinearOperator.map
          (BoundedLinearOperator.linearOperator
            (AdjointableOperator.boundedOperator T))
          x)
        y
      ≡
      InnerProductSpace.innerProduct H
        x
        (LinearOperator.map
          (BoundedLinearOperator.linearOperator
            (AdjointableOperator.adjointOperator T))
          y)

    adjointUnique :
      Set ℓ

    adjointBounded :
      Set ℓ

open OperatorAdjointLawShape public

record SelfAdjointOperator
  {ℓ : Level}
  (H : InnerProductSpace ℓ) :
  Set (lsuc ℓ) where
  field
    adjointableOperator :
      AdjointableOperator H

    selfAdjointAuthority :
      AdjointableOperator.adjointOperator adjointableOperator
      ≡
      AdjointableOperator.boundedOperator adjointableOperator

    selfAdjointLawShape :
      OperatorAdjointLawShape adjointableOperator

open SelfAdjointOperator public

record SelfAdjointLawShape
  {ℓ : Level}
  {H : InnerProductSpace ℓ}
  (T : SelfAdjointOperator H) :
  Set (lsuc ℓ) where
  field
    selfAdjointEquation :
      AdjointableOperator.adjointOperator
        (SelfAdjointOperator.adjointableOperator T)
      ≡
      AdjointableOperator.boundedOperator
        (SelfAdjointOperator.adjointableOperator T)

    selfAdjointEquationIsSocketEquation :
      selfAdjointEquation
      ≡
      SelfAdjointOperator.selfAdjointAuthority T

    selfAdjointRealSpectrum :
      Set ℓ

    selfAdjointQuadraticForm :
      Set ℓ

open SelfAdjointLawShape public

record UnitaryOnHilbertSpace
  {ℓ : Level}
  (H : HilbertSpace ℓ) :
  Set (lsuc ℓ) where
  field
    unitaryOperator :
      UnitaryOperator
        (BanachSpace.normedSpace (HilbertSpace.banachSpace H))

    innerProductPreservationAuthority :
      Set ℓ

    inverseEqualsAdjointAuthority :
      Set ℓ

open UnitaryOnHilbertSpace public

record UnitaryLawShape
  {ℓ : Level}
  {H : HilbertSpace ℓ}
  (U : UnitaryOnHilbertSpace H) :
  Set (lsuc ℓ) where
  field
    unitaryPreservesInnerProduct :
      Set ℓ

    unitaryPreservesNorm :
      (x : NormedSpace.Carrier (BanachSpace.normedSpace (HilbertSpace.banachSpace H))) →
      NormedSpace.‖_‖
        (BanachSpace.normedSpace (HilbertSpace.banachSpace H))
        (LinearOperator.map
          (BoundedLinearOperator.linearOperator
            (UnitaryOperator.boundedOperator
              (UnitaryOnHilbertSpace.unitaryOperator U)))
          x)
      ≡
      NormedSpace.‖_‖
        (BanachSpace.normedSpace (HilbertSpace.banachSpace H))
        x

    unitaryInverseIsAdjoint :
      Set ℓ

    unitarySurjectiveIsometry :
      Set ℓ

open UnitaryLawShape public

postulate
  Spectrum :
    ∀ {ℓ}
    {N : NormedSpace ℓ} →
    BoundedLinearOperator N N →
    Set ℓ

  ResolventSet :
    ∀ {ℓ}
    {N : NormedSpace ℓ} →
    BoundedLinearOperator N N →
    Set ℓ

record SpectralTheorySocket
  {ℓ : Level}
  {H : HilbertSpace ℓ}
  (T : SelfAdjointOperator (HilbertSpace.innerProductSpace H)) :
  Set (lsuc (lsuc ℓ)) where
  field
    spectralOperator :
      BoundedLinearOperator
        (BanachSpace.normedSpace (HilbertSpace.banachSpace H))
        (BanachSpace.normedSpace (HilbertSpace.banachSpace H))

    spectralOperatorMatchesInputAuthority :
      Set ℓ

    spectrum :
      Set ℓ

    spectrumIsAuthoritySpectrum :
      spectrum
      ≡
      Spectrum spectralOperator

    resolventSet :
      Set ℓ

    resolventSetIsAuthorityResolventSet :
      resolventSet
      ≡
      ResolventSet spectralOperator

    spectralTheoremAuthority :
      Set (lsuc ℓ)

    functionalCalculusAuthority :
      Set (lsuc ℓ)

    projectionValuedMeasureAuthority :
      Set (lsuc ℓ)

    spectralResolutionAuthority :
      Set (lsuc ℓ)

open SpectralTheorySocket public

record SpectralTheoremShape
  {ℓ : Level}
  {H : HilbertSpace ℓ}
  {T : SelfAdjointOperator (HilbertSpace.innerProductSpace H)}
  (S : SpectralTheorySocket {H = H} T) :
  Set (lsuc (lsuc ℓ)) where
  field
    spectrumDef :
      SpectralTheorySocket.spectrum S
      ≡
      Spectrum (SpectralTheorySocket.spectralOperator S)

    resolventBounded :
      Set ℓ

    spectralMeasurePVM :
      Set (lsuc ℓ)

    spectralTheoremAuthority :
      Set (lsuc ℓ)

    functionalCalculus :
      Set (lsuc ℓ)

open SpectralTheoremShape public

record DifferentialEquationSocket
  {ℓ : Level}
  (stateSpace : NormedSpace ℓ) :
  Set (lsuc ℓ) where
  field
    Time :
      Set

    initialState :
      NormedSpace.Carrier stateSpace

    vectorField :
      Time →
      NormedSpace.Carrier stateSpace →
      NormedSpace.Carrier stateSpace

    solution :
      Time →
      NormedSpace.Carrier stateSpace

    solutionInitialConditionAuthority :
      Set ℓ

    solutionSatisfiesEquationAuthority :
      Set ℓ

    existenceAuthority :
      Set ℓ

    uniquenessAuthority :
      Set ℓ

open DifferentialEquationSocket public

record DifferentialEquationLawShape
  {ℓ : Level}
  {stateSpace : NormedSpace ℓ}
  (D : DifferentialEquationSocket stateSpace) :
  Set (lsuc ℓ) where
  field
    derivativeCarrier :
      Set ℓ

    derivative :
      (DifferentialEquationSocket.Time D →
       NormedSpace.Carrier stateSpace) →
      DifferentialEquationSocket.Time D →
      derivativeCarrier

    vectorFieldRegularityAuthority :
      Set ℓ

    solutionDifferentiabilityAuthority :
      Set ℓ

    odeEquationAuthority :
      Set ℓ

    initialValueProblemAuthority :
      Set ℓ

    localExistenceAuthority :
      Set ℓ

    uniquenessByLipschitzAuthority :
      Set ℓ

    maximalContinuationAuthority :
      Set ℓ

open DifferentialEquationLawShape public

stringListNil :
  {ℓ : Level} →
  {A : Set ℓ} →
  List A
stringListNil =
  ListBase.[]

stringListCons :
  {ℓ : Level} →
  {A : Set ℓ} →
  A →
  List A →
  List A
stringListCons =
  ListBase._∷_

record ParityPayloadRow : Set where
  field
    rowName :
      String

    exactFields :
      List String

    localShapeChecked :
      Bool

    externalProofTheory :
      Bool

    continuumAuthorityPromoted :
      Bool

    continuumAuthorityPromotedIsFalse :
      continuumAuthorityPromoted ≡ false

open ParityPayloadRow public

scalarFieldLawShapePayloadRow :
  ParityPayloadRow
scalarFieldLawShapePayloadRow =
  record
    { rowName =
        "ScalarFieldLawShape"
    ; exactFields =
        stringListCons "addComm"
        (stringListCons "addAssoc"
        (stringListCons "addZeroL"
        (stringListCons "addInvL"
        (stringListCons "mulComm"
        (stringListCons "mulAssoc"
        (stringListCons "distL"
        (stringListCons "mulOneL"
          stringListNil)))))))
    ; localShapeChecked =
        true
    ; externalProofTheory =
        true
    ; continuumAuthorityPromoted =
        false
    ; continuumAuthorityPromotedIsFalse =
        refl
    }

scalarOrderOrModulusLawShapePayloadRow :
  ParityPayloadRow
scalarOrderOrModulusLawShapePayloadRow =
  record
    { rowName =
        "ScalarOrderOrModulusLawShape"
    ; exactFields =
        stringListCons "absNonneg"
        (stringListCons "absMul"
        (stringListCons "absTriangle"
          stringListNil))
    ; localShapeChecked =
        true
    ; externalProofTheory =
        true
    ; continuumAuthorityPromoted =
        false
    ; continuumAuthorityPromotedIsFalse =
        refl
    }

scalarCompletenessLawShapePayloadRow :
  ParityPayloadRow
scalarCompletenessLawShapePayloadRow =
  record
    { rowName =
        "ScalarCompletenessLawShape"
    ; exactFields =
        stringListCons "cauchyLimit"
        (stringListCons "ScalarCauchy -> Sigma limit"
          stringListNil)
    ; localShapeChecked =
        true
    ; externalProofTheory =
        true
    ; continuumAuthorityPromoted =
        false
    ; continuumAuthorityPromotedIsFalse =
        refl
    }

vectorSpaceEightAxiomPayloadRow :
  ParityPayloadRow
vectorSpaceEightAxiomPayloadRow =
  record
    { rowName =
        "VectorSpaceEightAxiomShape"
    ; exactFields =
        stringListCons "vectorAddComm"
        (stringListCons "vectorAddAssoc"
        (stringListCons "vectorAddZeroL"
        (stringListCons "vectorAddInvL"
        (stringListCons "scalarOneL"
        (stringListCons "scalarAssoc"
        (stringListCons "distVectorAdd"
        (stringListCons "distScalarAdd"
          stringListNil)))))))
    ; localShapeChecked =
        true
    ; externalProofTheory =
        false
    ; continuumAuthorityPromoted =
        false
    ; continuumAuthorityPromotedIsFalse =
        refl
    }

finiteDimensionalBasisPayloadRow :
  ParityPayloadRow
finiteDimensionalBasisPayloadRow =
  record
    { rowName =
        "FiniteDimensionalBasisShape"
    ; exactFields =
        stringListCons "length"
        (stringListCons "foldr2 spanning"
        (stringListCons "independence"
        (stringListCons "lookupSized"
        (stringListCons "index"
          stringListNil))))
    ; localShapeChecked =
        true
    ; externalProofTheory =
        false
    ; continuumAuthorityPromoted =
        false
    ; continuumAuthorityPromotedIsFalse =
        refl
    }

innerProductPayloadRow :
  ParityPayloadRow
innerProductPayloadRow =
  record
    { rowName =
        "InnerProductLawShape"
    ; exactFields =
        stringListCons "innerAddL"
        (stringListCons "innerScalarL"
        (stringListCons "innerSym"
        (stringListCons "innerPositive"
        (stringListCons "innerDefinite"
        (stringListCons "inducedNorm"
          stringListNil)))))
    ; localShapeChecked =
        true
    ; externalProofTheory =
        false
    ; continuumAuthorityPromoted =
        false
    ; continuumAuthorityPromotedIsFalse =
        refl
    }

hilbertCompletionPayloadRow :
  ParityPayloadRow
hilbertCompletionPayloadRow =
  record
    { rowName =
        "HilbertCompletionLawShape"
    ; exactFields =
        stringListCons "cauchyCompleteness"
        (stringListCons "limitPreservesInnerProduct"
        (stringListCons "banachCompatibility"
        (stringListCons "completionAuthorityExternal"
          stringListNil)))
    ; localShapeChecked =
        true
    ; externalProofTheory =
        true
    ; continuumAuthorityPromoted =
        false
    ; continuumAuthorityPromotedIsFalse =
        refl
    }

operatorLawPayloadRow :
  ParityPayloadRow
operatorLawPayloadRow =
  record
    { rowName =
        "Operator adjoint/self-adjoint/unitary law shapes"
    ; exactFields =
        stringListCons "adjointIdentity"
        (stringListCons "adjointUnique"
        (stringListCons "adjointBounded"
        (stringListCons "selfAdjointEquation"
        (stringListCons "selfAdjointRealSpectrum"
        (stringListCons "selfAdjointQuadraticForm"
        (stringListCons "unitaryPreservesInnerProduct"
        (stringListCons "unitaryPreservesNorm"
        (stringListCons "unitaryInverseIsAdjoint"
        (stringListCons "unitarySurjectiveIsometry"
          stringListNil)))))))))
    ; localShapeChecked =
        true
    ; externalProofTheory =
        true
    ; continuumAuthorityPromoted =
        false
    ; continuumAuthorityPromotedIsFalse =
        refl
    }

spectralTheoremPayloadRow :
  ParityPayloadRow
spectralTheoremPayloadRow =
  record
    { rowName =
        "SpectralTheoremShape"
    ; exactFields =
        stringListCons "spectrumDef"
        (stringListCons "resolventBounded"
        (stringListCons "spectralMeasurePVM"
        (stringListCons "spectralTheoremAuthority"
        (stringListCons "functionalCalculus"
          stringListNil))))
    ; localShapeChecked =
        true
    ; externalProofTheory =
        true
    ; continuumAuthorityPromoted =
        false
    ; continuumAuthorityPromotedIsFalse =
        refl
    }

record PhysicsLinearAnalysisExactPayloadReceipt : Set₁ where
  field
    rows :
      List ParityPayloadRow

    exactPayloadConsumed :
      Bool

    exactPayloadConsumedIsTrue :
      exactPayloadConsumed ≡ true

    scalarFieldEightFieldsPresent :
      Bool

    scalarFieldEightFieldsPresentIsTrue :
      scalarFieldEightFieldsPresent ≡ true

    scalarOrderThreeFieldsPresent :
      Bool

    scalarOrderThreeFieldsPresentIsTrue :
      scalarOrderThreeFieldsPresent ≡ true

    cauchySigmaLimitShapePresent :
      Bool

    cauchySigmaLimitShapePresentIsTrue :
      cauchySigmaLimitShapePresent ≡ true

    finiteBasisFoldr2LookupIndexPresent :
      Bool

    finiteBasisFoldr2LookupIndexPresentIsTrue :
      finiteBasisFoldr2LookupIndexPresent ≡ true

    spectralFiveFieldsPresent :
      Bool

    spectralFiveFieldsPresentIsTrue :
      spectralFiveFieldsPresent ≡ true

    continuumTheoremAuthorityPromoted :
      Bool

    continuumTheoremAuthorityPromotedIsFalse :
      continuumTheoremAuthorityPromoted ≡ false

open PhysicsLinearAnalysisExactPayloadReceipt public

canonicalPhysicsLinearAnalysisExactPayloadReceipt :
  PhysicsLinearAnalysisExactPayloadReceipt
canonicalPhysicsLinearAnalysisExactPayloadReceipt =
  record
    { rows =
        stringListCons scalarFieldLawShapePayloadRow
        (stringListCons scalarOrderOrModulusLawShapePayloadRow
        (stringListCons scalarCompletenessLawShapePayloadRow
        (stringListCons vectorSpaceEightAxiomPayloadRow
        (stringListCons finiteDimensionalBasisPayloadRow
        (stringListCons innerProductPayloadRow
        (stringListCons hilbertCompletionPayloadRow
        (stringListCons operatorLawPayloadRow
        (stringListCons spectralTheoremPayloadRow
          stringListNil))))))))
    ; exactPayloadConsumed =
        true
    ; exactPayloadConsumedIsTrue =
        refl
    ; scalarFieldEightFieldsPresent =
        true
    ; scalarFieldEightFieldsPresentIsTrue =
        refl
    ; scalarOrderThreeFieldsPresent =
        true
    ; scalarOrderThreeFieldsPresentIsTrue =
        refl
    ; cauchySigmaLimitShapePresent =
        true
    ; cauchySigmaLimitShapePresentIsTrue =
        refl
    ; finiteBasisFoldr2LookupIndexPresent =
        true
    ; finiteBasisFoldr2LookupIndexPresentIsTrue =
        refl
    ; spectralFiveFieldsPresent =
        true
    ; spectralFiveFieldsPresentIsTrue =
        refl
    ; continuumTheoremAuthorityPromoted =
        false
    ; continuumTheoremAuthorityPromotedIsFalse =
        refl
    }

record PhysicsLinearAnalysisParityReceipt : Set₁ where
  field
    usesRealAnalysisAxioms :
      Bool

    realScalarSocketSurfaced :
      Bool

    vectorSpaceSurfaceLocal :
      Bool

    finiteDimensionalSurfaceLocal :
      Bool

    normedSpaceSurfaceReused :
      Bool

    innerProductSurfaceLocal :
      Bool

    banachSpaceSurfaceReused :
      Bool

    hilbertSpaceSurfaceLocal :
      Bool

    tensorProductCarrierExternal :
      Bool

    tensorUniversalPropertyExternal :
      Bool

    boundedOperatorSurfaceReused :
      Bool

    adjointOperatorSurfaceLocal :
      Bool

    selfAdjointSurfaceLocal :
      Bool

    unitaryOperatorSurfaceReused :
      Bool

    spectralTheoryExternal :
      Bool

    differentialEquationSurfaceLocal :
      Bool

    differentialEquationExistenceExternal :
      Bool

    complexScalarsAreExternal :
      Bool

    promotionTokenPresent :
      Bool

    claimsPhysLeanParityComplete :
      Bool

    allExternalAuthorityIsFailClosed :
      Bool

    usesRealAnalysisAxiomsIsTrue :
      usesRealAnalysisAxioms ≡ true

    realScalarSocketSurfacedIsTrue :
      realScalarSocketSurfaced ≡ true

    vectorSpaceSurfaceLocalIsTrue :
      vectorSpaceSurfaceLocal ≡ true

    finiteDimensionalSurfaceLocalIsTrue :
      finiteDimensionalSurfaceLocal ≡ true

    normedSpaceSurfaceReusedIsTrue :
      normedSpaceSurfaceReused ≡ true

    innerProductSurfaceLocalIsTrue :
      innerProductSurfaceLocal ≡ true

    banachSpaceSurfaceReusedIsTrue :
      banachSpaceSurfaceReused ≡ true

    hilbertSpaceSurfaceLocalIsTrue :
      hilbertSpaceSurfaceLocal ≡ true

    tensorProductCarrierExternalIsTrue :
      tensorProductCarrierExternal ≡ true

    tensorUniversalPropertyExternalIsTrue :
      tensorUniversalPropertyExternal ≡ true

    boundedOperatorSurfaceReusedIsTrue :
      boundedOperatorSurfaceReused ≡ true

    adjointOperatorSurfaceLocalIsTrue :
      adjointOperatorSurfaceLocal ≡ true

    selfAdjointSurfaceLocalIsTrue :
      selfAdjointSurfaceLocal ≡ true

    unitaryOperatorSurfaceReusedIsTrue :
      unitaryOperatorSurfaceReused ≡ true

    spectralTheoryExternalIsTrue :
      spectralTheoryExternal ≡ true

    differentialEquationSurfaceLocalIsTrue :
      differentialEquationSurfaceLocal ≡ true

    differentialEquationExistenceExternalIsTrue :
      differentialEquationExistenceExternal ≡ true

    complexScalarsAreExternalIsTrue :
      complexScalarsAreExternal ≡ true

    promotionTokenPresentIsFalse :
      promotionTokenPresent ≡ false

    claimsPhysLeanParityCompleteIsFalse :
      claimsPhysLeanParityComplete ≡ false

    allExternalAuthorityIsFailClosedIsTrue :
      allExternalAuthorityIsFailClosed ≡ true

open PhysicsLinearAnalysisParityReceipt public

canonicalPhysicsLinearAnalysisParityReceipt :
  PhysicsLinearAnalysisParityReceipt
canonicalPhysicsLinearAnalysisParityReceipt =
  record
    { usesRealAnalysisAxioms =
        true
    ; realScalarSocketSurfaced =
        true
    ; vectorSpaceSurfaceLocal =
        true
    ; finiteDimensionalSurfaceLocal =
        true
    ; normedSpaceSurfaceReused =
        true
    ; innerProductSurfaceLocal =
        true
    ; banachSpaceSurfaceReused =
        true
    ; hilbertSpaceSurfaceLocal =
        true
    ; tensorProductCarrierExternal =
        true
    ; tensorUniversalPropertyExternal =
        true
    ; boundedOperatorSurfaceReused =
        true
    ; adjointOperatorSurfaceLocal =
        true
    ; selfAdjointSurfaceLocal =
        true
    ; unitaryOperatorSurfaceReused =
        true
    ; spectralTheoryExternal =
        true
    ; differentialEquationSurfaceLocal =
        true
    ; differentialEquationExistenceExternal =
        true
    ; complexScalarsAreExternal =
        true
    ; promotionTokenPresent =
        false
    ; claimsPhysLeanParityComplete =
        false
    ; allExternalAuthorityIsFailClosed =
        true
    ; usesRealAnalysisAxiomsIsTrue =
        refl
    ; realScalarSocketSurfacedIsTrue =
        refl
    ; vectorSpaceSurfaceLocalIsTrue =
        refl
    ; finiteDimensionalSurfaceLocalIsTrue =
        refl
    ; normedSpaceSurfaceReusedIsTrue =
        refl
    ; innerProductSurfaceLocalIsTrue =
        refl
    ; banachSpaceSurfaceReusedIsTrue =
        refl
    ; hilbertSpaceSurfaceLocalIsTrue =
        refl
    ; tensorProductCarrierExternalIsTrue =
        refl
    ; tensorUniversalPropertyExternalIsTrue =
        refl
    ; boundedOperatorSurfaceReusedIsTrue =
        refl
    ; adjointOperatorSurfaceLocalIsTrue =
        refl
    ; selfAdjointSurfaceLocalIsTrue =
        refl
    ; unitaryOperatorSurfaceReusedIsTrue =
        refl
    ; spectralTheoryExternalIsTrue =
        refl
    ; differentialEquationSurfaceLocalIsTrue =
        refl
    ; differentialEquationExistenceExternalIsTrue =
        refl
    ; complexScalarsAreExternalIsTrue =
        refl
    ; promotionTokenPresentIsFalse =
        refl
    ; claimsPhysLeanParityCompleteIsFalse =
        refl
    ; allExternalAuthorityIsFailClosedIsTrue =
        refl
    }
