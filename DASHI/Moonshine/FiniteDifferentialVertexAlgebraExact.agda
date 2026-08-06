module DASHI.Moonshine.FiniteDifferentialVertexAlgebraExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Victor G. Kac,
-- "Vertex Algebras for Beginners", second edition,
-- University Lecture Series 10, American Mathematical Society, 1998.
-- No DOI is asserted for the cited AMS book edition.
--
-- Richard E. Borcherds,
-- "Vertex algebras, Kac-Moody algebras, and the Monster",
-- Proceedings of the National Academy of Sciences 83 (1986), 3068--3071.
-- DOI: 10.1073/pnas.83.10.3068.
--
-- DASHI CONTRIBUTION
--
-- Prove the finite square-zero differential-algebra construction generically.
-- For a commutative unital algebra with derivation D and D^2=0, define
--
--   a_(-1)b = ab,
--   a_(-2)b = (Da)b,
--   a_n b   = 0 otherwise.
--
-- Vacuum, creation, translation, the derivation law and exact commutation of
-- the degree-one truncated fields follow from the supplied algebra laws.
-- This is the finite nilpotent specialization of the standard commutative
-- differential-algebra vertex construction; unrestricted exponential series
-- and the full formal Jacobi identity remain separate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer.Base using (ℤ; +_; -[1+_])

symmetry : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
symmetry refl = refl

transitivity : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transitivity refl second = second

congruence : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
congruence f refl = refl

congruence₂ : ∀ {A B C : Set} (f : A → B → C)
  {x x' : A} {y y' : B} → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
congruence₂ f refl refl = refl

record SquareZeroDifferentialAlgebra : Set₁ where
  field
    Carrier : Set
    zero one : Carrier
    add multiply : Carrier → Carrier → Carrier
    derivative : Carrier → Carrier

    multiplyAssociative : ∀ first second third →
      multiply (multiply first second) third
      ≡ multiply first (multiply second third)
    multiplyCommutative : ∀ left right →
      multiply left right ≡ multiply right left
    multiplyOneLeft : ∀ value → multiply one value ≡ value
    multiplyOneRight : ∀ value → multiply value one ≡ value
    multiplyZeroLeft : ∀ value → multiply zero value ≡ zero
    multiplyZeroRight : ∀ value → multiply value zero ≡ zero

    derivativeOneZero : derivative one ≡ zero
    derivativeSquareZero : ∀ value →
      derivative (derivative value) ≡ zero
    derivativeLeibniz : ∀ left right →
      derivative (multiply left right)
      ≡ add
          (multiply (derivative left) right)
          (multiply left (derivative right))

open SquareZeroDifferentialAlgebra public

minusOne minusTwo : ℤ
minusOne = -[1+ zero ]
minusTwo = -[1+ suc zero ]

vertexMode :
  (algebra : SquareZeroDifferentialAlgebra) →
  Carrier algebra → ℤ → Carrier algebra → Carrier algebra
vertexMode algebra left (-[1+ zero ]) right =
  multiply algebra left right
vertexMode algebra left (-[1+ suc zero ]) right =
  multiply algebra (derivative algebra left) right
vertexMode algebra left (-[1+ suc (suc distance) ]) right =
  zero algebra
vertexMode algebra left (+ nonnegative) right = zero algebra

vacuumMinusOneIdentity : ∀ algebra value →
  vertexMode algebra (one algebra) minusOne value ≡ value
vacuumMinusOneIdentity algebra value =
  multiplyOneLeft algebra value

vacuumMinusTwoVanishes : ∀ algebra value →
  vertexMode algebra (one algebra) minusTwo value ≡ zero algebra
vacuumMinusTwoVanishes algebra value =
  transitivity
    (congruence
      (λ differentiated → multiply algebra differentiated value)
      (derivativeOneZero algebra))
    (multiplyZeroLeft algebra value)

creationMinusOne : ∀ algebra value →
  vertexMode algebra value minusOne (one algebra) ≡ value
creationMinusOne algebra value = multiplyOneRight algebra value

creationMinusTwo : ∀ algebra value →
  vertexMode algebra value minusTwo (one algebra)
  ≡ derivative algebra value
creationMinusTwo algebra value =
  multiplyOneRight algebra (derivative algebra value)

translationMinusOneToMinusTwo : ∀ algebra value input →
  vertexMode algebra (derivative algebra value) minusOne input
  ≡ vertexMode algebra value minusTwo input
translationMinusOneToMinusTwo algebra value input = refl

translationMinusTwoVanishes : ∀ algebra value input →
  vertexMode algebra (derivative algebra value) minusTwo input
  ≡ zero algebra
translationMinusTwoVanishes algebra value input =
  transitivity
    (congruence
      (λ differentiated → multiply algebra differentiated input)
      (derivativeSquareZero algebra value))
    (multiplyZeroLeft algebra input)

record TruncatedField (algebra : SquareZeroDifferentialAlgebra) : Set where
  constructor truncatedField
  field
    constantCoefficient : Carrier algebra
    linearCoefficient : Carrier algebra

open TruncatedField public

truncatedFieldExtensionality : ∀ {algebra} {left right : TruncatedField algebra} →
  constantCoefficient left ≡ constantCoefficient right →
  linearCoefficient left ≡ linearCoefficient right →
  left ≡ right
truncatedFieldExtensionality
    {left = truncatedField _ _} {right = truncatedField _ _}
    refl refl = refl

vertexField :
  (algebra : SquareZeroDifferentialAlgebra) →
  Carrier algebra → Carrier algebra → TruncatedField algebra
vertexField algebra value input = truncatedField
  (multiply algebra value input)
  (multiply algebra (derivative algebra value) input)

vacuumField : ∀ algebra input →
  vertexField algebra (one algebra) input
  ≡ truncatedField input (zero algebra)
vacuumField algebra input =
  truncatedFieldExtensionality
    (multiplyOneLeft algebra input)
    (vacuumMinusTwoVanishes algebra input)

creationField : ∀ algebra value →
  vertexField algebra value (one algebra)
  ≡ truncatedField value (derivative algebra value)
creationField algebra value =
  truncatedFieldExtensionality
    (creationMinusOne algebra value)
    (creationMinusTwo algebra value)

record BivariateTruncatedField
    (algebra : SquareZeroDifferentialAlgebra) : Set where
  constructor bivariateField
  field
    constantTerm : Carrier algebra
    zCoefficient : Carrier algebra
    wCoefficient : Carrier algebra
    zwCoefficient : Carrier algebra

open BivariateTruncatedField public

bivariateExtensionality :
  ∀ {algebra}
    {left right : BivariateTruncatedField algebra} →
  constantTerm left ≡ constantTerm right →
  zCoefficient left ≡ zCoefficient right →
  wCoefficient left ≡ wCoefficient right →
  zwCoefficient left ≡ zwCoefficient right →
  left ≡ right
bivariateExtensionality
    {left = bivariateField _ _ _ _}
    {right = bivariateField _ _ _ _}
    refl refl refl refl = refl

leftThenRightField :
  (algebra : SquareZeroDifferentialAlgebra) →
  Carrier algebra → Carrier algebra → Carrier algebra →
  BivariateTruncatedField algebra
leftThenRightField algebra a b c = bivariateField
  (multiply algebra a (multiply algebra b c))
  (multiply algebra (derivative algebra a) (multiply algebra b c))
  (multiply algebra a (multiply algebra (derivative algebra b) c))
  (multiply algebra (derivative algebra a)
    (multiply algebra (derivative algebra b) c))

rightThenLeftField :
  (algebra : SquareZeroDifferentialAlgebra) →
  Carrier algebra → Carrier algebra → Carrier algebra →
  BivariateTruncatedField algebra
rightThenLeftField algebra a b c = bivariateField
  (multiply algebra b (multiply algebra a c))
  (multiply algebra b (multiply algebra (derivative algebra a) c))
  (multiply algebra (derivative algebra b) (multiply algebra a c))
  (multiply algebra (derivative algebra b)
    (multiply algebra (derivative algebra a) c))

exchangeFactors : ∀ algebra first second third →
  multiply algebra first (multiply algebra second third)
  ≡ multiply algebra second (multiply algebra first third)
exchangeFactors algebra first second third =
  transitivity
    (symmetry (multiplyAssociative algebra first second third))
    (transitivity
      (congruence
        (λ product → multiply algebra product third)
        (multiplyCommutative algebra first second))
      (multiplyAssociative algebra second first third))

truncatedVertexFieldsCommute : ∀ algebra a b c →
  leftThenRightField algebra a b c
  ≡ rightThenLeftField algebra a b c
truncatedVertexFieldsCommute algebra a b c =
  bivariateExtensionality
    (exchangeFactors algebra a b c)
    (exchangeFactors algebra (derivative algebra a) b c)
    (exchangeFactors algebra a (derivative algebra b) c)
    (exchangeFactors algebra
      (derivative algebra a) (derivative algebra b) c)

record FiniteDifferentialVertexCertificate
    (algebra : SquareZeroDifferentialAlgebra) : Set where
  field
    vacuumIdentity : ∀ value →
      vertexMode algebra (one algebra) minusOne value ≡ value
    vacuumDerivativeModeZero : ∀ value →
      vertexMode algebra (one algebra) minusTwo value ≡ zero algebra
    creationIdentity : ∀ value →
      vertexMode algebra value minusOne (one algebra) ≡ value
    creationDerivative : ∀ value →
      vertexMode algebra value minusTwo (one algebra)
      ≡ derivative algebra value
    translation : ∀ value input →
      vertexMode algebra (derivative algebra value) minusOne input
      ≡ vertexMode algebra value minusTwo input
    translationTruncates : ∀ value input →
      vertexMode algebra (derivative algebra value) minusTwo input
      ≡ zero algebra
    localityZero : ∀ a b c →
      leftThenRightField algebra a b c
      ≡ rightThenLeftField algebra a b c

canonicalFiniteDifferentialVertexCertificate :
  ∀ algebra → FiniteDifferentialVertexCertificate algebra
canonicalFiniteDifferentialVertexCertificate algebra = record
  { vacuumIdentity = vacuumMinusOneIdentity algebra
  ; vacuumDerivativeModeZero = vacuumMinusTwoVanishes algebra
  ; creationIdentity = creationMinusOne algebra
  ; creationDerivative = creationMinusTwo algebra
  ; translation = translationMinusOneToMinusTwo algebra
  ; translationTruncates = translationMinusTwoVanishes algebra
  ; localityZero = truncatedVertexFieldsCommute algebra
  }
