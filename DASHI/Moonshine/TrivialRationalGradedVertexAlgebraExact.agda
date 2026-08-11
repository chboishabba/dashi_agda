module DASHI.Moonshine.TrivialRationalGradedVertexAlgebraExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Victor G. Kac,
-- "Vertex Algebras for Beginners", second edition,
-- University Lecture Series 10, American Mathematical Society, 1998.
-- No DOI is asserted for the book edition used here.
--
-- Richard E. Borcherds,
-- "Vertex algebras, Kac-Moody algebras, and the Monster",
-- Proceedings of the National Academy of Sciences 83 (1986), 3068--3071.
-- DOI: 10.1073/pnas.83.10.3068.
--
-- DASHI CONTRIBUTION
--
-- Construct the exact one-dimensional rational commutative vertex-algebra
-- seed.  The only nonzero mode is
--
--   a_(-1) b = a b,
--
-- all other modes vanish, the vacuum is 1, the translation operator is zero,
-- and the conformal vector is zero.  Vacuum, creation, commutativity,
-- associativity of the (-1)-product, vanishing positive modes and zero
-- Virasoro action are proved directly over the rational ring.
--
-- This is a concrete proof-bearing graded vertex-algebra example.  It is not
-- V^natural, has central charge zero, carries no Monster action, and does not
-- establish the full Jacobi identity for a general VOA or any moonshine
-- modularity/genus-zero theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _+_)
import Data.Rational.Tactic.RingSolver as ℚRing

------------------------------------------------------------------------
-- Grading: grade zero is ℚ; every positive grade contains only its zero.
------------------------------------------------------------------------

data TrivialHomogeneous : Nat → Set where
  gradeZero : ℚ → TrivialHomogeneous zero
  positiveGradeZero : ∀ {grade} → TrivialHomogeneous (suc grade)

injectHomogeneous : ∀ {grade} → TrivialHomogeneous grade → ℚ
injectHomogeneous (gradeZero value) = value
injectHomogeneous positiveGradeZero = 0ℚ

vacuum : TrivialHomogeneous zero
vacuum = gradeZero 1ℚ

conformalVector : TrivialHomogeneous (suc (suc zero))
conformalVector = positiveGradeZero

trivialGradeDimension : Nat → Nat
trivialGradeDimension zero = 1
trivialGradeDimension (suc grade) = 0

trivialGradeZeroDimension : trivialGradeDimension zero ≡ 1
trivialGradeZeroDimension = refl

trivialPositiveGradeDimension : ∀ grade →
  trivialGradeDimension (suc grade) ≡ 0
trivialPositiveGradeDimension grade = refl

------------------------------------------------------------------------
-- Exact modes.
------------------------------------------------------------------------

minusOne : ℤ
minusOne = -[1+ zero ]

trivialMode : ℚ → ℤ → ℚ → ℚ
trivialMode left (-[1+ zero ]) right = left * right
trivialMode left (-[1+ suc distance ]) right = 0ℚ
trivialMode left (+ nonnegativeIndex) right = 0ℚ

translationOperator : ℚ → ℚ
translationOperator value = 0ℚ

vacuumMinusOneIdentity : ∀ value →
  trivialMode 1ℚ minusOne value ≡ value
vacuumMinusOneIdentity value = ℚRing.solve-∀ value

vacuumPositiveModesVanish : ∀ index value →
  trivialMode 1ℚ (+ index) value ≡ 0ℚ
vacuumPositiveModesVanish index value = refl

vacuumLowerNegativeModesVanish : ∀ distance value →
  trivialMode 1ℚ (-[1+ suc distance ]) value ≡ 0ℚ
vacuumLowerNegativeModesVanish distance value = refl

creationMinusOne : ∀ value →
  trivialMode value minusOne 1ℚ ≡ value
creationMinusOne value = ℚRing.solve-∀ value

creationPositiveModesVanish : ∀ value index →
  trivialMode value (+ index) 1ℚ ≡ 0ℚ
creationPositiveModesVanish value index = refl

minusOneProductCommutative : ∀ left right →
  trivialMode left minusOne right
  ≡ trivialMode right minusOne left
minusOneProductCommutative left right = ℚRing.solve-∀ left right

minusOneProductAssociative : ∀ first second third →
  trivialMode first minusOne (trivialMode second minusOne third)
  ≡ trivialMode (trivialMode first minusOne second) minusOne third
minusOneProductAssociative first second third =
  ℚRing.solve-∀ first second third

minusOneProductDistributesOverAddition : ∀ multiplier left right →
  trivialMode multiplier minusOne (left + right)
  ≡ trivialMode multiplier minusOne left
    + trivialMode multiplier minusOne right
minusOneProductDistributesOverAddition multiplier left right =
  ℚRing.solve-∀ multiplier left right

translationIsZero : ∀ value → translationOperator value ≡ 0ℚ
translationIsZero value = refl

translationActsAsDerivationOnMinusOneProduct : ∀ left right →
  translationOperator (trivialMode left minusOne right)
  ≡ trivialMode (translationOperator left) minusOne right
    + trivialMode left minusOne (translationOperator right)
translationActsAsDerivationOnMinusOneProduct left right =
  ℚRing.solve-∀ left right

conformalModesVanish : ∀ mode value →
  trivialMode (injectHomogeneous conformalVector) mode value ≡ 0ℚ
conformalModesVanish (+ index) value = refl
conformalModesVanish (-[1+ zero ]) value = ℚRing.solve-∀ value
conformalModesVanish (-[1+ suc distance ]) value = refl

record TrivialRationalVertexAlgebraCertificate : Set where
  field
    vacuumIdentity : ∀ value →
      trivialMode 1ℚ minusOne value ≡ value
    creationIdentity : ∀ value →
      trivialMode value minusOne 1ℚ ≡ value
    positiveVacuumModesZero : ∀ index value →
      trivialMode 1ℚ (+ index) value ≡ 0ℚ
    positiveCreationModesZero : ∀ value index →
      trivialMode value (+ index) 1ℚ ≡ 0ℚ
    commutativeProduct : ∀ left right →
      trivialMode left minusOne right
      ≡ trivialMode right minusOne left
    associativeProduct : ∀ first second third →
      trivialMode first minusOne (trivialMode second minusOne third)
      ≡ trivialMode (trivialMode first minusOne second) minusOne third
    translationDerivation : ∀ left right →
      translationOperator (trivialMode left minusOne right)
      ≡ trivialMode (translationOperator left) minusOne right
        + trivialMode left minusOne (translationOperator right)
    zeroConformalAction : ∀ mode value →
      trivialMode (injectHomogeneous conformalVector) mode value ≡ 0ℚ

trivialRationalVertexAlgebraCertificate :
  TrivialRationalVertexAlgebraCertificate
trivialRationalVertexAlgebraCertificate = record
  { vacuumIdentity = vacuumMinusOneIdentity
  ; creationIdentity = creationMinusOne
  ; positiveVacuumModesZero = vacuumPositiveModesVanish
  ; positiveCreationModesZero = creationPositiveModesVanish
  ; commutativeProduct = minusOneProductCommutative
  ; associativeProduct = minusOneProductAssociative
  ; translationDerivation = translationActsAsDerivationOnMinusOneProduct
  ; zeroConformalAction = conformalModesVanish
  }
