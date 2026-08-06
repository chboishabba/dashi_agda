module DASHI.Moonshine.DualNumberDifferentialVertexAlgebraExact where

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
-- Construct a nontrivial finite commutative differential vertex-algebra seed
-- from the rational dual numbers Q[epsilon]/(epsilon^2).  The derivation
--
--   D(a+b epsilon) = b epsilon
--
-- is proved square-zero and Leibniz.  The only nonzero modes are
--
--   a_(-1)b = ab,
--   a_(-2)b = (Da)b.
--
-- Vacuum, creation, translation-mode relations and exact commutation of the
-- truncated fields Y(a,z) and Y(b,w) are proved by rational polynomial
-- identities.  This is strictly stronger than the prior zero-derivation
-- one-dimensional example, but it is not the Heisenberg or Monster VOA.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

record DualRational : Set where
  constructor dual
  field
    scalarPart : ℚ
    infinitesimalPart : ℚ

open DualRational public

dualExtensionality : ∀ {left right} →
  scalarPart left ≡ scalarPart right →
  infinitesimalPart left ≡ infinitesimalPart right →
  left ≡ right
dualExtensionality {dual _ _} {dual _ _} refl refl = refl

zeroDual : DualRational
zeroDual = dual 0ℚ 0ℚ

oneDual : DualRational
oneDual = dual 1ℚ 0ℚ

addDual : DualRational → DualRational → DualRational
addDual (dual a b) (dual c d) = dual (a + c) (b + d)

multiplyDual : DualRational → DualRational → DualRational
multiplyDual (dual a b) (dual c d) =
  dual (a * c) (a * d + b * c)

derivative : DualRational → DualRational
derivative (dual a b) = dual 0ℚ b

multiplyAssociative : ∀ x y z →
  multiplyDual (multiplyDual x y) z
  ≡ multiplyDual x (multiplyDual y z)
multiplyAssociative (dual a b) (dual c d) (dual e f) =
  dualExtensionality
    (solve (a ∷ c ∷ e ∷ []))
    (solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []))

multiplyCommutative : ∀ x y →
  multiplyDual x y ≡ multiplyDual y x
multiplyCommutative (dual a b) (dual c d) =
  dualExtensionality
    (solve (a ∷ c ∷ []))
    (solve (a ∷ b ∷ c ∷ d ∷ []))

multiplyOneRight : ∀ x → multiplyDual x oneDual ≡ x
multiplyOneRight (dual a b) =
  dualExtensionality (solve (a ∷ [])) (solve (b ∷ []))

multiplyOneLeft : ∀ x → multiplyDual oneDual x ≡ x
multiplyOneLeft (dual a b) =
  dualExtensionality (solve (a ∷ [])) (solve (b ∷ []))

multiplyZeroRight : ∀ x → multiplyDual x zeroDual ≡ zeroDual
multiplyZeroRight (dual a b) =
  dualExtensionality (solve (a ∷ [])) (solve (b ∷ []))

derivativeSquareZero : ∀ x → derivative (derivative x) ≡ zeroDual
derivativeSquareZero (dual a b) = refl

derivativeOneZero : derivative oneDual ≡ zeroDual
derivativeOneZero = refl

derivativeLeibniz : ∀ x y →
  derivative (multiplyDual x y)
  ≡ addDual
      (multiplyDual (derivative x) y)
      (multiplyDual x (derivative y))
derivativeLeibniz (dual a b) (dual c d) =
  dualExtensionality
    refl
    (solve (a ∷ b ∷ c ∷ d ∷ []))

minusOne minusTwo : ℤ
minusOne = -[1+ zero ]
minusTwo = -[1+ suc zero ]

vertexMode : DualRational → ℤ → DualRational → DualRational
vertexMode left (-[1+ zero ]) right = multiplyDual left right
vertexMode left (-[1+ suc zero ]) right =
  multiplyDual (derivative left) right
vertexMode left (-[1+ suc (suc distance) ]) right = zeroDual
vertexMode left (+ nonnegative) right = zeroDual

vacuumMinusOneIdentity : ∀ value →
  vertexMode oneDual minusOne value ≡ value
vacuumMinusOneIdentity = multiplyOneLeft

vacuumMinusTwoVanishes : ∀ value →
  vertexMode oneDual minusTwo value ≡ zeroDual
vacuumMinusTwoVanishes value = refl

creationMinusOne : ∀ value →
  vertexMode value minusOne oneDual ≡ value
creationMinusOne = multiplyOneRight

creationMinusTwo : ∀ value →
  vertexMode value minusTwo oneDual ≡ derivative value
creationMinusTwo value =
  multiplyOneRight (derivative value)

translationMinusOneToMinusTwo : ∀ value input →
  vertexMode (derivative value) minusOne input
  ≡ vertexMode value minusTwo input
translationMinusOneToMinusTwo value input = refl

translationMinusTwoVanishes : ∀ value input →
  vertexMode (derivative value) minusTwo input ≡ zeroDual
translationMinusTwoVanishes value input =
  transEquality
    (congruenceMultiply
      (derivativeSquareZero value) refl)
    (multiplyZeroLeft input)
  where
    transEquality : ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    transEquality refl second = second

    congruenceMultiply : ∀ {a a' b b'} →
      a ≡ a' → b ≡ b' →
      multiplyDual a b ≡ multiplyDual a' b'
    congruenceMultiply refl refl = refl

    multiplyZeroLeft : ∀ x → multiplyDual zeroDual x ≡ zeroDual
    multiplyZeroLeft (dual a b) =
      dualExtensionality (solve (a ∷ [])) (solve (b ∷ []))

record TruncatedField : Set where
  constructor truncatedField
  field
    constantCoefficient : DualRational
    linearCoefficient : DualRational

open TruncatedField public

vertexField : DualRational → DualRational → TruncatedField
vertexField value input =
  truncatedField
    (multiplyDual value input)
    (multiplyDual (derivative value) input)

vacuumField : ∀ input →
  vertexField oneDual input ≡ truncatedField input zeroDual
vacuumField input =
  fieldExtensionality
    (multiplyOneLeft input)
    (vacuumMinusTwoVanishes input)
  where
    fieldExtensionality : ∀ {left right} →
      constantCoefficient left ≡ constantCoefficient right →
      linearCoefficient left ≡ linearCoefficient right →
      left ≡ right
    fieldExtensionality {truncatedField _ _} {truncatedField _ _}
      refl refl = refl

creationField : ∀ value →
  vertexField value oneDual ≡ truncatedField value (derivative value)
creationField value =
  fieldExtensionality
    (creationMinusOne value)
    (creationMinusTwo value)
  where
    fieldExtensionality : ∀ {left right} →
      constantCoefficient left ≡ constantCoefficient right →
      linearCoefficient left ≡ linearCoefficient right →
      left ≡ right
    fieldExtensionality {truncatedField _ _} {truncatedField _ _}
      refl refl = refl

record BivariateTruncatedField : Set where
  constructor bivariateField
  field
    constantTerm : DualRational
    zCoefficient : DualRational
    wCoefficient : DualRational
    zwCoefficient : DualRational

open BivariateTruncatedField public

bivariateExtensionality : ∀ {left right} →
  constantTerm left ≡ constantTerm right →
  zCoefficient left ≡ zCoefficient right →
  wCoefficient left ≡ wCoefficient right →
  zwCoefficient left ≡ zwCoefficient right →
  left ≡ right
bivariateExtensionality
    {bivariateField _ _ _ _} {bivariateField _ _ _ _}
    refl refl refl refl = refl

leftThenRightField :
  DualRational → DualRational → DualRational →
  BivariateTruncatedField
leftThenRightField a b c = bivariateField
  (multiplyDual a (multiplyDual b c))
  (multiplyDual (derivative a) (multiplyDual b c))
  (multiplyDual a (multiplyDual (derivative b) c))
  (multiplyDual (derivative a)
    (multiplyDual (derivative b) c))

rightThenLeftField :
  DualRational → DualRational → DualRational →
  BivariateTruncatedField
rightThenLeftField a b c = bivariateField
  (multiplyDual b (multiplyDual a c))
  (multiplyDual b (multiplyDual (derivative a) c))
  (multiplyDual (derivative b) (multiplyDual a c))
  (multiplyDual (derivative b)
    (multiplyDual (derivative a) c))

truncatedVertexFieldsCommute : ∀ a b c →
  leftThenRightField a b c ≡ rightThenLeftField a b c
truncatedVertexFieldsCommute
    (dual a aε) (dual b bε) (dual c cε) =
  bivariateExtensionality
    (dualExtensionality
      (solve (a ∷ b ∷ c ∷ []))
      (solve (a ∷ aε ∷ b ∷ bε ∷ c ∷ cε ∷ [])))
    (dualExtensionality
      (solve (a ∷ aε ∷ b ∷ c ∷ []))
      (solve (a ∷ aε ∷ b ∷ bε ∷ c ∷ cε ∷ [])))
    (dualExtensionality
      (solve (a ∷ b ∷ bε ∷ c ∷ []))
      (solve (a ∷ aε ∷ b ∷ bε ∷ c ∷ cε ∷ [])))
    (dualExtensionality
      (solve (aε ∷ bε ∷ c ∷ []))
      (solve (a ∷ aε ∷ b ∷ bε ∷ c ∷ cε ∷ [])))

record DualNumberVertexCertificate : Set where
  field
    derivationSquaredZero : ∀ x → derivative (derivative x) ≡ zeroDual
    leibniz : ∀ x y →
      derivative (multiplyDual x y)
      ≡ addDual
          (multiplyDual (derivative x) y)
          (multiplyDual x (derivative y))
    vacuumIdentity : ∀ value →
      vertexMode oneDual minusOne value ≡ value
    creationIdentity : ∀ value →
      vertexMode value minusOne oneDual ≡ value
    translationMode : ∀ value input →
      vertexMode (derivative value) minusOne input
      ≡ vertexMode value minusTwo input
    localityZero : ∀ a b c →
      leftThenRightField a b c ≡ rightThenLeftField a b c

canonicalDualNumberVertexCertificate : DualNumberVertexCertificate
canonicalDualNumberVertexCertificate = record
  { derivationSquaredZero = derivativeSquareZero
  ; leibniz = derivativeLeibniz
  ; vacuumIdentity = vacuumMinusOneIdentity
  ; creationIdentity = creationMinusOne
  ; translationMode = translationMinusOneToMinusTwo
  ; localityZero = truncatedVertexFieldsCommute
  }
