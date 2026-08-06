module DASHI.Moonshine.SquareZeroDifferentialVertexAlgebraExact where

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
-- from
--
--   A = Q + Q x + Q y,
--   (Q x + Q y)^2 = 0,
--   D(x)=y,
--   D(y)=0.
--
-- Thus D(a+bx+cy)=b y.  The derivation is genuinely nonzero, square-zero and
-- Leibniz.  The only nonzero modes are
--
--   a_(-1)b = ab,
--   a_(-2)b = (Da)b.
--
-- Vacuum, creation, translation-mode relations and exact commutation of the
-- truncated fields Y(a,z) and Y(b,w) are proved by rational polynomial
-- identities.  This is not the Heisenberg or Monster VOA.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

record SquareZeroRational : Set where
  constructor squareZero
  field
    scalarPart : ℚ
    xPart : ℚ
    yPart : ℚ

open SquareZeroRational public

squareZeroExtensionality : ∀ {left right} →
  scalarPart left ≡ scalarPart right →
  xPart left ≡ xPart right →
  yPart left ≡ yPart right →
  left ≡ right
squareZeroExtensionality
    {squareZero _ _ _} {squareZero _ _ _} refl refl refl = refl

zeroElement : SquareZeroRational
zeroElement = squareZero 0ℚ 0ℚ 0ℚ

oneElement : SquareZeroRational
oneElement = squareZero 1ℚ 0ℚ 0ℚ

xGenerator : SquareZeroRational
xGenerator = squareZero 0ℚ 1ℚ 0ℚ

yGenerator : SquareZeroRational
yGenerator = squareZero 0ℚ 0ℚ 1ℚ

addElement : SquareZeroRational → SquareZeroRational → SquareZeroRational
addElement (squareZero a b c) (squareZero d e f) =
  squareZero (a + d) (b + e) (c + f)

multiplyElement :
  SquareZeroRational → SquareZeroRational → SquareZeroRational
multiplyElement (squareZero a b c) (squareZero d e f) =
  squareZero
    (a * d)
    (a * e + b * d)
    (a * f + c * d)

derivative : SquareZeroRational → SquareZeroRational
derivative (squareZero a b c) = squareZero 0ℚ 0ℚ b

multiplyAssociative : ∀ first second third →
  multiplyElement (multiplyElement first second) third
  ≡ multiplyElement first (multiplyElement second third)
multiplyAssociative
    (squareZero a b c)
    (squareZero d e f)
    (squareZero g h i) =
  squareZeroExtensionality
    (solve (a ∷ d ∷ g ∷ []))
    (solve (a ∷ b ∷ d ∷ e ∷ g ∷ h ∷ []))
    (solve (a ∷ c ∷ d ∷ f ∷ g ∷ i ∷ []))

multiplyCommutative : ∀ left right →
  multiplyElement left right ≡ multiplyElement right left
multiplyCommutative
    (squareZero a b c) (squareZero d e f) =
  squareZeroExtensionality
    (solve (a ∷ d ∷ []))
    (solve (a ∷ b ∷ d ∷ e ∷ []))
    (solve (a ∷ c ∷ d ∷ f ∷ []))

multiplyOneLeft : ∀ value → multiplyElement oneElement value ≡ value
multiplyOneLeft (squareZero a b c) =
  squareZeroExtensionality
    (solve (a ∷ [])) (solve (b ∷ [])) (solve (c ∷ []))

multiplyOneRight : ∀ value → multiplyElement value oneElement ≡ value
multiplyOneRight (squareZero a b c) =
  squareZeroExtensionality
    (solve (a ∷ [])) (solve (b ∷ [])) (solve (c ∷ []))

multiplyZeroLeft : ∀ value →
  multiplyElement zeroElement value ≡ zeroElement
multiplyZeroLeft (squareZero a b c) =
  squareZeroExtensionality
    (solve (a ∷ [])) (solve (b ∷ [])) (solve (c ∷ []))

nilIdealSquaresToZero : ∀ b c e f →
  multiplyElement
    (squareZero 0ℚ b c)
    (squareZero 0ℚ e f)
  ≡ zeroElement
nilIdealSquaresToZero b c e f =
  squareZeroExtensionality
    (solve (b ∷ c ∷ e ∷ f ∷ []))
    (solve (b ∷ c ∷ e ∷ f ∷ []))
    (solve (b ∷ c ∷ e ∷ f ∷ []))

derivativeOnX : derivative xGenerator ≡ yGenerator
derivativeOnX = refl

derivativeOnY : derivative yGenerator ≡ zeroElement
derivativeOnY = refl

derivativeSquareZero : ∀ value →
  derivative (derivative value) ≡ zeroElement
derivativeSquareZero (squareZero a b c) = refl

derivativeOneZero : derivative oneElement ≡ zeroElement
derivativeOneZero = refl

derivativeLeibniz : ∀ left right →
  derivative (multiplyElement left right)
  ≡ addElement
      (multiplyElement (derivative left) right)
      (multiplyElement left (derivative right))
derivativeLeibniz
    (squareZero a b c) (squareZero d e f) =
  squareZeroExtensionality
    (solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []))
    (solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []))
    (solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []))

minusOne minusTwo : ℤ
minusOne = -[1+ zero ]
minusTwo = -[1+ suc zero ]

vertexMode :
  SquareZeroRational → ℤ → SquareZeroRational → SquareZeroRational
vertexMode left (-[1+ zero ]) right = multiplyElement left right
vertexMode left (-[1+ suc zero ]) right =
  multiplyElement (derivative left) right
vertexMode left (-[1+ suc (suc distance) ]) right = zeroElement
vertexMode left (+ nonnegative) right = zeroElement

vacuumMinusOneIdentity : ∀ value →
  vertexMode oneElement minusOne value ≡ value
vacuumMinusOneIdentity = multiplyOneLeft

vacuumMinusTwoVanishes : ∀ value →
  vertexMode oneElement minusTwo value ≡ zeroElement
vacuumMinusTwoVanishes value = multiplyZeroLeft value

creationMinusOne : ∀ value →
  vertexMode value minusOne oneElement ≡ value
creationMinusOne = multiplyOneRight

creationMinusTwo : ∀ value →
  vertexMode value minusTwo oneElement ≡ derivative value
creationMinusTwo value = multiplyOneRight (derivative value)

translationMinusOneToMinusTwo : ∀ value input →
  vertexMode (derivative value) minusOne input
  ≡ vertexMode value minusTwo input
translationMinusOneToMinusTwo value input = refl

translationMinusTwoVanishes : ∀ value input →
  vertexMode (derivative value) minusTwo input ≡ zeroElement
translationMinusTwoVanishes value input
    with derivativeSquareZero value
... | derivativeSquaredZero =
  transitivity
    (multiplyCongruence derivativeSquaredZero refl)
    (multiplyZeroLeft input)
  where
    transitivity : ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    transitivity refl second = second

    multiplyCongruence : ∀ {a a' b b'} →
      a ≡ a' → b ≡ b' →
      multiplyElement a b ≡ multiplyElement a' b'
    multiplyCongruence refl refl = refl

record TruncatedField : Set where
  constructor truncatedField
  field
    constantCoefficient : SquareZeroRational
    linearCoefficient : SquareZeroRational

open TruncatedField public

truncatedFieldExtensionality : ∀ {left right} →
  constantCoefficient left ≡ constantCoefficient right →
  linearCoefficient left ≡ linearCoefficient right →
  left ≡ right
truncatedFieldExtensionality
    {truncatedField _ _} {truncatedField _ _} refl refl = refl

vertexField : SquareZeroRational → SquareZeroRational → TruncatedField
vertexField value input =
  truncatedField
    (multiplyElement value input)
    (multiplyElement (derivative value) input)

vacuumField : ∀ input →
  vertexField oneElement input ≡ truncatedField input zeroElement
vacuumField input =
  truncatedFieldExtensionality
    (multiplyOneLeft input)
    (vacuumMinusTwoVanishes input)

creationField : ∀ value →
  vertexField value oneElement
  ≡ truncatedField value (derivative value)
creationField value =
  truncatedFieldExtensionality
    (creationMinusOne value)
    (creationMinusTwo value)

record BivariateTruncatedField : Set where
  constructor bivariateField
  field
    constantTerm : SquareZeroRational
    zCoefficient : SquareZeroRational
    wCoefficient : SquareZeroRational
    zwCoefficient : SquareZeroRational

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
  SquareZeroRational → SquareZeroRational → SquareZeroRational →
  BivariateTruncatedField
leftThenRightField a b c = bivariateField
  (multiplyElement a (multiplyElement b c))
  (multiplyElement (derivative a) (multiplyElement b c))
  (multiplyElement a (multiplyElement (derivative b) c))
  (multiplyElement (derivative a)
    (multiplyElement (derivative b) c))

rightThenLeftField :
  SquareZeroRational → SquareZeroRational → SquareZeroRational →
  BivariateTruncatedField
rightThenLeftField a b c = bivariateField
  (multiplyElement b (multiplyElement a c))
  (multiplyElement b (multiplyElement (derivative a) c))
  (multiplyElement (derivative b) (multiplyElement a c))
  (multiplyElement (derivative b)
    (multiplyElement (derivative a) c))

truncatedVertexFieldsCommute : ∀ a b c →
  leftThenRightField a b c ≡ rightThenLeftField a b c
truncatedVertexFieldsCommute
    (squareZero a ax ay)
    (squareZero b bx by)
    (squareZero c cx cy) =
  bivariateExtensionality
    (squareZeroExtensionality
      (solve (a ∷ b ∷ c ∷ []))
      (solve (a ∷ ax ∷ b ∷ bx ∷ c ∷ cx ∷ []))
      (solve (a ∷ ay ∷ b ∷ by ∷ c ∷ cy ∷ [])))
    (squareZeroExtensionality
      (solve (a ∷ ax ∷ b ∷ c ∷ []))
      (solve (a ∷ ax ∷ b ∷ bx ∷ c ∷ cx ∷ []))
      (solve (a ∷ ax ∷ ay ∷ b ∷ by ∷ c ∷ cy ∷ [])))
    (squareZeroExtensionality
      (solve (a ∷ b ∷ bx ∷ c ∷ []))
      (solve (a ∷ ax ∷ b ∷ bx ∷ c ∷ cx ∷ []))
      (solve (a ∷ ay ∷ b ∷ bx ∷ by ∷ c ∷ cy ∷ [])))
    (squareZeroExtensionality
      (solve (ax ∷ bx ∷ c ∷ []))
      (solve (ax ∷ bx ∷ cx ∷ []))
      (solve (ax ∷ bx ∷ cy ∷ [])))

record SquareZeroVertexCertificate : Set where
  field
    nontrivialDifferential : derivative xGenerator ≡ yGenerator
    derivationSquaredZero : ∀ value →
      derivative (derivative value) ≡ zeroElement
    leibniz : ∀ left right →
      derivative (multiplyElement left right)
      ≡ addElement
          (multiplyElement (derivative left) right)
          (multiplyElement left (derivative right))
    vacuumIdentity : ∀ value →
      vertexMode oneElement minusOne value ≡ value
    creationIdentity : ∀ value →
      vertexMode value minusOne oneElement ≡ value
    translationMode : ∀ value input →
      vertexMode (derivative value) minusOne input
      ≡ vertexMode value minusTwo input
    localityZero : ∀ a b c →
      leftThenRightField a b c ≡ rightThenLeftField a b c

canonicalSquareZeroVertexCertificate : SquareZeroVertexCertificate
canonicalSquareZeroVertexCertificate = record
  { nontrivialDifferential = derivativeOnX
  ; derivationSquaredZero = derivativeSquareZero
  ; leibniz = derivativeLeibniz
  ; vacuumIdentity = vacuumMinusOneIdentity
  ; creationIdentity = creationMinusOne
  ; translationMode = translationMinusOneToMinusTwo
  ; localityZero = truncatedVertexFieldsCommute
  }
