module DASHI.Geometry.TriadicEllipticModuliGate where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Minimal coefficient ring interface for a division-free j relation.

record EllipticCoefficientRing : Set₁ where
  field
    Scalar : Set
    zero : Scalar
    one : Scalar
    _+_ : Scalar → Scalar → Scalar
    _*_ : Scalar → Scalar → Scalar

    four : Scalar
    twentySeven : Scalar
    oneThousandSevenHundredTwentyEight : Scalar

    NonZero : Scalar → Set

open EllipticCoefficientRing public

square :
  (R : EllipticCoefficientRing) →
  Scalar R →
  Scalar R
square R x = _*_ R x x

cube :
  (R : EllipticCoefficientRing) →
  Scalar R →
  Scalar R
cube R x = _*_ R (_*_ R x x) x

------------------------------------------------------------------------
-- Short Weierstrass data y^2 = x^3 + A x + B.

record WeierstrassDatum (R : EllipticCoefficientRing) : Set where
  constructor weierstrass-datum
  field
    A : Scalar R
    B : Scalar R

open WeierstrassDatum public

cubicAContribution :
  (R : EllipticCoefficientRing) →
  WeierstrassDatum R →
  Scalar R
cubicAContribution R E = _*_ R (four R) (cube R (A E))

cubicBContribution :
  (R : EllipticCoefficientRing) →
  WeierstrassDatum R →
  Scalar R
cubicBContribution R E = _*_ R (twentySeven R) (square R (B E))

discriminantTerm :
  (R : EllipticCoefficientRing) →
  WeierstrassDatum R →
  Scalar R
discriminantTerm R E =
  _+_ R
    (cubicAContribution R E)
    (cubicBContribution R E)

------------------------------------------------------------------------
-- The j-coordinate is stated without division:
--
--   discriminantTerm(E) * j(E) = 1728 * 4 A^3.
--
-- An instance may recover the usual quotient when inversion is available.

record JInvariantCertificate
  (R : EllipticCoefficientRing)
  (E : WeierstrassDatum R) : Set where
  field
    nonSingular : NonZero R (discriminantTerm R E)
    jCoordinate : Scalar R

    jRelation :
      _*_ R (discriminantTerm R E) jCoordinate
      ≡ _*_ R
          (oneThousandSevenHundredTwentyEight R)
          (cubicAContribution R E)

open JInvariantCertificate public

------------------------------------------------------------------------
-- The elliptic object must be derived before the j quotient is meaningful.

record EllipticOriginGate (R : EllipticCoefficientRing) : Set₁ where
  field
    SourceObject : Set
    source : SourceObject

    CurvePresentation : Set
    deriveCurve : SourceObject → CurvePresentation

    isGenusOne : CurvePresentation → Set
    hasChosenBasePoint : CurvePresentation → Set

    toWeierstrass : CurvePresentation → WeierstrassDatum R

    genusOneReceipt : isGenusOne (deriveCurve source)
    basePointReceipt : hasChosenBasePoint (deriveCurve source)

open EllipticOriginGate public

record CoordinateChangeInvariantGate
  (R : EllipticCoefficientRing) : Set₁ where
  field
    Change : Set
    actOnCurve :
      Change →
      WeierstrassDatum R →
      WeierstrassDatum R

    admissibleChange : Change → Set

    jIsInvariant :
      (g : Change) →
      (E : WeierstrassDatum R) →
      admissibleChange g →
      JInvariantCertificate R E →
      JInvariantCertificate R (actOnCurve g E) →
      jCoordinate
        (recordJAfter g E)
      ≡ jCoordinate
          (recordJBefore g E)
      where
        recordJBefore :
          (g : Change) →
          (E : WeierstrassDatum R) →
          JInvariantCertificate R E
        recordJBefore g E = λ where

        recordJAfter :
          (g : Change) →
          (E : WeierstrassDatum R) →
          JInvariantCertificate R (actOnCurve g E)
        recordJAfter g E = λ where

------------------------------------------------------------------------
-- The previous fully generic invariance statement cannot manufacture the two
-- certificates it compares.  This explicit receipt is the usable form.

record JOrbitReceipt
  (R : EllipticCoefficientRing)
  (E E′ : WeierstrassDatum R) : Set where
  field
    firstJ : JInvariantCertificate R E
    secondJ : JInvariantCertificate R E′
    sameOrbit : Set
    jCoordinatesAgree :
      jCoordinate firstJ ≡ jCoordinate secondJ

open JOrbitReceipt public

record EllipticModuliCompression
  (R : EllipticCoefficientRing)
  (O : EllipticOriginGate R) : Set₁ where
  field
    curve : WeierstrassDatum R
    curveMatchesOrigin :
      curve ≡ toWeierstrass O (deriveCurve O (source O))

    jCertificate : JInvariantCertificate R curve

    ExtraLevelStructure : Set
    levelStructure : ExtraLevelStructure

    RawPresentation : Set
    encodeToModuli : RawPresentation → Scalar R
    residualLevelData : RawPresentation → ExtraLevelStructure

    jClassIsQuotientCoordinate : Set
    reconstructionWithLevelData : Set

open EllipticModuliCompression public

------------------------------------------------------------------------
-- Promotion boundary.

jInvariantStatement : String
jInvariantStatement =
  "The j-coordinate is a quotient coordinate only for an associated nonsingular genus-one object. The relation is carried division-free so finite, real, complex, and p-adic coefficient instances can share the same interface."

jInvariantBoundary : String
jInvariantBoundary =
  "No raw balanced-ternary stream or p-adic integer acquires a j-invariant merely by encoding it. EllipticOriginGate, nonsingularity, and coordinate-change invariance must be supplied first; j alone may also require retained level structure for reconstruction."
