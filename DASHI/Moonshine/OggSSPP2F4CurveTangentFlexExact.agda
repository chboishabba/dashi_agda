module DASHI.Moonshine.OggSSPP2F4CurveTangentFlexExact where

------------------------------------------------------------------------
-- F4 SPECIAL FIBRE: ACTUAL TANGENT / FLEX GEOMETRY
--
-- Arithmetic geometry for E/F4 : y²+y=x³.  The F4 arithmetic and eight
-- affine points are imported from the existing independent enumerator.
--
-- At (x,y) the tangent has Y = y + x² (X+x), in characteristic 2.
-- The exact intersection polynomial is (X+x)³:
--
--    (Y²+Y)+X³ = (X+x)³.
--
-- Thus each of the eight affine rational points has intersection
-- multiplicity three with its tangent.  This is a geometric flex receipt,
-- not (yet) a formal elliptic group law, group-scheme identification,
-- level-4 marking, or Monster 3B recognition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact as Curve

open Curve using (F4; _+₄_; _*₄_; square₄; cube₄; yTrace;
                  zero₄; one₄; zeta₄; zetaSquared₄)

-- No division: the partial derivative of y²+y-x³ by y is exactly one.
tangentAt : Curve.AffineF4Point → F4 → F4
tangentAt p X =
  let x = proj₁ (Curve.affineCoordinates p)
      y = proj₂ (Curve.affineCoordinates p)
  in y +₄ (square₄ x *₄ (X +₄ x))

tangentCurveResidual : Curve.AffineF4Point → F4 → F4
tangentCurveResidual p X =
  yTrace (tangentAt p X) +₄ cube₄ X

tangentTripleRoot : Curve.AffineF4Point → F4 → F4
tangentTripleRoot p X =
  let x = proj₁ (Curve.affineCoordinates p)
  in cube₄ (X +₄ x)

-- Eight source points times four independent field values: no numerical
-- count shortcut and no assumption of a formal elliptic group law.
tangentIsTripleIntersection :
  (p : Curve.AffineF4Point) (X : F4) →
  tangentCurveResidual p X ≡ tangentTripleRoot p X
tangentIsTripleIntersection Curve.p00 zero₄ = refl
tangentIsTripleIntersection Curve.p00 one₄ = refl
tangentIsTripleIntersection Curve.p00 zeta₄ = refl
tangentIsTripleIntersection Curve.p00 zetaSquared₄ = refl
tangentIsTripleIntersection Curve.p01 zero₄ = refl
tangentIsTripleIntersection Curve.p01 one₄ = refl
tangentIsTripleIntersection Curve.p01 zeta₄ = refl
tangentIsTripleIntersection Curve.p01 zetaSquared₄ = refl
tangentIsTripleIntersection Curve.p1Zeta zero₄ = refl
tangentIsTripleIntersection Curve.p1Zeta one₄ = refl
tangentIsTripleIntersection Curve.p1Zeta zeta₄ = refl
tangentIsTripleIntersection Curve.p1Zeta zetaSquared₄ = refl
tangentIsTripleIntersection Curve.p1ZetaSquared zero₄ = refl
tangentIsTripleIntersection Curve.p1ZetaSquared one₄ = refl
tangentIsTripleIntersection Curve.p1ZetaSquared zeta₄ = refl
tangentIsTripleIntersection Curve.p1ZetaSquared zetaSquared₄ = refl
tangentIsTripleIntersection Curve.pZetaZeta zero₄ = refl
tangentIsTripleIntersection Curve.pZetaZeta one₄ = refl
tangentIsTripleIntersection Curve.pZetaZeta zeta₄ = refl
tangentIsTripleIntersection Curve.pZetaZeta zetaSquared₄ = refl
tangentIsTripleIntersection Curve.pZetaZetaSquared zero₄ = refl
tangentIsTripleIntersection Curve.pZetaZetaSquared one₄ = refl
tangentIsTripleIntersection Curve.pZetaZetaSquared zeta₄ = refl
tangentIsTripleIntersection Curve.pZetaZetaSquared zetaSquared₄ = refl
tangentIsTripleIntersection Curve.pZetaSquaredZeta zero₄ = refl
tangentIsTripleIntersection Curve.pZetaSquaredZeta one₄ = refl
tangentIsTripleIntersection Curve.pZetaSquaredZeta zeta₄ = refl
tangentIsTripleIntersection Curve.pZetaSquaredZeta zetaSquared₄ = refl
tangentIsTripleIntersection Curve.pZetaSquaredZetaSquared zero₄ = refl
tangentIsTripleIntersection Curve.pZetaSquaredZetaSquared one₄ = refl
tangentIsTripleIntersection Curve.pZetaSquaredZetaSquared zeta₄ = refl
tangentIsTripleIntersection Curve.pZetaSquaredZetaSquared zetaSquared₄ = refl

tangentPassesThroughPoint :
  (p : Curve.AffineF4Point) →
  tangentAt p (proj₁ (Curve.affineCoordinates p))
    ≡ proj₂ (Curve.affineCoordinates p)
tangentPassesThroughPoint Curve.p00 = refl
tangentPassesThroughPoint Curve.p01 = refl
tangentPassesThroughPoint Curve.p1Zeta = refl
tangentPassesThroughPoint Curve.p1ZetaSquared = refl
tangentPassesThroughPoint Curve.pZetaZeta = refl
tangentPassesThroughPoint Curve.pZetaZetaSquared = refl
tangentPassesThroughPoint Curve.pZetaSquaredZeta = refl
tangentPassesThroughPoint Curve.pZetaSquaredZetaSquared = refl

-- The affine inverse for this Weierstrass model is (x,y+1).
negateAffine : Curve.AffineF4Point → Curve.AffineF4Point
negateAffine Curve.p00 = Curve.p01
negateAffine Curve.p01 = Curve.p00
negateAffine Curve.p1Zeta = Curve.p1ZetaSquared
negateAffine Curve.p1ZetaSquared = Curve.p1Zeta
negateAffine Curve.pZetaZeta = Curve.pZetaZetaSquared
negateAffine Curve.pZetaZetaSquared = Curve.pZetaZeta
negateAffine Curve.pZetaSquaredZeta = Curve.pZetaSquaredZetaSquared
negateAffine Curve.pZetaSquaredZetaSquared = Curve.pZetaSquaredZeta

negateAffineCoordinates :
  (p : Curve.AffineF4Point) →
  Curve.affineCoordinates (negateAffine p)
    ≡
    (proj₁ (Curve.affineCoordinates p) ,
     proj₂ (Curve.affineCoordinates p) +₄ one₄)
negateAffineCoordinates Curve.p00 = refl
negateAffineCoordinates Curve.p01 = refl
negateAffineCoordinates Curve.p1Zeta = refl
negateAffineCoordinates Curve.p1ZetaSquared = refl
negateAffineCoordinates Curve.pZetaZeta = refl
negateAffineCoordinates Curve.pZetaZetaSquared = refl
negateAffineCoordinates Curve.pZetaSquaredZeta = refl
negateAffineCoordinates Curve.pZetaSquaredZetaSquared = refl

negateAffineInvolutive :
  (p : Curve.AffineF4Point) →
  negateAffine (negateAffine p) ≡ p
negateAffineInvolutive Curve.p00 = refl
negateAffineInvolutive Curve.p01 = refl
negateAffineInvolutive Curve.p1Zeta = refl
negateAffineInvolutive Curve.p1ZetaSquared = refl
negateAffineInvolutive Curve.pZetaZeta = refl
negateAffineInvolutive Curve.pZetaZetaSquared = refl
negateAffineInvolutive Curve.pZetaSquaredZeta = refl
negateAffineInvolutive Curve.pZetaSquaredZetaSquared = refl

negationCommutesWithFrobenius :
  (p : Curve.AffineF4Point) →
  Curve.frobeniusAffine (negateAffine p)
    ≡ negateAffine (Curve.frobeniusAffine p)
negationCommutesWithFrobenius Curve.p00 = refl
negationCommutesWithFrobenius Curve.p01 = refl
negationCommutesWithFrobenius Curve.p1Zeta = refl
negationCommutesWithFrobenius Curve.p1ZetaSquared = refl
negationCommutesWithFrobenius Curve.pZetaZeta = refl
negationCommutesWithFrobenius Curve.pZetaZetaSquared = refl
negationCommutesWithFrobenius Curve.pZetaSquaredZeta = refl
negationCommutesWithFrobenius Curve.pZetaSquaredZetaSquared = refl

record F4CurveTangentFlexBoundary : Set where
  constructor f4-curve-tangent-flex-boundary
  field
    tangentUsesLiteralF4Arithmetic : Bool
    allEightAffineTangentsHaveTripleIntersection : Bool
    affineNegationIsCoordinateYPlusOne : Bool
    negationCommutesWithArithmeticFrobenius : Bool
    ellipticGroupLawConstructedHere : Bool
    threeTorsionGroupEquivalenceConstructed : Bool
    gammaZeroFourMarkingConstructed : Bool

canonicalF4CurveTangentFlexBoundary : F4CurveTangentFlexBoundary
canonicalF4CurveTangentFlexBoundary =
  f4-curve-tangent-flex-boundary
    true true true true false false false
