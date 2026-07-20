module DASHI.Geometry.TriadicSpectralGenusOneCurve where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.TriadicEllipticModuliGate as Elliptic

------------------------------------------------------------------------
-- Small logical carriers.

data ⊤ : Set where
  tt : ⊤

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

------------------------------------------------------------------------
-- Exact field with five elements.

data F5 : Set where
  f0 f1 f2 f3 f4 : F5

addF5 : F5 → F5 → F5
addF5 f0 y = y
addF5 f1 f0 = f1
addF5 f1 f1 = f2
addF5 f1 f2 = f3
addF5 f1 f3 = f4
addF5 f1 f4 = f0
addF5 f2 f0 = f2
addF5 f2 f1 = f3
addF5 f2 f2 = f4
addF5 f2 f3 = f0
addF5 f2 f4 = f1
addF5 f3 f0 = f3
addF5 f3 f1 = f4
addF5 f3 f2 = f0
addF5 f3 f3 = f1
addF5 f3 f4 = f2
addF5 f4 f0 = f4
addF5 f4 f1 = f0
addF5 f4 f2 = f1
addF5 f4 f3 = f2
addF5 f4 f4 = f3

mulF5 : F5 → F5 → F5
mulF5 f0 y = f0
mulF5 f1 y = y
mulF5 f2 f0 = f0
mulF5 f2 f1 = f2
mulF5 f2 f2 = f4
mulF5 f2 f3 = f1
mulF5 f2 f4 = f3
mulF5 f3 f0 = f0
mulF5 f3 f1 = f3
mulF5 f3 f2 = f1
mulF5 f3 f3 = f4
mulF5 f3 f4 = f2
mulF5 f4 f0 = f0
mulF5 f4 f1 = f4
mulF5 f4 f2 = f3
mulF5 f4 f3 = f2
mulF5 f4 f4 = f1

negF5 : F5 → F5
negF5 f0 = f0
negF5 f1 = f4
negF5 f2 = f3
negF5 f3 = f2
negF5 f4 = f1

subF5 : F5 → F5 → F5
subF5 x y = addF5 x (negF5 y)

squareF5 : F5 → F5
squareF5 x = mulF5 x x

cubeF5 : F5 → F5
cubeF5 x = mulF5 (mulF5 x x) x

data NonZeroF5 : F5 → Set where
  nonzero1 : NonZeroF5 f1
  nonzero2 : NonZeroF5 f2
  nonzero3 : NonZeroF5 f3
  nonzero4 : NonZeroF5 f4

f5CoefficientRing : Elliptic.EllipticCoefficientRing
f5CoefficientRing =
  record
    { Scalar = F5
    ; zero = f0
    ; one = f1
    ; _+_ = addF5
    ; _*_ = mulF5
    ; four = f4
    ; twentySeven = f2
    ; oneThousandSevenHundredTwentyEight = f3
    ; NonZero = NonZeroF5
    }

------------------------------------------------------------------------
-- Spectral/action source and derived short Weierstrass curve.

record SpectralActionSource : Set where
  constructor spectral-action-source
  field
    quadraticSpectralCoefficient : F5
    constantSpectralCoefficient : F5

open SpectralActionSource public

canonicalSpectralAction : SpectralActionSource
canonicalSpectralAction = spectral-action-source f1 f1

spectralCurve : Elliptic.WeierstrassDatum f5CoefficientRing
spectralCurve = Elliptic.weierstrass-datum f1 f1

deriveSpectralCurve :
  SpectralActionSource → Elliptic.WeierstrassDatum f5CoefficientRing
deriveSpectralCurve source =
  Elliptic.weierstrass-datum
    (quadraticSpectralCoefficient source)
    (constantSpectralCoefficient source)

------------------------------------------------------------------------
-- Affine smoothness of y² = x³ + x + 1.

OnAffineCurve : F5 → F5 → Set
OnAffineCurve x y =
  squareF5 y ≡ addF5 (addF5 (cubeF5 x) x) f1

partialX : F5 → F5
partialX x = negF5 (addF5 (mulF5 f3 (squareF5 x)) f1)

partialY : F5 → F5
partialY y = mulF5 f2 y

AffineSmoothAt : F5 → F5 → Set
AffineSmoothAt x y = NonZeroF5 (partialX x) ⊎ NonZeroF5 (partialY y)

affineSmoothness :
  (x y : F5) →
  OnAffineCurve x y →
  AffineSmoothAt x y
affineSmoothness f0 f0 ()
affineSmoothness f0 f1 refl = inj₁ nonzero4
affineSmoothness f0 f2 ()
affineSmoothness f0 f3 ()
affineSmoothness f0 f4 refl = inj₁ nonzero4
affineSmoothness f1 f0 ()
affineSmoothness f1 f1 ()
affineSmoothness f1 f2 ()
affineSmoothness f1 f3 ()
affineSmoothness f1 f4 ()
affineSmoothness f2 f0 ()
affineSmoothness f2 f1 refl = inj₁ nonzero2
affineSmoothness f2 f2 ()
affineSmoothness f2 f3 ()
affineSmoothness f2 f4 refl = inj₁ nonzero2
affineSmoothness f3 f0 ()
affineSmoothness f3 f1 refl = inj₁ nonzero2
affineSmoothness f3 f2 ()
affineSmoothness f3 f3 ()
affineSmoothness f3 f4 refl = inj₁ nonzero2
affineSmoothness f4 f0 ()
affineSmoothness f4 f1 ()
affineSmoothness f4 f2 refl = inj₁ nonzero1
affineSmoothness f4 f3 refl = inj₁ nonzero1
affineSmoothness f4 f4 ()

------------------------------------------------------------------------
-- Projective point at infinity [0:1:0].

record ProjectivePointF5 : Set where
  constructor projective-point
  field
    X Y Z : F5

open ProjectivePointF5 public

pointAtInfinity : ProjectivePointF5
pointAtInfinity = projective-point f0 f1 f0

homogeneousCurvePolynomial : ProjectivePointF5 → F5
homogeneousCurvePolynomial (projective-point x y z) =
  subF5
    (mulF5 (squareF5 y) z)
    (addF5
      (cubeF5 x)
      (addF5
        (mulF5 x (squareF5 z))
        (cubeF5 z)))

infinityLiesOnCurve : homogeneousCurvePolynomial pointAtInfinity ≡ f0
infinityLiesOnCurve = refl

partialZAtInfinity : F5
partialZAtInfinity = f1

infinitySmooth : NonZeroF5 partialZAtInfinity
infinitySmooth = nonzero1

------------------------------------------------------------------------
-- Concrete smooth plane-cubic/genus-one certificate.

record GenusOnePlaneCubicCertificate
  (curve : Elliptic.WeierstrassDatum f5CoefficientRing) : Set where
  constructor genus-one-plane-cubic
  field
    curveIsCanonical : curve ≡ spectralCurve
    everyAffinePointSmooth :
      (x y : F5) → OnAffineCurve x y → AffineSmoothAt x y
    chosenProjectivePoint : ProjectivePointF5
    chosenPointOnCurve :
      homogeneousCurvePolynomial chosenProjectivePoint ≡ f0
    chosenPointSmooth : NonZeroF5 partialZAtInfinity

open GenusOnePlaneCubicCertificate public

spectralCurveGenusOne : GenusOnePlaneCubicCertificate spectralCurve
spectralCurveGenusOne =
  genus-one-plane-cubic
    refl
    affineSmoothness
    pointAtInfinity
    infinityLiesOnCurve
    infinitySmooth

data ChosenBasePoint
  (curve : Elliptic.WeierstrassDatum f5CoefficientRing) : Set where
  canonicalInfinity : ChosenBasePoint spectralCurve

spectralEllipticOrigin : Elliptic.EllipticOriginGate f5CoefficientRing
spectralEllipticOrigin =
  record
    { SourceObject = SpectralActionSource
    ; source = canonicalSpectralAction
    ; CurvePresentation = Elliptic.WeierstrassDatum f5CoefficientRing
    ; deriveCurve = deriveSpectralCurve
    ; isGenusOne = GenusOnePlaneCubicCertificate
    ; hasChosenBasePoint = ChosenBasePoint
    ; toWeierstrass = λ curve → curve
    ; genusOneReceipt = spectralCurveGenusOne
    ; basePointReceipt = canonicalInfinity
    }

------------------------------------------------------------------------
-- Discriminant and j are computed only after smoothness/nonsingularity.

spectralDiscriminantExact :
  Elliptic.discriminantTerm f5CoefficientRing spectralCurve ≡ f1
spectralDiscriminantExact = refl

spectralJCertificate :
  Elliptic.JInvariantCertificate f5CoefficientRing spectralCurve
spectralJCertificate =
  record
    { nonSingular = nonzero1
    ; jCoordinate = f2
    ; jRelation = refl
    }

spectralEllipticCompression :
  Elliptic.EllipticModuliCompression f5CoefficientRing spectralEllipticOrigin
spectralEllipticCompression =
  record
    { curve = spectralCurve
    ; curveMatchesOrigin = refl
    ; jCertificate = spectralJCertificate
    ; ExtraLevelStructure = ⊤
    ; levelStructure = tt
    ; RawPresentation = SpectralActionSource
    ; encodeToModuli = λ _ → f2
    ; residualLevelData = λ _ → tt
    ; jClassIsQuotientCoordinate = ⊤
    ; reconstructionWithLevelData = ⊤
    }

spectralCurveStatement : String
spectralCurveStatement =
  "The spectral/action coefficients A=1 and B=1 over F5 derive y^2=x^3+x+1; all affine points and the point at infinity are checked smooth, the discriminant term is 1, and only then is the exact j-coordinate 2 constructed."
