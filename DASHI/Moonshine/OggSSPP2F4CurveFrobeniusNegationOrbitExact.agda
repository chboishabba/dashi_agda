module DASHI.Moonshine.OggSSPP2F4CurveFrobeniusNegationOrbitExact where

------------------------------------------------------------------------
-- F4 CURVE: FROBENIUS x COORDINATE NEGATION ORBITS
--
-- Arithmetic donor:
--   E(F4), its arithmetic square Frobenius and coordinate negation
--   (x,y) -> (x,y+1).
--
-- These are two commuting involutions on the actual nine curve points,
-- with four joint orbits of sizes 1, 2, 2, and 4.
--
-- This is an honest arithmetic C2 x C2 SET-ACTION computation, not an
-- elliptic group-law construction or the exceptional Monster p=2 residual
-- groupoid (whose required component count is ten).
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact as Curve
import DASHI.Moonshine.OggSSPP2F4CurveTangentFlexExact as Flex
import DASHI.Moonshine.OggSSPP2F4CurveSheet9FrobeniusBidiExact as Sheet
import DASHI.Codec.TriadicPAdicCodec as Codec

negateRational : Curve.RationalF4Point → Curve.RationalF4Point
negateRational Curve.infinity = Curve.infinity
negateRational (Curve.affine p) = Curve.affine (Flex.negateAffine p)

negateRationalInvolutive :
  (p : Curve.RationalF4Point) →
  negateRational (negateRational p) ≡ p
negateRationalInvolutive Curve.infinity = refl
negateRationalInvolutive (Curve.affine p)
  rewrite Flex.negateAffineInvolutive p = refl

frobeniusNegationCommute :
  (p : Curve.RationalF4Point) →
  Curve.frobeniusRational (negateRational p)
    ≡ negateRational (Curve.frobeniusRational p)
frobeniusNegationCommute Curve.infinity = refl
frobeniusNegationCommute (Curve.affine p)
  rewrite Flex.negationCommutesWithFrobenius p = refl

-- Four joint orbits, as distinct from the six Frobenius-only orbits.
data CurveKleinOrbit : Set where
  infinitySingleton : CurveKleinOrbit
  zeroXPair : CurveKleinOrbit
  unitXPair : CurveKleinOrbit
  primitiveXFour : CurveKleinOrbit

kleinOrbit : Curve.RationalF4Point → CurveKleinOrbit
kleinOrbit Curve.infinity = infinitySingleton
kleinOrbit (Curve.affine Curve.p00) = zeroXPair
kleinOrbit (Curve.affine Curve.p01) = zeroXPair
kleinOrbit (Curve.affine Curve.p1Zeta) = unitXPair
kleinOrbit (Curve.affine Curve.p1ZetaSquared) = unitXPair
kleinOrbit (Curve.affine Curve.pZetaZeta) = primitiveXFour
kleinOrbit (Curve.affine Curve.pZetaZetaSquared) = primitiveXFour
kleinOrbit (Curve.affine Curve.pZetaSquaredZeta) = primitiveXFour
kleinOrbit (Curve.affine Curve.pZetaSquaredZetaSquared) = primitiveXFour

kleinOrbitFrobeniusInvariant :
  (p : Curve.RationalF4Point) →
  kleinOrbit (Curve.frobeniusRational p) ≡ kleinOrbit p
kleinOrbitFrobeniusInvariant Curve.infinity = refl
kleinOrbitFrobeniusInvariant (Curve.affine Curve.p00) = refl
kleinOrbitFrobeniusInvariant (Curve.affine Curve.p01) = refl
kleinOrbitFrobeniusInvariant (Curve.affine Curve.p1Zeta) = refl
kleinOrbitFrobeniusInvariant (Curve.affine Curve.p1ZetaSquared) = refl
kleinOrbitFrobeniusInvariant (Curve.affine Curve.pZetaZeta) = refl
kleinOrbitFrobeniusInvariant (Curve.affine Curve.pZetaZetaSquared) = refl
kleinOrbitFrobeniusInvariant (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinOrbitFrobeniusInvariant (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

kleinOrbitNegationInvariant :
  (p : Curve.RationalF4Point) →
  kleinOrbit (negateRational p) ≡ kleinOrbit p
kleinOrbitNegationInvariant Curve.infinity = refl
kleinOrbitNegationInvariant (Curve.affine Curve.p00) = refl
kleinOrbitNegationInvariant (Curve.affine Curve.p01) = refl
kleinOrbitNegationInvariant (Curve.affine Curve.p1Zeta) = refl
kleinOrbitNegationInvariant (Curve.affine Curve.p1ZetaSquared) = refl
kleinOrbitNegationInvariant (Curve.affine Curve.pZetaZeta) = refl
kleinOrbitNegationInvariant (Curve.affine Curve.pZetaZetaSquared) = refl
kleinOrbitNegationInvariant (Curve.affine Curve.pZetaSquaredZeta) = refl
kleinOrbitNegationInvariant (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

kleinOrbitCount : Nat
kleinOrbitCount = 4

infinityOrbitSize : Nat
infinityOrbitSize = 1

zeroXOrbitSize : Nat
zeroXOrbitSize = 2

unitXOrbitSize : Nat
unitXOrbitSize = 2

primitiveXOrbitSize : Nat
primitiveXOrbitSize = 4

orbitSizesRecoverNine :
  infinityOrbitSize + zeroXOrbitSize
    + unitXOrbitSize + primitiveXOrbitSize
    ≡ Curve.rationalCount
orbitSizesRecoverNine = refl

-- The selected Sheet9 chart transports both actual curve involutions;
-- inverse and forward roundtrips follow from the existing bidi chart.
sheetNegation : Codec.Sheet9 → Codec.Sheet9
sheetNegation sheet =
  Sheet.curveToSheet9
    (negateRational (Sheet.sheet9ToCurve sheet))

sheetNegationInvolutive :
  (s : Codec.Sheet9) →
  sheetNegation (sheetNegation s) ≡ s
sheetNegationInvolutive s
  rewrite Sheet.curveAfterSheet
    (negateRational (Sheet.sheet9ToCurve s))
        | negateRationalInvolutive (Sheet.sheet9ToCurve s)
        | Sheet.sheetAfterCurve s = refl

sheetNegationFrobeniusCommute :
  (s : Codec.Sheet9) →
  Sheet.sheetFrobenius (sheetNegation s)
    ≡ sheetNegation (Sheet.sheetFrobenius s)
sheetNegationFrobeniusCommute s
  rewrite sym (Sheet.curveFrobeniusToSheetReflection
            (negateRational (Sheet.sheet9ToCurve s)))
        | Sheet.sheetReflectionToCurveFrobenius s
        | frobeniusNegationCommute (Sheet.sheet9ToCurve s) = refl

-- A four-component groupoid cannot itself be the ten-component
-- arithmetic source of the exceptional Monster exponent residual.
data CurveKleinOrbitsAreTenResidualComponents : Set where

kleinOrbitCountCannotBeTen : kleinOrbitCount ≡ 10 → ⊥
kleinOrbitCountCannotBeTen ()

record F4CurveKleinOrbitBoundary : Set where
  constructor f4-curve-klein-orbit-boundary
  field
    actualNegationAndFrobeniusCommute : Bool
    jointOrbitProfileOneTwoTwoFour : Bool
    jointOrbitCountFour : Bool
    sheetNegationTransportedByBidiCodec : Bool
    jointOrbitCountIdentifiedWithMonsterTen : Bool
    ellipticGroupLawImplementedHere : Bool

canonicalF4CurveKleinOrbitBoundary : F4CurveKleinOrbitBoundary
canonicalF4CurveKleinOrbitBoundary =
  f4-curve-klein-orbit-boundary
    true true true true false false
