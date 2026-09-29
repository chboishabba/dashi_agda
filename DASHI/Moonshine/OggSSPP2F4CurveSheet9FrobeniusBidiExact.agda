module DASHI.Moonshine.OggSSPP2F4CurveSheet9FrobeniusBidiExact where

------------------------------------------------------------------------
-- F4 CURVE POINTS <-> CANONICAL NINE-SHEET WITH FROBENIUS REFLECTION
--
-- Arithmetic source: the F4-points and coordinatewise square Frobenius on
-- y^2+y=x^3, defined independently in
-- OggSSPP2F4ZetaCurvePointEnumerationExact.
--
-- Repo-specific chart: assign the three Frobenius fixed points to the
-- second-trit-zero axis, and the three pairs to the three first-trit values.
--
-- The resulting finite chart is bijective AND intertwines the actual
-- arithmetic Frobenius with (a,b) -> (a,inv b).
--
-- This is a chosen C2-SET CHART, not an elliptic-group isomorphism,
-- 3-torsion identification, characteristic-zero field map, Gamma0(4)
-- marking, nor identification of any Monster inertia action.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Algebra.Trit as Trit
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact as Curve

open Codec using ([]ᵥ; _∷ᵥ_)

sheetFrobenius : Codec.Sheet9 → Codec.Sheet9
sheetFrobenius (a ∷ᵥ b ∷ᵥ []ᵥ) =
  a ∷ᵥ Trit.inv b ∷ᵥ []ᵥ

sheetFrobeniusInvolutive :
  (s : Codec.Sheet9) →
  sheetFrobenius (sheetFrobenius s) ≡ s
sheetFrobeniusInvolutive (a ∷ᵥ b ∷ᵥ []ᵥ)
  rewrite Trit.inv-invol b = refl

-- First trit labels the Frobenius orbit. Second trit distinguishes the
-- two members, with zero denoting the fixed-point stratum.
curveToSheet9 : Curve.RationalF4Point → Codec.Sheet9
curveToSheet9 Curve.infinity = Codec.sheet Trit.neg Trit.zer
curveToSheet9 (Curve.affine Curve.p00) = Codec.sheet Trit.zer Trit.zer
curveToSheet9 (Curve.affine Curve.p01) = Codec.sheet Trit.pos Trit.zer
curveToSheet9 (Curve.affine Curve.p1Zeta) = Codec.sheet Trit.neg Trit.pos
curveToSheet9 (Curve.affine Curve.p1ZetaSquared) =
  Codec.sheet Trit.neg Trit.neg
curveToSheet9 (Curve.affine Curve.pZetaZeta) =
  Codec.sheet Trit.zer Trit.pos
curveToSheet9 (Curve.affine Curve.pZetaSquaredZetaSquared) =
  Codec.sheet Trit.zer Trit.neg
curveToSheet9 (Curve.affine Curve.pZetaZetaSquared) =
  Codec.sheet Trit.pos Trit.pos
curveToSheet9 (Curve.affine Curve.pZetaSquaredZeta) =
  Codec.sheet Trit.pos Trit.neg

sheet9ToCurve : Codec.Sheet9 → Curve.RationalF4Point
sheet9ToCurve (Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = Curve.infinity
sheet9ToCurve (Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) =
  Curve.affine Curve.p00
sheet9ToCurve (Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) =
  Curve.affine Curve.p01
sheet9ToCurve (Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) =
  Curve.affine Curve.p1Zeta
sheet9ToCurve (Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) =
  Curve.affine Curve.p1ZetaSquared
sheet9ToCurve (Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) =
  Curve.affine Curve.pZetaZeta
sheet9ToCurve (Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) =
  Curve.affine Curve.pZetaSquaredZetaSquared
sheet9ToCurve (Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) =
  Curve.affine Curve.pZetaZetaSquared
sheet9ToCurve (Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) =
  Curve.affine Curve.pZetaSquaredZeta

sheetAfterCurve :
  (s : Codec.Sheet9) →
  curveToSheet9 (sheet9ToCurve s) ≡ s
sheetAfterCurve (Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
sheetAfterCurve (Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
sheetAfterCurve (Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
sheetAfterCurve (Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
sheetAfterCurve (Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
sheetAfterCurve (Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
sheetAfterCurve (Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
sheetAfterCurve (Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
sheetAfterCurve (Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl

curveAfterSheet :
  (p : Curve.RationalF4Point) →
  sheet9ToCurve (curveToSheet9 p) ≡ p
curveAfterSheet Curve.infinity = refl
curveAfterSheet (Curve.affine Curve.p00) = refl
curveAfterSheet (Curve.affine Curve.p01) = refl
curveAfterSheet (Curve.affine Curve.p1Zeta) = refl
curveAfterSheet (Curve.affine Curve.p1ZetaSquared) = refl
curveAfterSheet (Curve.affine Curve.pZetaZeta) = refl
curveAfterSheet (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
curveAfterSheet (Curve.affine Curve.pZetaZetaSquared) = refl
curveAfterSheet (Curve.affine Curve.pZetaSquaredZeta) = refl

curveFrobeniusToSheetReflection :
  (p : Curve.RationalF4Point) →
  curveToSheet9 (Curve.frobeniusRational p)
  ≡ sheetFrobenius (curveToSheet9 p)
curveFrobeniusToSheetReflection Curve.infinity = refl
curveFrobeniusToSheetReflection (Curve.affine Curve.p00) = refl
curveFrobeniusToSheetReflection (Curve.affine Curve.p01) = refl
curveFrobeniusToSheetReflection (Curve.affine Curve.p1Zeta) = refl
curveFrobeniusToSheetReflection (Curve.affine Curve.p1ZetaSquared) = refl
curveFrobeniusToSheetReflection (Curve.affine Curve.pZetaZeta) = refl
curveFrobeniusToSheetReflection (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
curveFrobeniusToSheetReflection (Curve.affine Curve.pZetaZetaSquared) = refl
curveFrobeniusToSheetReflection (Curve.affine Curve.pZetaSquaredZeta) = refl

sheetReflectionToCurveFrobenius :
  (s : Codec.Sheet9) →
  sheet9ToCurve (sheetFrobenius s)
  ≡ Curve.frobeniusRational (sheet9ToCurve s)
sheetReflectionToCurveFrobenius (Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
sheetReflectionToCurveFrobenius (Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
sheetReflectionToCurveFrobenius (Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
sheetReflectionToCurveFrobenius (Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
sheetReflectionToCurveFrobenius (Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
sheetReflectionToCurveFrobenius (Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
sheetReflectionToCurveFrobenius (Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
sheetReflectionToCurveFrobenius (Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
sheetReflectionToCurveFrobenius (Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl

-- Unlike whole-sheet simultaneous sign inversion, arithmetic Frobenius
-- leaves every point on the b=0 axis fixed.
sheetFrobeniusFixesZeroAxis :
  (a : Trit.Trit) →
  sheetFrobenius (Codec.sheet a Trit.zer)
  ≡ Codec.sheet a Trit.zer
sheetFrobeniusFixesZeroAxis Trit.neg = refl
sheetFrobeniusFixesZeroAxis Trit.zer = refl
sheetFrobeniusFixesZeroAxis Trit.pos = refl

sheetFrobeniusDiffersFromWholeInversion :
  sheetFrobenius (Codec.sheet Trit.pos Trit.zer)
  ≡ Codec.invertKernel (Codec.sheet Trit.pos Trit.zer)
  → ⊥
sheetFrobeniusDiffersFromWholeInversion ()

record F4CurveSheet9FrobeniusBoundary : Set where
  constructor f4-curve-sheet9-frobenius-boundary
  field
    curveNinePointsReused : Bool
    twoSidedNineSheetChart : Bool
    actualFrobeniusIntertwinesSheetReflection : Bool
    inverseIntertwiningOwned : Bool
    threeFixedPointAxisOwned : Bool
    arithmeticFrobeniusNotWholeSheetInversion : Bool
    ellipticGroupLawIntertwiningClaimed : Bool
    sourceNativeInertiaActionIdentified : Bool
    gammaZeroFourFlagConstructed : Bool

canonicalF4CurveSheet9FrobeniusBoundary :
  F4CurveSheet9FrobeniusBoundary
canonicalF4CurveSheet9FrobeniusBoundary =
  f4-curve-sheet9-frobenius-boundary
    true true true true true true false false false
