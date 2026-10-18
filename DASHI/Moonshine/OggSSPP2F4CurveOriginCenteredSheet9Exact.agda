module DASHI.Moonshine.OggSSPP2F4CurveOriginCenteredSheet9Exact where

------------------------------------------------------------------------
-- F4 CURVE / SHEET9: ORIGIN-CENTRED FROBENIUS-EQUIVARIANT CHART
--
-- The older nine-sheet chart sends the elliptic identity infinity to
-- (neg, zero), not (zero, zero).  That chart is a genuine C2-set equivalence,
-- but it cannot be interpreted as a group isomorphism to a zero-based
-- ternary vector group without first repairing the identity coordinate.
--
-- The following cyclic first-trit translation sends infinity to (0,0)
-- while commuting with Frobenius reflection in the second coordinate.
--
-- This is still ONLY a pointed C2-set chart, not an elliptic-group law.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Algebra.Trit as Trit
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact as Curve
import DASHI.Moonshine.OggSSPP2F4CurveSheet9FrobeniusBidiExact as Original

open Codec using ([]ᵥ; _∷ᵥ_)

advanceFirst : Trit.Trit → Trit.Trit
advanceFirst Trit.neg = Trit.zer
advanceFirst Trit.zer = Trit.pos
advanceFirst Trit.pos = Trit.neg

retreatFirst : Trit.Trit → Trit.Trit
retreatFirst Trit.neg = Trit.pos
retreatFirst Trit.zer = Trit.neg
retreatFirst Trit.pos = Trit.zer

advanceAfterRetreat :
  (t : Trit.Trit) → advanceFirst (retreatFirst t) ≡ t
advanceAfterRetreat Trit.neg = refl
advanceAfterRetreat Trit.zer = refl
advanceAfterRetreat Trit.pos = refl

retreatAfterAdvance :
  (t : Trit.Trit) → retreatFirst (advanceFirst t) ≡ t
retreatAfterAdvance Trit.neg = refl
retreatAfterAdvance Trit.zer = refl
retreatAfterAdvance Trit.pos = refl

normalizeSheet : Codec.Sheet9 → Codec.Sheet9
normalizeSheet (a ∷ᵥ b ∷ᵥ []ᵥ) =
  advanceFirst a ∷ᵥ b ∷ᵥ []ᵥ

denormalizeSheet : Codec.Sheet9 → Codec.Sheet9
denormalizeSheet (a ∷ᵥ b ∷ᵥ []ᵥ) =
  retreatFirst a ∷ᵥ b ∷ᵥ []ᵥ

normalizeDenormalize :
  (s : Codec.Sheet9) → normalizeSheet (denormalizeSheet s) ≡ s
normalizeDenormalize (a ∷ᵥ b ∷ᵥ []ᵥ)
  rewrite advanceAfterRetreat a = refl

denormalizeNormalize :
  (s : Codec.Sheet9) → denormalizeSheet (normalizeSheet s) ≡ s
denormalizeNormalize (a ∷ᵥ b ∷ᵥ []ᵥ)
  rewrite retreatAfterAdvance a = refl

centeredCurveToSheet : Curve.RationalF4Point → Codec.Sheet9
centeredCurveToSheet p = normalizeSheet (Original.curveToSheet9 p)

centeredSheetToCurve : Codec.Sheet9 → Curve.RationalF4Point
centeredSheetToCurve s = Original.sheet9ToCurve (denormalizeSheet s)

centeredAfterCurve :
  (p : Curve.RationalF4Point) →
  centeredSheetToCurve (centeredCurveToSheet p) ≡ p
centeredAfterCurve p
  rewrite denormalizeNormalize (Original.curveToSheet9 p)
        | Original.curveAfterSheet p = refl

centeredAfterSheet :
  (s : Codec.Sheet9) →
  centeredCurveToSheet (centeredSheetToCurve s) ≡ s
centeredAfterSheet s
  rewrite Original.sheetAfterCurve (denormalizeSheet s)
        | normalizeDenormalize s = refl

centeredIdentityAtZero :
  centeredCurveToSheet Curve.infinity ≡ Codec.sheet Trit.zer Trit.zer
centeredIdentityAtZero = refl

normalizeCommutesWithFrobenius :
  (s : Codec.Sheet9) →
  normalizeSheet (Original.sheetFrobenius s)
    ≡ Original.sheetFrobenius (normalizeSheet s)
normalizeCommutesWithFrobenius (a ∷ᵥ b ∷ᵥ []ᵥ) = refl

centeredFrobeniusIntertwining :
  (p : Curve.RationalF4Point) →
  centeredCurveToSheet (Curve.frobeniusRational p)
    ≡ Original.sheetFrobenius (centeredCurveToSheet p)
centeredFrobeniusIntertwining p
  rewrite Original.curveFrobeniusToSheetReflection p
        | normalizeCommutesWithFrobenius (Original.curveToSheet9 p) = refl

record F4CurveOriginCenteredSheetBoundary : Set where
  constructor f4-curve-origin-centered-sheet-boundary
  field
    originalFrobeniusChartRetained : Bool
    originNormalizedToZeroZero : Bool
    bidirectionalRechartPaid : Bool
    frobeniusStillReflectsSecondCoordinate : Bool
    ellipticGroupLawPreservationProved : Bool
    gammaZeroFourMarkingProved : Bool

canonicalF4CurveOriginCenteredSheetBoundary :
  F4CurveOriginCenteredSheetBoundary
canonicalF4CurveOriginCenteredSheetBoundary =
  f4-curve-origin-centered-sheet-boundary
    true true true true false false
