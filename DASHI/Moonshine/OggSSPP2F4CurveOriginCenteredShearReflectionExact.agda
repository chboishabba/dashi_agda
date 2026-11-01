module DASHI.Moonshine.OggSSPP2F4CurveOriginCenteredShearReflectionExact where

------------------------------------------------------------------------
-- ORIGIN-CENTRED SHEET9 TRANSPORT OF THE ACTUAL F4 CURVE S3 ACTION
--
-- Donors:
--   * OggSSPP2F4CurveOriginCenteredSheet9Exact:
--       pointed Frobenius-equivariant bidi
--         E(F4)_set <-> Sheet9
--       sending elliptic infinity to (zero,zero);
--   * OggSSPP2F4CurveShearReflectionExact:
--       actual coordinate shear rho(x,y)=(zeta*x,y),
--       Frobenius, rho^3=id, F^2=id, F rho F=rho^-1.
--
-- DASHI contribution:
--   transport the ACTUAL curve actions through the pointed bidi and prove
--   the same S3 presentation on the existing Sheet9 carrier.
--
-- This is still a SET-ACTION transport. It does not assert that Sheet9's
-- displayed ternary operation is already the actual elliptic group law.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact as Curve
import DASHI.Moonshine.OggSSPP2F4CurveOriginCenteredSheet9Exact as Center
import DASHI.Moonshine.OggSSPP2F4CurveShearReflectionExact as CurveS3
import DASHI.Moonshine.OggSSPP2F4CurveSheet9FrobeniusBidiExact as Original

centeredShear : Codec.Sheet9 → Codec.Sheet9
centeredShear s =
  Center.centeredCurveToSheet
    (CurveS3.rho (Center.centeredSheetToCurve s))

centeredFrobenius : Codec.Sheet9 → Codec.Sheet9
centeredFrobenius = Original.sheetFrobenius

centeredShearIntertwining :
  (p : Curve.RationalF4Point) →
  Center.centeredCurveToSheet (CurveS3.rho p)
    ≡ centeredShear (Center.centeredCurveToSheet p)
centeredShearIntertwining p
  rewrite Center.centeredAfterCurve p = refl

centeredShearDecode :
  (s : Codec.Sheet9) →
  Center.centeredSheetToCurve (centeredShear s)
    ≡ CurveS3.rho (Center.centeredSheetToCurve s)
centeredShearDecode s
  rewrite Center.centeredAfterCurve
    (CurveS3.rho (Center.centeredSheetToCurve s)) = refl

centeredShearTwice : Codec.Sheet9 → Codec.Sheet9
centeredShearTwice s = centeredShear (centeredShear s)

centeredShearThree :
  (s : Codec.Sheet9) →
  centeredShear (centeredShearTwice s) ≡ s
centeredShearThree s
  rewrite centeredShearDecode s
        | centeredShearDecode (centeredShear s)
        | centeredShearDecode (centeredShearTwice s)
        | CurveS3.rhoThree (Center.centeredSheetToCurve s)
        | Center.centeredAfterSheet s = refl

centeredFrobeniusTwo :
  (s : Codec.Sheet9) →
  centeredFrobenius (centeredFrobenius s) ≡ s
centeredFrobeniusTwo s =
  Original.sheetFrobeniusInvolutive s

centeredFrobeniusIntertwining :
  (p : Curve.RationalF4Point) →
  Center.centeredCurveToSheet (Curve.frobeniusRational p)
    ≡ centeredFrobenius (Center.centeredCurveToSheet p)
centeredFrobeniusIntertwining =
  Center.centeredFrobeniusIntertwining

centeredFrobeniusDecode :
  (s : Codec.Sheet9) →
  Center.centeredSheetToCurve (centeredFrobenius s)
    ≡ Curve.frobeniusRational (Center.centeredSheetToCurve s)
centeredFrobeniusDecode s
  rewrite Center.centeredFrobeniusIntertwining
    (Center.centeredSheetToCurve s)
        | Center.centeredAfterSheet s = refl

-- Sheet-level reflection conjugates the shear to its inverse.
centeredFrobeniusConjugatesShear :
  (s : Codec.Sheet9) →
  centeredFrobenius
    (centeredShear (centeredFrobenius s))
  ≡ centeredShearTwice s
centeredFrobeniusConjugatesShear s
  rewrite centeredFrobeniusDecode s
        | centeredShearDecode (centeredFrobenius s)
        | centeredFrobeniusDecode (centeredShear (centeredFrobenius s))
        | CurveS3.frobeniusConjugatesRho
            (Center.centeredSheetToCurve s)
        | Center.centeredAfterCurve
            (CurveS3.rhoTwice (Center.centeredSheetToCurve s))
        | centeredShearDecode s
        | centeredShearDecode (centeredShear s) = refl

centeredIdentityFixedByShear :
  centeredShear
    (Center.centeredCurveToSheet Curve.infinity)
  ≡ Center.centeredCurveToSheet Curve.infinity
centeredIdentityFixedByShear =
  centeredShearIntertwining Curve.infinity

centeredIdentityFixedByFrobenius :
  centeredFrobenius
    (Center.centeredCurveToSheet Curve.infinity)
  ≡ Center.centeredCurveToSheet Curve.infinity
centeredIdentityFixedByFrobenius =
  centeredFrobeniusIntertwining Curve.infinity

record Boundary : Set where
  constructor boundary
  field
    pointedCurveSheetBidiReused : Bool
    actualCurveShearTransported : Bool
    actualFrobeniusTransported : Bool
    sheetShearOrderThree : Bool
    sheetFrobeniusOrderTwo : Bool
    sheetS3ConjugationRelation : Bool
    groupLawIntertwiningProved : Bool
    monsterValuationRecognitionProved : Bool

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true true true false false
