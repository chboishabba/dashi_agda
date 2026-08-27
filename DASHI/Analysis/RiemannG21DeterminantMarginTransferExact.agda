module DASHI.Analysis.RiemannG21DeterminantMarginTransferExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Margin-preserving transfer from continuum odd determinant to the actual
-- finite-radius parity minor.
--
-- Do NOT approximate four response entries independently and only then form
-- the determinant.  Instead expose a direct determinant approximation:
--
--   Delta_odd > 0,
--   |D_R - Delta_odd| < Delta_odd,
--   hence D_R > 0.
--
-- This is the exact condition needed to preserve sign while minimizing
-- constant loss.
------------------------------------------------------------------------

record DeterminantMarginTransfer : Set₁ where
  field
    Scalar : Set
    zero continuumMargin finiteRadiusDeterminant errorMagnitude : Scalar

    StrictGreater StrictBelow : Scalar → Scalar → Set

    continuumMarginPositive : StrictGreater continuumMargin zero
    determinantApproximationError :
      StrictBelow errorMagnitude continuumMargin
    finiteRadiusSignPreserved :
      StrictGreater finiteRadiusDeterminant zero

    transferReading : String

open DeterminantMarginTransfer public

------------------------------------------------------------------------
-- Literal signed version with an abstract distance/absolute-error operation.
------------------------------------------------------------------------

record SignedDeterminantApproximation : Set₁ where
  field
    Scalar : Set
    zero : Scalar
    continuumDet finiteDet : Scalar
    distance : Scalar → Scalar → Scalar
    StrictGreater StrictBelow : Scalar → Scalar → Set

    continuumPositive : StrictGreater continuumDet zero
    relativeErrorBelowMargin :
      StrictBelow (distance finiteDet continuumDet) continuumDet
    finitePositive : StrictGreater finiteDet zero

    approximationReading : String

open SignedDeterminantApproximation public

record OddFiniteRadiusMarginTarget : Set₁ where
  field
    Height Radius Scalar : Set
    offLineHeight poleHeight : Height
    innerRadius outerRadius : Radius

    zero : Scalar
    continuumOddMargin : Scalar
    finiteOddMinor : Scalar
    determinantError : Scalar

    StrictGreater StrictBelow : Scalar → Scalar → Set

    continuumOddMarginPositive : StrictGreater continuumOddMargin zero
    directDeterminantErrorBelowMargin :
      StrictBelow determinantError continuumOddMargin
    finiteOddMinorPositive : StrictGreater finiteOddMinor zero

    targetReading : String

record DeterminantMarginBoundary : Set where
  constructor determinantMarginBoundary
  field
    directDeterminantErrorTargetConstructed : Bool
    directDeterminantErrorTargetConstructedIsTrue :
      directDeterminantErrorTargetConstructed ≡ true
    entrywiseTriangleBoundRequiredByInterface : Bool
    entrywiseTriangleBoundRequiredByInterfaceIsFalse :
      entrywiseTriangleBoundRequiredByInterface ≡ false
    continuumMarginMustBeStrict : Bool
    continuumMarginMustBeStrictIsTrue : continuumMarginMustBeStrict ≡ true
    actualTaylorMarginTransferDerived : Bool
    actualTaylorMarginTransferDerivedIsFalse :
      actualTaylorMarginTransferDerived ≡ false

canonicalDeterminantMarginBoundary : DeterminantMarginBoundary
canonicalDeterminantMarginBoundary =
  determinantMarginBoundary true refl false refl true refl false refl
