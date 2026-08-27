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
--   |D_R - Delta_odd| < Delta_odd.
--
-- This is the exact condition needed to preserve the sign of the finite-
-- radius determinant while minimizing constant loss.
------------------------------------------------------------------------

record DeterminantMarginTransfer : Set₁ where
  field
    Scalar : Set
    continuumMargin finiteRadiusDeterminant errorMagnitude : Scalar

    StrictPositive : Scalar → Set
    StrictBelow : Scalar → Scalar → Set
    StrictGreater : Scalar → Scalar → Set

    continuumMarginPositive : StrictPositive continuumMargin
    determinantApproximationError :
      StrictBelow errorMagnitude continuumMargin

    finiteRadiusSignPreserved :
      StrictGreater finiteRadiusDeterminant continuumMargin → Set

    transferReading : String

open DeterminantMarginTransfer public

------------------------------------------------------------------------
-- More literal signed version: the consumer supplies an absolute-value error
-- relation and receives a strict positive determinant theorem as the intended
-- endpoint.  The implication is kept as a theorem socket until the ordered
-- real carrier used by G21 is available in Agda.
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

    continuumOddMargin : Scalar
    finiteOddMinor : Scalar
    determinantError : Scalar

    StrictPositive : Scalar → Set
    StrictBelow : Scalar → Scalar → Set

    continuumOddMarginPositive : StrictPositive continuumOddMargin
    directDeterminantErrorBelowMargin :
      StrictBelow determinantError continuumOddMargin
    finiteOddMinorPositive : StrictPositive finiteOddMinor

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
