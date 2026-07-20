module DASHI.Philosophy.RepresentationReadingBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Structural and symbolic readings answer different questions.
--
-- A property noticed in a representation is not automatically a property
-- proved of the represented object.

data ReadingKind : Set where
  structuralReading :
    ReadingKind

  symbolicReading :
    ReadingKind

record RepresentationReadingBoundary : Set where
  constructor mkRepresentationReadingBoundary
  field
    structuralReadingTracksDefinedRelations :
      Bool

    symbolicReadingTracksAssociations :
      Bool

    symbolicResonanceProvesStructuralProperty :
      Bool

    decimalPointPromotionGateIsIntrinsicArithmetic :
      Bool

    customChartMustBeDeclared :
      Bool

open RepresentationReadingBoundary public

canonicalRepresentationReadingBoundary :
  RepresentationReadingBoundary
canonicalRepresentationReadingBoundary =
  mkRepresentationReadingBoundary
    true
    true
    false
    false
    true

canonicalSymbolicDoesNotProveStructural :
  symbolicResonanceProvesStructuralProperty
    canonicalRepresentationReadingBoundary
  ≡
  false
canonicalSymbolicDoesNotProveStructural =
  refl
