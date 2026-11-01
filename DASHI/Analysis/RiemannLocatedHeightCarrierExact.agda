module DASHI.Analysis.RiemannLocatedHeightCarrierExact where

------------------------------------------------------------------------
-- MINIMAL REAL CAPABILITY ACTUALLY REQUIRED BY THE RH LOW/HIGH SPLIT
--
-- No field operations, reciprocal, completeness package, decidable comparison,
-- rational density or Archimedean ceiling are required at the terminal split.
-- We need only:
--
--   * a real carrier,
--   * absolute value for the ordinate,
--   * strict order,
--   * two separated thresholds,
--   * locatedness between those thresholds.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Sum using (_⊎_)

record LocatedHeightCarrier : Set₁ where
  infix 4 _<_
  field
    Carrier : Set
    abs : Carrier → Carrier
    _<_ : Carrier → Carrier → Set

    highStart : Carrier
    publishedHeight : Carrier
    highStartBelowPublishedHeight : highStart < publishedHeight

    locatedBetweenThresholds :
      (value : Carrier) →
      value < publishedHeight ⊎ highStart < value

open LocatedHeightCarrier public

record LocatedHeightCarrierBoundary : Set where
  constructor located-height-carrier-boundary
  field
    fullOrderedFieldRequired : Bool
    completenessRequired : Bool
    exactThresholdDecisionRequired : Bool
    strictLocatedSplitRequired : Bool
    absoluteOrdinateRequired : Bool

open LocatedHeightCarrierBoundary public

canonicalLocatedHeightCarrierBoundary : LocatedHeightCarrierBoundary
canonicalLocatedHeightCarrierBoundary =
  located-height-carrier-boundary
    false false false true true
