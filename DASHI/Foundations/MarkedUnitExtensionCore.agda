module DASHI.Foundations.MarkedUnitExtensionCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Marked unit extension.
--
-- A carrier-plus-one law keeps the adjoined unit's provenance visible.  An
-- external fresh unit, a labelled inherited subfibre, and an internal
-- residual witness are distinct constructors even when all measure one.
------------------------------------------------------------------------

data UnitOrigin : Set where
  freshExternalUnit labelledSubfibreUnit internalResidualUnit : UnitOrigin

freshExternalIsNotInternal :
  freshExternalUnit ≡ internalResidualUnit → ⊥
freshExternalIsNotInternal ()

labelledSubfibreIsNotSubtraction :
  labelledSubfibreUnit ≡ internalResidualUnit → ⊥
labelledSubfibreIsNotSubtraction ()

record MarkedUnitExtension : Set where
  field
    carrierMeasure : Nat
    unitMeasure : Nat
    extendedMeasure : Nat
    unitIsOne : unitMeasure ≡ 1
    extensionExact : carrierMeasure + unitMeasure ≡ extendedMeasure
    unitOrigin : UnitOrigin
    carrierLabel : String
    unitLabel : String
    extendedLabel : String
    originRetainedAfterExtension : Bool
    internalSubobjectClaimed : Bool
    semanticIdentityWithOtherCarriersClaimed : Bool

open MarkedUnitExtension public

carrierPlusOne :
  (extension : MarkedUnitExtension) →
  carrierMeasure extension + 1 ≡ extendedMeasure extension
carrierPlusOne extension =
  trans
    (cong (λ n → carrierMeasure extension + n)
      (sym (unitIsOne extension)))
    (extensionExact extension)

record PlusOneShapePair
    (left right : MarkedUnitExtension) : Set where
  field
    leftPlusOne :
      carrierMeasure left + 1 ≡ extendedMeasure left
    rightPlusOne :
      carrierMeasure right + 1 ≡ extendedMeasure right
    unitOriginsVisible : Bool
    carriersIdentified : Bool
    scalesIdentified : Bool
    semanticsIdentified : Bool
    shapeReceipt : String

open PlusOneShapePair public

mkPlusOneShapePair :
  (left right : MarkedUnitExtension) →
  String →
  PlusOneShapePair left right
mkPlusOneShapePair left right receipt = record
  { leftPlusOne = carrierPlusOne left
  ; rightPlusOne = carrierPlusOne right
  ; unitOriginsVisible = true
  ; carriersIdentified = false
  ; scalesIdentified = false
  ; semanticsIdentified = false
  ; shapeReceipt = receipt
  }

record MarkedUnitExtensionBoundary : Set where
  field
    predecessorSubtractionRequired : Bool
    freshUnitEqualsInternalResidual : Bool
    sameMeasuredSizeImpliesSameConstruction : Bool
    sharedPlusOneShapeAvailable : Bool
    provenanceMustRemainVisible : Bool
    boundaryNote : String

canonicalMarkedUnitExtensionBoundary : MarkedUnitExtensionBoundary
canonicalMarkedUnitExtensionBoundary = record
  { predecessorSubtractionRequired = false
  ; freshUnitEqualsInternalResidual = false
  ; sameMeasuredSizeImpliesSameConstruction = false
  ; sharedPlusOneShapeAvailable = true
  ; provenanceMustRemainVisible = true
  ; boundaryNote =
      "The hyphenated 'j-previous subfibre' may be a label, not subtraction. A fresh external one-dimensional unit is not an internal residual merely because both measure one."
  }
