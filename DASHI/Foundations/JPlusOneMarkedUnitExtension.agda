module DASHI.Foundations.JPlusOneMarkedUnitExtension where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import Moonshine as Moon
import DASHI.Foundations.JPlusOneScaleBridge as Legacy
import DASHI.Foundations.MarkedUnitExtensionCore as Marked

------------------------------------------------------------------------
-- Typed refinement of the existing j+1 bridge.
--
-- The expression "j-previous subfibre" is treated as a compound label unless
-- a subtraction witness is separately supplied.  The stage and moonshine
-- instances share the carrier-plus-marked-unit schema without sharing carrier,
-- scale, representation theory or semantics.
------------------------------------------------------------------------

j-unit : Nat
j-unit = 1

J-stage-carrier : Nat
J-stage-carrier = 10

J-stage-extended : Nat
J-stage-extended = 11

J-moonshine-carrier : Nat
J-moonshine-carrier = Moon.rep-dim

J-moonshine-extended : Nat
J-moonshine-extended = Moon.j-coefficient

stageMarkedUnitExtension : Marked.MarkedUnitExtension
stageMarkedUnitExtension = record
  { carrierMeasure = J-stage-carrier
  ; unitMeasure = j-unit
  ; extendedMeasure = J-stage-extended
  ; unitIsOne = refl
  ; extensionExact = Legacy.elevenJIsTenJPlusJ
  ; unitOrigin = Marked.labelledSubfibreUnit
  ; carrierLabel = "decimal cross-scale carrier 10j"
  ; unitLabel = "fresh j-unit / j-previous-subfibre-labelled unit"
  ; extendedLabel = "11j"
  ; originRetainedAfterExtension = true
  ; internalSubobjectClaimed = false
  ; semanticIdentityWithOtherCarriersClaimed = false
  }

moonshineMarkedUnitExtension : Marked.MarkedUnitExtension
moonshineMarkedUnitExtension = record
  { carrierMeasure = J-moonshine-carrier
  ; unitMeasure = j-unit
  ; extendedMeasure = J-moonshine-extended
  ; unitIsOne = refl
  ; extensionExact = Moon.mckay
  ; unitOrigin = Marked.freshExternalUnit
  ; carrierLabel = "196883-dimensional nontrivial moonshine component"
  ; unitLabel = "independently supplied trivial one-dimensional component"
  ; extendedLabel = "196884 first nonconstant j-coefficient decomposition"
  ; originRetainedAfterExtension = true
  ; internalSubobjectClaimed = false
  ; semanticIdentityWithOtherCarriersClaimed = false
  }

stageAndMoonshineSharePlusOneShape :
  Marked.PlusOneShapePair
    stageMarkedUnitExtension
    moonshineMarkedUnitExtension
stageAndMoonshineSharePlusOneShape =
  Marked.mkPlusOneShapePair
    stageMarkedUnitExtension
    moonshineMarkedUnitExtension
    "10j + j = 11j and 196883 + 1 = 196884 instantiate one marked carrier-plus-unit schema; carriers and semantics remain distinct."

stageCarrierPlusOneExact :
  J-stage-carrier + 1 ≡ J-stage-extended
stageCarrierPlusOneExact =
  Marked.carrierPlusOne stageMarkedUnitExtension

moonshineCarrierPlusOneExact :
  J-moonshine-carrier + 1 ≡ J-moonshine-extended
moonshineCarrierPlusOneExact =
  Marked.carrierPlusOne moonshineMarkedUnitExtension

data HyphenReading : Set where
  compoundSubfibreLabel subtractionExpression : HyphenReading

intendedJPreviousSubfibreReading : HyphenReading
intendedJPreviousSubfibreReading = compoundSubfibreLabel

compoundLabelIsNotSubtraction :
  compoundSubfibreLabel ≡ subtractionExpression → ⊥
compoundLabelIsNotSubtraction ()

record JPlusOneMarkedAuthorityBoundary : Set where
  field
    predecessorResidualConstructionRequired : Bool
    previousSubfibreHyphenParsedAsSubtraction : Bool
    stageUnitProvenanceRetained : Bool
    moonshineUnitExternal : Bool
    moonshineInternal196882SubrepresentationClaimed : Bool
    samePlusOneSchemaProved : Bool
    carriersIdentified : Bool
    semanticsIdentified : Bool
    boundaryNote : String

canonicalJPlusOneMarkedAuthorityBoundary :
  JPlusOneMarkedAuthorityBoundary
canonicalJPlusOneMarkedAuthorityBoundary = record
  { predecessorResidualConstructionRequired = false
  ; previousSubfibreHyphenParsedAsSubtraction = false
  ; stageUnitProvenanceRetained = true
  ; moonshineUnitExternal = true
  ; moonshineInternal196882SubrepresentationClaimed = false
  ; samePlusOneSchemaProved = true
  ; carriersIdentified = false
  ; semanticsIdentified = false
  ; boundaryNote =
      "The common theorem is marked unit extension. No subtraction reading, 196882-dimensional internal subrepresentation or equality of stage and moonshine carriers is asserted."
  }
