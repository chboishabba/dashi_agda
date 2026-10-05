module DASHI.Moonshine.OggSSPP2SupersingularUniversalDeformationSourceExact where

------------------------------------------------------------------------
-- p=2 SUPERSINGULAR UNIVERSAL DEFORMATION SOURCE
--
-- EXTERNAL SOURCE CONTEXT
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves",
-- Annals of Mathematics Studies 108, Princeton University Press, 1985.
--
-- Source facts used as acquisition targets:
--
-- * a supersingular elliptic curve over an algebraically closed field of
--   characteristic p has a one-parameter universal deformation over a complete
--   local Witt-vector power-series base W(k)[[t]];
-- * Drinfeld p^n-level structures are studied on finite local extensions of
--   that universal deformation.
--
-- These source facts justify the SHAPE of the source interface below.
-- This module does not implement Witt vectors, formal schemes, the universal
-- property, or the Katz--Mazur level-structure theorem internally.
--
-- DASHI CONTRIBUTION
--
-- The p=2 arithmetic recognition wall is represented as:
--
--   universal supersingular deformation
--      + Gamma_0(4) marked state
--      + specialization to the unique raw ker(F^2) subgroup
--      + exact finite classification into the paid ten-state target.
--
-- The first three pieces are source-acquisition structure; the final
-- ten-state classification is the open DASHI recognition theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparationExact as Unique
import DASHI.Moonshine.OggSSPP2UniqueGamma0FourMarkingBidiExact as Bidi
import DASHI.Moonshine.OggSSPP2ArithmeticBidiDualCodecTransportExact as Transport
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source-calibrated universal-deformation receipt shape.
------------------------------------------------------------------------

record SupersingularUniversalDeformationDatum : Set₁ where
  field
    ResidueField : Set
    WittBase : Set
    FormalParameter : Set
    DeformationBase : Set
    EllipticFamilyState : Set

    characteristic : Nat
    characteristicIsTwo :
      characteristic ≡ 2

    oneFormalParameter : Bool
    oneFormalParameterIsTrue :
      oneFormalParameter ≡ true

    completeLocalWittPowerSeriesShape : Bool
    completeLocalWittPowerSeriesShapeIsTrue :
      completeLocalWittPowerSeriesShape ≡ true

    supersingularSpecialFibre : Bool
    supersingularSpecialFibreIsTrue :
      supersingularSpecialFibre ≡ true

    universalPropertyImportedFromSource : Bool
    universalPropertyImportedFromSourceIsTrue :
      universalPropertyImportedFromSource ≡ true

    sourceReference : String

open SupersingularUniversalDeformationDatum public

------------------------------------------------------------------------
-- 2. Level-four marked states over the universal deformation.
------------------------------------------------------------------------

record Gamma0FourUniversalDeformationMarking
  (datum : SupersingularUniversalDeformationDatum) : Set₁ where
  field
    MarkedState : Set

    underlyingFamilyState :
      MarkedState ->
      EllipticFamilyState datum

    specializesToRawSubgroup :
      MarkedState ->
      Unique.SupersingularRawGamma0FourSubgroup

    specializationIsUniqueKerFrobeniusSquared :
      (state : MarkedState) ->
      specializesToRawSubgroup state
      ≡ Unique.kerFrobeniusSquared

    gamma0FourLevelStructurePresent :
      MarkedState ->
      Bool

    gamma0FourLevelStructurePresentIsTrue :
      (state : MarkedState) ->
      gamma0FourLevelStructurePresent state ≡ true

    deformationProvenanceRetained :
      MarkedState ->
      Bool

    deformationProvenanceRetainedIsTrue :
      (state : MarkedState) ->
      deformationProvenanceRetained state ≡ true

open Gamma0FourUniversalDeformationMarking public

------------------------------------------------------------------------
-- 3. Adapter into the already-defined unique-subgroup marking surface.
------------------------------------------------------------------------

toUniqueSubgroupMarking :
  {datum : SupersingularUniversalDeformationDatum} ->
  Gamma0FourUniversalDeformationMarking datum ->
  Unique.MarkingOverUniqueGamma0FourSubgroup
toUniqueSubgroupMarking marking =
  record
    { MarkedState =
        MarkedState marking
    ; rawSubgroup =
        specializesToRawSubgroup marking
    ; everyStateLiesOverKerFrobeniusSquared =
        specializationIsUniqueKerFrobeniusSquared marking
    ; residualDatum =
        λ _ -> Unique.deformationMarking
    ; provenanceFromArithmeticModuli =
        true
    ; provenanceFromArithmeticModuliIsTrue =
        refl
    }

------------------------------------------------------------------------
-- 4. The actual open finite-classification theorem.
--
-- Once this record is inhabited, BOTH paid dependent codecs follow
-- automatically by OggSSPP2ArithmeticBidiDualCodecTransportExact.
------------------------------------------------------------------------

record UniversalDeformationTenStateRecognition
  (datum : SupersingularUniversalDeformationDatum)
  (marking : Gamma0FourUniversalDeformationMarking datum) : Set₁ where
  field
    arithmeticBidi :
      Bidi.UniqueGamma0FourMarkingBidi
        (toUniqueSubgroupMarking marking)

open UniversalDeformationTenStateRecognition public

f4CodecInheritedFromUniversalRecognition :
  {datum : SupersingularUniversalDeformationDatum} ->
  {marking : Gamma0FourUniversalDeformationMarking datum} ->
  UniversalDeformationTenStateRecognition datum marking ->
  Bool
f4CodecInheritedFromUniversalRecognition recognition =
  true

phaseCodecInheritedFromUniversalRecognition :
  {datum : SupersingularUniversalDeformationDatum} ->
  {marking : Gamma0FourUniversalDeformationMarking datum} ->
  UniversalDeformationTenStateRecognition datum marking ->
  Bool
phaseCodecInheritedFromUniversalRecognition recognition =
  true

------------------------------------------------------------------------
-- 5. Promotion firewalls.
------------------------------------------------------------------------

data UniversalDeformationDimensionCreatesTenStates : Set where
data UniqueSpecialFibreSubgroupCreatesTenStates : Set where
data DrinfeldLevelStructureExistenceCreatesOneOneEight : Set where

oneParameterDoesNotCreateTenStates :
  UniversalDeformationDimensionCreatesTenStates -> ⊥
oneParameterDoesNotCreateTenStates ()

uniqueSpecialFibreSubgroupDoesNotCreateTenStates :
  UniqueSpecialFibreSubgroupCreatesTenStates -> ⊥
uniqueSpecialFibreSubgroupDoesNotCreateTenStates ()

drinfeldExistenceDoesNotCreateOneOneEight :
  DrinfeldLevelStructureExistenceCreatesOneOneEight -> ⊥
drinfeldExistenceDoesNotCreateOneOneEight ()

------------------------------------------------------------------------
-- 6. Exact residual ordering.
------------------------------------------------------------------------

data UniversalDeformationSourceResidual : Set where
  missingFormalWittPowerSeriesBase :
    UniversalDeformationSourceResidual

  missingFormalUniversalEllipticFamily :
    UniversalDeformationSourceResidual

  missingGamma0FourMarkedDeformationStates :
    UniversalDeformationSourceResidual

  missingTenStateClassificationBidi :
    UniversalDeformationSourceResidual

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

sourceCitation : String
sourceCitation =
  "N. Katz and B. Mazur, Arithmetic Moduli of Elliptic Curves, Annals of Mathematics Studies 108, Princeton University Press, 1985"

record SupersingularUniversalDeformationBoundary : Set where
  constructor supersingular-universal-deformation-boundary
  field
    sourceBackedOneParameterShapeRecorded : Bool
    sourceBackedWittPowerSeriesShapeRecorded : Bool
    sourceBackedDrinfeldLevelStructureContextRecorded : Bool
    specializationToUniqueKerFrobeniusSquaredRequired : Bool
    tenStateClassificationSeparatedFromSourceShape : Bool
    oneParameterCountPromotedToTenStates : Bool
    universalDeformationImplementedInternally : Bool
    gamma0FourMarkedStatesConstructed : Bool
    tenStateRecognitionConstructed : Bool
    firstResidual : UniversalDeformationSourceResidual

canonicalSupersingularUniversalDeformationBoundary :
  SupersingularUniversalDeformationBoundary
canonicalSupersingularUniversalDeformationBoundary =
  supersingular-universal-deformation-boundary
    true true true true true false false false false
    missingFormalWittPowerSeriesBase
