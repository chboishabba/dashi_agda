module DASHI.Physics.Plasma.FRCCompressionFusionHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.MagneticTopologyHyperfabricExact as Plasma

------------------------------------------------------------------------
-- FIELD-REVERSED-CONFIGURATION / COMPRESSION / FUSION CHAIN
------------------------------------------------------------------------

record FRCState : Set₁ where
  constructor frc-state
  field
    voxel : Plasma.PlasmaHypervoxel
    ClosedPoloidalFlux : Set
    FieldReversal : Set
    CompactToroidalPlasmoid : Set
    PlasmaBeta : Set
    frcReference : String

open FRCState public

record CompressionState : Set₁ where
  constructor compression-state
  field
    before after : FRCState
    VolumeReduction DensityIncrease TemperatureIncrease MagneticCompression : Set
    compressionReference : String

open CompressionState public

record FusionAdmissibility (state : FRCState) : Set₁ where
  constructor fusion-admissibility
  field
    FuelSpecies : Set
    DensityTemperatureConfinementReceipt : Set
    ReactionRateReceipt : Set
    admissibilityReference : String

open FusionAdmissibility public

record FusionEvent (state : FRCState) : Set₁ where
  constructor fusion-event
  field
    admissible : FusionAdmissibility state
    FusionProducts : Set
    ReleasedFusionEnergy : Set
    eventReference : String

open FusionEvent public

------------------------------------------------------------------------
-- BIDI firewalls.
------------------------------------------------------------------------

record FRCFusionBoundary : Set where
  constructor frc-fusion-boundary
  field
    frcTopologyAloneImpliesFusion : Bool
    frcTopologyAloneImpliesFusionIsFalse : frcTopologyAloneImpliesFusion ≡ false

    compressionAloneImpliesFusion : Bool
    compressionAloneImpliesFusionIsFalse : compressionAloneImpliesFusion ≡ false

    fusionRequiresStateIndexedAdmissibility : Bool
    fusionRequiresStateIndexedAdmissibilityIsTrue :
      fusionRequiresStateIndexedAdmissibility ≡ true

    frcCanBeUsedWithoutFusion : Bool
    frcCanBeUsedWithoutFusionIsTrue : frcCanBeUsedWithoutFusion ≡ true

canonicalFRCFusionBoundary : FRCFusionBoundary
canonicalFRCFusionBoundary =
  frc-fusion-boundary false refl false refl true refl true refl
