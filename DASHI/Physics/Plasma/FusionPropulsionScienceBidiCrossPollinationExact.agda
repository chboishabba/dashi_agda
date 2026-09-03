module DASHI.Physics.Plasma.FusionPropulsionScienceBidiCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.IdealMHDReconnectionBidiExact as Reconnection
import DASHI.Physics.Plasma.FRCCompressionFusionHyperfabricExact as FRC
import DASHI.Physics.Plasma.MagneticNozzleMomentumConversionBidiExact as Nozzle

------------------------------------------------------------------------
-- SCIENCE-LEVEL BIDI CROSS-POLLINATION
--
-- The chain is typed by distinct producers.  No arrow is filled by vocabulary
-- overlap alone.
--
-- magnetic topology
--   -> non-ideal topology change (optional reconnection lane)
--   -> FRC/plasmoid state
--   -> compression
--   -> fusion admissibility/event
--   -> hot plasma / fusion products
--   -> magnetic-nozzle directed momentum conversion
--   -> thrust.
------------------------------------------------------------------------

record FusionPropulsionScienceChain : Set₁ where
  constructor fusion-propulsion-science-chain
  field
    FRCState0 FRCState1 : FRC.FRCState
    compression : FRC.CompressionState
    compressionEndsAtState1 : FRC.after compression ≡ FRCState1
    fusion : FRC.FusionEvent FRCState1

    nozzleState : Nozzle.NozzlePlasmaState
    nozzleGeometry : Nozzle.MagneticNozzleGeometry
    thrust : Nozzle.ThrustReceipt nozzleState nozzleGeometry

    fusionProductsFeedNozzleReference : String
    sameObjectEnergyTransferReference : String
    chainReference : String

open FusionPropulsionScienceChain public

------------------------------------------------------------------------
-- Reconnection is a cross-cutting topology/energy-conversion mechanism, not a
-- mandatory synonym for FRC formation, fusion, or nozzle thrust.
------------------------------------------------------------------------

record ReconnectionCrossCut : Set₁ where
  constructor reconnection-cross-cut
  field
    regime : Reconnection.PlasmaEvolutionRegime
    state : Reconnection.ReconnectionState
    receipt : Reconnection.ReconnectionReceipt regime state
    couplingTarget : String
    sameObjectCouplingStillRequired : Bool
    sameObjectCouplingStillRequiredIsTrue :
      sameObjectCouplingStillRequired ≡ true

open ReconnectionCrossCut public

record ScienceBidiBoundary : Set where
  constructor science-bidi-boundary
  field
    reconnectionImpliesFRC : Bool
    reconnectionImpliesFRCIsFalse : reconnectionImpliesFRC ≡ false

    frcImpliesFusion : Bool
    frcImpliesFusionIsFalse : frcImpliesFusion ≡ false

    fusionEnergyImpliesThrust : Bool
    fusionEnergyImpliesThrustIsFalse : fusionEnergyImpliesThrust ≡ false

    sameTheoremShapeTransfersAcrossApplications : Bool
    sameTheoremShapeTransfersAcrossApplicationsIsTrue :
      sameTheoremShapeTransfersAcrossApplications ≡ true

    foreignApplicationReceiptDischargesLocalScienceReceipt : Bool
    foreignApplicationReceiptDischargesLocalScienceReceiptIsFalse :
      foreignApplicationReceiptDischargesLocalScienceReceipt ≡ false

canonicalScienceBidiBoundary : ScienceBidiBoundary
canonicalScienceBidiBoundary =
  science-bidi-boundary false refl false refl false refl true refl false refl

------------------------------------------------------------------------
-- Reverse acquisition frontier.
-- Each observed downstream coordinate asks for its immediate same-object
-- producer, preventing a downstream engineering observation from manufacturing
-- an upstream plasma/fusion explanation.
------------------------------------------------------------------------

record ReverseScienceObligations : Set where
  constructor reverse-science-obligations
  field
    thrustNeedsMomentumConversionReceipt : Bool
    thrustNeedsMomentumConversionReceiptIsTrue :
      thrustNeedsMomentumConversionReceipt ≡ true

    momentumConversionNeedsNozzleCouplingReceipt : Bool
    momentumConversionNeedsNozzleCouplingReceiptIsTrue :
      momentumConversionNeedsNozzleCouplingReceipt ≡ true

    fusionClaimNeedsFusionAdmissibilityReceipt : Bool
    fusionClaimNeedsFusionAdmissibilityReceiptIsTrue :
      fusionClaimNeedsFusionAdmissibilityReceipt ≡ true

    reconnectionClaimNeedsFrozenInBreakingReceipt : Bool
    reconnectionClaimNeedsFrozenInBreakingReceiptIsTrue :
      reconnectionClaimNeedsFrozenInBreakingReceipt ≡ true

canonicalReverseScienceObligations : ReverseScienceObligations
canonicalReverseScienceObligations =
  reverse-science-obligations true refl true refl true refl true refl
