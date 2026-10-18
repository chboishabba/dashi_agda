module DASHI.Physics.Foundations.RFComplexSmithCabarlahCSICrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.RFComplexSmithPhasedArrayGoniometerExact as RF
import DASHI.Physics.Foundations.CSIArrayGoniometerSnowballExact as CSI
import DASHI.Physics.Foundations.CabarlahGoniometerAcquisitionExact as Cabarlah

------------------------------------------------------------------------
-- CSI / PHASOR BRIDGE
--
-- Commodity CSI and RF port observations may both retain complex magnitude/
-- phase information, but neither is identified with the other hardware family.
-- The shared useful coordinate is phase-sensitive observation feeding an
-- angular consumer after sufficient spatial information is retained.
------------------------------------------------------------------------

record CSIComplexPhaseBridgeReceipt : Set where
  constructor csi-complex-phase-bridge-receipt
  field
    engineeringJReceiptRetained : RF.EngineeringJReceipt
    smithCoordinateReceiptRetained : RF.SmithChartCoordinateReceipt
    csiPhaseRefinementRetained : CSI.PhaseRefinementReceipt
    phasedArrayEndpointRetained : CSI.PhasedArrayEndpointReceipt
    goniometerEndpointRetained : CSI.GoniometerEndpointReceipt

    csiEqualsSmithChartMeasurement : Bool
    csiEqualsSmithChartMeasurementIsFalse :
      csiEqualsSmithChartMeasurement ≡ false

    csiPhaseEqualsPortSParameter : Bool
    csiPhaseEqualsPortSParameterIsFalse :
      csiPhaseEqualsPortSParameter ≡ false

    sharedComplexPhaseSupportsCommonAngularConsumer : Bool
    sharedComplexPhaseSupportsCommonAngularConsumerIsTrue :
      sharedComplexPhaseSupportsCommonAngularConsumer ≡ true

open CSIComplexPhaseBridgeReceipt public

canonicalCSIComplexPhaseBridgeReceipt : CSIComplexPhaseBridgeReceipt
canonicalCSIComplexPhaseBridgeReceipt =
  csi-complex-phase-bridge-receipt
    RF.canonicalEngineeringJReceipt
    RF.canonicalSmithChartCoordinateReceipt
    CSI.canonicalPhaseRefinementReceipt
    CSI.canonicalPhasedArrayEndpointReceipt
    CSI.canonicalGoniometerEndpointReceipt
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- CABARLAH / COMPLEX-RF BRIDGE
--
-- Cabarlah's sourced DF lineage and the complex-RF coordinate machinery can
-- coexist in one observer graph without upgrading historical capability into
-- a claim about exact hardware or a Smith-chart-equipped instrument.
------------------------------------------------------------------------

record CabarlahComplexRFBridgeReceipt : Set where
  constructor cabarlah-complex-rf-bridge-receipt
  field
    cabarlahDFAcquisitionRetained :
      Cabarlah.CabarlahDirectionFindingAcquisition

    cabarlahGoniometerBoundaryRetained :
      Cabarlah.CabarlahGoniometerBoundary

    cabarlahObserverCrossPollinationRetained :
      Cabarlah.CabarlahObserverCrossPollination

    complexPhaseArrayBridgeRetained :
      RF.PhasorArrayCrossPollinationReceipt

    cabarlahHistoricalDFImpliesSmithChartUse : Bool
    cabarlahHistoricalDFImpliesSmithChartUseIsFalse :
      cabarlahHistoricalDFImpliesSmithChartUse ≡ false

    cabarlahHistoricalDFImpliesElectronicPhasedArray : Bool
    cabarlahHistoricalDFImpliesElectronicPhasedArrayIsFalse :
      cabarlahHistoricalDFImpliesElectronicPhasedArray ≡ false

    cabarlahDFMayShareAbstractAngularObservationRole : Bool
    cabarlahDFMayShareAbstractAngularObservationRoleIsTrue :
      cabarlahDFMayShareAbstractAngularObservationRole ≡ true

open CabarlahComplexRFBridgeReceipt public

canonicalCabarlahComplexRFBridgeReceipt : CabarlahComplexRFBridgeReceipt
canonicalCabarlahComplexRFBridgeReceipt =
  cabarlah-complex-rf-bridge-receipt
    Cabarlah.canonicalCabarlahDirectionFindingAcquisition
    Cabarlah.canonicalCabarlahGoniometerBoundary
    Cabarlah.canonicalCabarlahObserverCrossPollination
    RF.canonicalPhasorArrayCrossPollinationReceipt
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- CROSS-DOMAIN FIREWALL
------------------------------------------------------------------------

record RFComplexCrossDomainFirewall : Set where
  constructor rf-complex-cross-domain-firewall
  field
    smithChartEqualsAoAPlot : Bool
    smithChartEqualsAoAPlotIsFalse :
      smithChartEqualsAoAPlot ≡ false

    sParameterEqualsBearing : Bool
    sParameterEqualsBearingIsFalse :
      sParameterEqualsBearing ≡ false

    relativePhaseEqualsEmitterIdentity : Bool
    relativePhaseEqualsEmitterIdentityIsFalse :
      relativePhaseEqualsEmitterIdentity ≡ false

    engineeringJEqualsModularJ : Bool
    engineeringJEqualsModularJIsFalse :
      engineeringJEqualsModularJ ≡ false

    cabarlahContextEqualsObservedHardwareProof : Bool
    cabarlahContextEqualsObservedHardwareProofIsFalse :
      cabarlahContextEqualsObservedHardwareProof ≡ false

open RFComplexCrossDomainFirewall public

canonicalRFComplexCrossDomainFirewall : RFComplexCrossDomainFirewall
canonicalRFComplexCrossDomainFirewall =
  rf-complex-cross-domain-firewall
    false refl
    false refl
    false refl
    false refl
    false refl
