module DASHI.Physics.Photovoltaic.PVPrimaryConversionMaxCutExact where

-- PV-FIRST convergence toward 369/optical/quantum conversion.
-- Thermal is an auxiliary port. This source is not Agda-kernel accepted,
-- is not measured material physics and does not prove >50% efficiency.

open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Photovoltaic.C3OpticalWorkBoundaryExact as C3Optical
import DASHI.Physics.Semiconductor.Device.DriftDiffusionContinuityExact as Carrier

-- All entries are in one common ENERGY grid, not photon/electron counts.
-- Exported excitation is distinct from the still-stored final inventory.
record PVPrimaryEnergyWindow : Set where
  constructor pvPrimaryEnergyWindow
  field
    incidentSolar suppliedRFDrive initialStored : Nat
    exportedElectrical exportedChemical excitationExport : Nat
    thermalOutput escapingLight recoveredRFDrive finalStored : Nat
    firstLaw :
      (incidentSolar + suppliedRFDrive) + initialStored
      ≡ exportedElectrical +
        (exportedChemical + (excitationExport +
        (thermalOutput + (escapingLight +
        (recoveredRFDrive + finalStored)))))

open PVPrimaryEnergyWindow public

sourceAndDriverAvailable : PVPrimaryEnergyWindow -> Nat
sourceAndDriverAvailable w =
  (incidentSolar w + suppliedRFDrive w) + initialStored w

electricalWorkBound :
  (w : PVPrimaryEnergyWindow) ->
  Bound._≤_ (exportedElectrical w) (sourceAndDriverAvailable w)
electricalWorkBound w =
  Bound.transportUpper (Bound.sym (firstLaw w))
    (Bound.≤-append (exportedElectrical w)
      (exportedChemical w + (excitationExport w +
      (thermalOutput w + (escapingLight w +
      (recoveredRFDrive w + finalStored w))))))

-- Photon and electron COUNTS are not measured electrical work.
-- Multiple excitons per photon are permitted but do not imply power gain.
record PhotonToChargeWindow : Set where
  constructor photonToChargeWindow
  field
    incidentPhotons absorbedPhotons escapedPhotons : Nat
    photonPartition : incidentPhotons ≡ absorbedPhotons + escapedPhotons
    generatedPairs additionalPairsViaMultiplication baseExcitationPairs : Nat
    pairMechanism :
      generatedPairs ≡ baseExcitationPairs + additionalPairsViaMultiplication
    oneDirectPairPerAbsorbedPhotonMax :
      Bound._≤_ baseExcitationPairs absorbedPhotons
    collectedCarriers recombinedCarriers trappedCarriers finalCarrierInventory : Nat
    pairCollection :
      generatedPairs ≡
      collectedCarriers + (recombinedCarriers +
      (trappedCarriers + finalCarrierInventory))

open PhotonToChargeWindow public

collectedCannotExceedGenerated :
  (w : PhotonToChargeWindow) ->
  Bound._≤_ (collectedCarriers w) (generatedPairs w)
collectedCannotExceedGenerated w =
  Bound.transportUpper (Bound.sym (pairCollection w))
    (Bound.≤-append (collectedCarriers w)
      (recombinedCarriers w + (trappedCarriers w + finalCarrierInventory w)))

-- The CALIBRATED SAME MATERIAL bridge is not inferred from a DOI or an
-- abstract C3 representation. No witness is supplied by this file.
record SameMaterialConversionAdmission : Set₁ where
  field
    atomicOpticalBridge : C3Optical.SameMaterialOpticalAdmission
    carrierContinuityReceipt : Carrier.CarrierContinuity
    opticalTransitionSource bandgapOrDotLevelSource : String
    carrierMobilityAndLifetimeSource matchedDeviceGeometrySource : String
    timeResolvedRFAndPhotonSource sameCellCurrentVoltageSource : String
    independentReplicationSource : String

-- Matched static-versus-driven net electric gain needs exact same sunlight
-- and reservoir boundary, then signed RF electricity supplied AND recovered.
-- Proving this predicate requires a physical instrumented matched-pair
-- witness; no value is asserted by the type.
record MatchedDrivenPVGain : Set where
  field
    passive driven : PVPrimaryEnergyWindow
    sameSolar : incidentSolar passive ≡ incidentSolar driven
    sameInitialStore : initialStored passive ≡ initialStored driven
    sameFinalStore : finalStored passive ≡ finalStored driven
    sameApertureAndSpectrum sameCellAndTimeWindow : String
    -- Strict benefit, not merely a tie. The previous weak <= proof
    -- erroneously admitted equal-output/equal-drive controls.
    positiveNetElectricalGain :
      Bound._≤_
        (suc (exportedElectrical passive +
         (recoveredRFDrive passive + suppliedRFDrive driven)))
        (exportedElectrical driven +
         (recoveredRFDrive driven + suppliedRFDrive passive))
