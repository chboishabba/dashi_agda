module DASHI.Physics.Photovoltaic.PV369FourJunctionOpticsToMeasuredIVExact where

-- P5/P7 reuse-first finite photon and electrical source boundary.
-- No empirical EQE, IV, MPP, multijunction device or 369-specific
-- material improvement is constructed by the synthetic Nat fixture.
-- Original owners: site fibre (LES), semiconductor continuity,
-- Scharfetter-Gummel device flux, PV signed work, G173 model loss frontier.
-- No ESD source edited. Agda Golden native acceptance OPEN.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Photovoltaic.PVPrimaryConversionMaxCutExact as PV
import DASHI.Physics.Photovoltaic.PV369NetHalfThresholdExact as Net
import DASHI.Physics.Photovoltaic.PV369G173MultiJunctionLossFrontierExact as Frontier
import DASHI.Physics.Semiconductor.Device.SpatialContinuityRecombinationExact as Continuity
import DASHI.Physics.Semiconductor.Device.FiniteScharfetterGummelFluxExact as SG
import DASHI.Environment.SolarOpticalSiteFibreCrossPollinationExact as Site
import DASHI.Environment.CanopySpectralRadiativeTransferExact as Canopy

-- At each photon wavelength/bin the optical source must be partitioned
-- EXCLUSIVELY into reflected, four junction absorptions and transmitted.
-- This is a photon COUNT identity; it is not an energy or charge equality.
record FourJunctionPhotonBin : Set where
  field
    incident reflected transmitted : Nat
    absorbed1 absorbed2 absorbed3 absorbed4 : Nat
    photonPartition :
      incident ≡ reflected +
        (absorbed1 + (absorbed2 +
        (absorbed3 + (absorbed4 + transmitted))))

    -- Collected electron counts under the same illumination, individually
    -- bounded by the photons absorbed in that junction. There is no
    -- multiplication in this baseline: P4 multiplication uses separate
    -- source-owned signed mechanism evidence, not fake EQE>absorption.
    collected1 collected2 collected3 collected4 : Nat
    eqe1 : Bound._≤_ collected1 absorbed1
    eqe2 : Bound._≤_ collected2 absorbed2
    eqe3 : Bound._≤_ collected3 absorbed3
    eqe4 : Bound._≤_ collected4 absorbed4

-- Purely finite self-test for four exclusive absorbers, 100 photon units.
fourJunctionSyntheticPhotonFixture : FourJunctionPhotonBin
fourJunctionSyntheticPhotonFixture = record
  { incident = 100
  ; reflected = 10
  ; transmitted = 10
  ; absorbed1 = 20
  ; absorbed2 = 20
  ; absorbed3 = 20
  ; absorbed4 = 20
  ; photonPartition = refl
  ; collected1 = 16
  ; collected2 = 16
  ; collected3 = 16
  ; collected4 = 16
  ; eqe1 = Bound.≤-append 16 4
  ; eqe2 = Bound.≤-append 16 4
  ; eqe3 = Bound.≤-append 16 4
  ; eqe4 = Bound.≤-append 16 4
  }

-- The same incident flux cannot be counted four times. The source
-- partition is *not* implied by 4 independently normalized IV curves.
record OpticalToTerminalSourceWeld : Set₂ where
  field
    SiteId Spectrum Direction Temperature Shading Soiling Wind Humidity : Set

    measuredSolarSite :
      Site.SolarOpticalSiteFibre SiteId Spectrum Direction Temperature
        Shading Soiling Wind Humidity

    Wavelength : Set
    wavelengthResolvedPhotonReceipt : Wavelength -> FourJunctionPhotonBin

    measuredReflectanceTransmittance : Set
    originalMeasuredOptics : measuredReflectanceTransmittance

    fourDistinctJunctionEQEUnderSameSource : Set
    measuredEQE : fourDistinctJunctionEQEUnderSameSource

    sameSampleMeasuredIlluminatedJV : Set
    measuredFourIVCurves : sameSampleMeasuredIlluminatedJV

    continuousMeasuredCarrierTransport : Set
    sourceCurrentContinuity : continuousMeasuredCarrierTransport

    explicitlySourceMatchedOpticalJsc : Set
    eqeAndIVShortCircuitMatch : explicitlySourceMatchedOpticalJsc

    experimentallyVerifiedConvertersAndAuxiliaries : Set
    converterAndAuxiliaryEvidence : experimentallyVerifiedConvertersAndAuxiliaries

    sameSourceNetElectricDevice : Net.NetSolarElectricPVAcceptance

-- The interface does not identify Canopy light transport with PV absorbers,
-- nor the SG finite fixture with an actual diode mobility/current law.
-- Sourced spectral geometry, direction, contacts and device physics are
-- mandatory producer responsibilities beyond the finite bookkeeping.
