module DASHI.Physics.Photovoltaic.PV369NREL2017ThreeJunctionTwoGroupTopologyExact where

-- M2 actual architecture of the published NREL 35.9% mechanical stack:
-- 3 physical absorbers = GaInP, GaAs, Si; 2 *independent electrical groups*
-- = series GaInP/GaAs top tandem, and separately extracted Si bottom.
-- 4 terminals DOES NOT mean four optical junctions.
-- Source: Green et al., 2026 Version 68, Table 4;
-- original Essig et al. Nature Energy (2017), DOI 10.1038/nenergy.2017.144.
--
-- A published 4T voltage/Jsc pair is NOT an optical absorptance
-- partition and cannot be accepted as a three-junction EQE spectrum.
-- P3 RF and P4 carrier multiplication need separate non-baseline gates.
-- Agda Golden kernel acceptance OPEN.

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Photovoltaic.PVGreen68FourTerminalPublishedSourceExact as Source
import DASHI.Physics.Photovoltaic.PV369FourJunctionOpticsToMeasuredIVExact as Optical
import DASHI.Physics.Semiconductor.Device.SpatialContinuityRecombinationExact as Carrier

data OpticalJunction : Set where
  gaInP gaAs silicon : OpticalJunction

data IndependentlyContactedGroup : Set where
  seriesIIIvTop siliconSeparate : IndependentlyContactedGroup

outputGroup : OpticalJunction -> IndependentlyContactedGroup
outputGroup gaInP = seriesIIIvTop
outputGroup gaAs = seriesIIIvTop
outputGroup silicon = siliconSeparate

publishedGaInPAndGaAsShareOneSeriesOutput :
  outputGroup gaInP ≡ outputGroup gaAs
publishedGaInPAndGaAsShareOneSeriesOutput = refl

data False : Set where

publishedSiIsSeparateFromTop :
  outputGroup silicon ≡ outputGroup gaAs -> False
publishedSiIsSeparateFromTop ()

-- This is a STRUCTURAL source mapping, not a proof of actual collected
-- junction photocarriers, per-subcell current matching, or original raw IV.
record PublishedThreeJunctionTwoGroupPhysicalAdmission : Set₁ where
  field
    OriginalThreeDistinctAbsorberSpectra : Set
    originalAbsorptance : OriginalThreeDistinctAbsorberSpectra
    SourceMatchedGaInPAndGaAsSeriesJunctionJV : Set
    topSeriesCurrentMatch : SourceMatchedGaInPAndGaAsSeriesJunctionJV
    SourceMatchedSiGroupJV : Set
    siSeparatePower : SourceMatchedSiGroupJV
    CommonApertureIncidentSpectrum : Set
    measuredSameSun : CommonApertureIncidentSpectrum
    SourceMeasuredIndependentFourContactPower : Set
    sourceTotalFourTerminalPower : SourceMeasuredIndependentFourContactPower

-- Original Green68 arithmetic is checked by Source; neither the
-- synthetic finite photon fixture nor a 4-Junction 4T ideal-model
-- curve creates this physical three-absorber/two-output source record.
