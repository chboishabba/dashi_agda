module DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopySourceReplayDepthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopySourceReplayExact as Base

record MaiwaldDepthReplay : Set where
  constructor maiwald-depth-replay
  field
    sourceReference : String
    lowerWavenumberCmInv upperWavenumberCmInv : Nat
    n2OptimalTagTemperatureK ch4OptimalTagTemperatureK : Nat
    highlightedFeatureCmInv : Nat
    supportingInformationInventory : String
    dissociationTimeFigurePresent : Bool
    atomicCoordinateTablesPresent : Bool
    vibrationalFrequencyTablePresent : Bool
    rawExperimentalIntensityArrayPaid : Bool
    absoluteCalibrationPaid : Bool

open MaiwaldDepthReplay public

maiwaldDepthReplay : MaiwaldDepthReplay
maiwaldDepthReplay = maiwald-depth-replay
  "DOI 10.1021/acs.jpca.4c03552; ACS Supporting Information"
  1000 1900 30 60 1773
  "SI exposes calculated spectra/structures, IR photodissociation-time figure, atomic-coordinate tables and unscaled vibrational-frequency table"
  true true true false false

baseReplay : Base.MaiwaldValineSourceReplay
baseReplay = Base.sourceExactMaiwaldValineReplay

supportingInformationNarrowsReverseLeaf : Bool
supportingInformationNarrowsReverseLeaf = true

supportingInformationInventoryEqualsRawSpectrum : Bool
supportingInformationInventoryEqualsRawSpectrum = false

sourceCoordinatesPayBiosignatureInference : Bool
sourceCoordinatesPayBiosignatureInference = false
