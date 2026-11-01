module DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopySourceReplayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopyBidiExact as M

------------------------------------------------------------------------
-- SOURCE-EXACT REPLAY COORDINATES
-- Terry et al., J. Phys. Chem. A 128 (2024) 7137-7144,
-- DOI 10.1021/acs.jpca.4c03552, PMID 39150465.
------------------------------------------------------------------------

record MaiwaldValineSourceReplay : Set where
  constructor maiwald-valine-source-replay
  field
    sourceReference : String
    molecularObject : String
    lowerWavenumberCmInv : Nat
    upperWavenumberCmInv : Nat
    n2OptimalTagTemperatureK : Nat
    ch4OptimalTagTemperatureK : Nat
    highlightedFeatureCmInv : Nat
    structuralInference : String
    n2IntensityObservation : String
    sourceBackedMechanisticExplanation : String
    rawSpectrumArrayPaid : Bool
    calibrationFilePaid : Bool

open MaiwaldValineSourceReplay public

sourceExactMaiwaldValineReplay : MaiwaldValineSourceReplay
sourceExactMaiwaldValineReplay = maiwald-valine-source-replay
  "DOI 10.1021/acs.jpca.4c03552; PMID 39150465"
  "messenger-tagged protonated valine, ValH+; N2 and CH4 messenger tags"
  1000
  1900
  30
  60
  1773
  "comparison with calculated IR spectra supports trans configuration of the carboxylic-acid hydroxyl and protonated amine groups"
  "measured N2-tagged ValH+ intensities are strongly suppressed except for the highest-frequency feature at 1773 cm^-1"
  "source attributes the differing action response to stronger N2 messenger-tag binding relative to CH4, supported by calculations/rate estimates"
  false
  false

existingExperiment : M.ActionSpectroscopyExperiment
existingExperiment = M.maiwaldSURP

sourceReplayPaysExactSpectralWindow : Bool
sourceReplayPaysExactSpectralWindow = true

sourceReplayPaysExactTagTemperatures : Bool
sourceReplayPaysExactTagTemperatures = true

sourceReplayPaysSyntheticSpectrumReplacement : Bool
sourceReplayPaysSyntheticSpectrumReplacement = false

sourceReplayPaysBiosignatureDetection : Bool
sourceReplayPaysBiosignatureDetection = false
