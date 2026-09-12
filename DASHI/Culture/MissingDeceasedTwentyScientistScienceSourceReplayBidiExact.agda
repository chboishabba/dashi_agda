module DASHI.Culture.MissingDeceasedTwentyScientistScienceSourceReplayBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistScienceCapabilityBidiExact as B
import DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastSourceReplayExact as ZX
import DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopySourceReplayExact as M
import DASHI.Physics.Materials.FangDainingInverseDesignSourceReplayExact as F
import DASHI.Physics.Aerospace.YanHongThermalExcitationSourceReplayExact as Y

------------------------------------------------------------------------
-- SOURCE-EXACT REPLAY ADAPTER
-- These bindings refine earlier synthetic finite witnesses using source-exposed
-- finite coordinates. They still do not pay hidden arrays, full source code,
-- operational qualification, person possession, programme identity or events.
------------------------------------------------------------------------

data SourceReplayWitness : Set where
  zhangForecastReplay : ZX.ZhangForecastSourceReplay → SourceReplayWitness
  maiwaldValineReplay : M.MaiwaldValineSourceReplay → SourceReplayWitness
  fangInverseDesignReplay : F.FangInverseDesignSourceReplay → SourceReplayWitness
  yanThermalReplay : Y.YanThermalSourceReplay → SourceReplayWitness

record SourceReplayBinding : Set where
  constructor source-replay-binding
  field
    person : String
    fibre : B.ScientistTechnologyFibre
    replay : SourceReplayWitness
    sourceReference : String
    promotedCoordinate : String
    stillUnpaid : String

open SourceReplayBinding public

zhangReplayBinding : SourceReplayBinding
zhangReplayBinding = source-replay-binding
  "Zhang Xiaoxin" B.zhangXiaoxinFibre
  (zhangForecastReplay ZX.sourceExactZhangForecastReplay)
  "DOI 10.1029/2023SW003522"
  "229-event Oulu carrier; 166 Kp>=5, 63 Kp<5; 129/166 accurate; IMF4+IMF5; 4-24 h source timescale"
  "exact whitening/CEEMDAN/CWT hyperparameters, precursor quantisation rule, code/runtime and operational threshold"

maiwaldReplayBinding : SourceReplayBinding
maiwaldReplayBinding = source-replay-binding
  "Frank W. Maiwald" B.frankMaiwaldFibre
  (maiwaldValineReplay M.sourceExactMaiwaldValineReplay)
  "DOI 10.1021/acs.jpca.4c03552; PMID 39150465"
  "1000-1900 cm^-1 ValH+ action spectrum; N2 30 K; CH4 60 K; 1773 cm^-1 highlighted feature and tag-response distinction"
  "raw spectrum array, absolute/normalised intensities, calibration files, dissociation-time table and dataset custody"

fangReplayBinding : SourceReplayBinding
fangReplayBinding = source-replay-binding
  "Fang Daining" B.fangDainingFibre
  (fangInverseDesignReplay F.sourceExactFangInverseDesignReplay)
  "DOI 10.1016/j.jmps.2025.106144"
  "source-exact force-field-induced energy design objective and experimentally verified negative-group-velocity dispersion claim"
  "complete energy functional, unit-cell geometry, material constants, computed/experimental band arrays and project/code custody"

yanReplayBinding : SourceReplayBinding
yanReplayBinding = source-replay-binding
  "Yan Hong" B.yanHongFibre
  (yanThermalReplay Y.sourceExactYanThermalReplay)
  "DOI 10.7638/kqdlxxb-2013.0102"
  "four source-exact Mach-5 thermal-actuator cases with E/N/S coordinates and source qualitative response ordering"
  "shock-angle/separation curves, geometry/mesh/boundary conditions, heat-source model, solver settings and project custody"

sourceReplayBindings : List SourceReplayBinding
sourceReplayBindings =
  zhangReplayBinding ∷ maiwaldReplayBinding ∷ fangReplayBinding ∷ yanReplayBinding ∷ []

sourceReplayBindingsCount : Nat
sourceReplayBindingsCount = 4

sourceReplayRefinesSyntheticFiniteWitness : Bool
sourceReplayRefinesSyntheticFiniteWitness = true

sourceReplayDoesNotPayHistoricalDeployment : Bool
sourceReplayDoesNotPayHistoricalDeployment = false

sourceReplayDoesNotPayPersonPossession : Bool
sourceReplayDoesNotPayPersonPossession = false

sourceReplayDoesNotPayCommonProgramme : Bool
sourceReplayDoesNotPayCommonProgramme = false
