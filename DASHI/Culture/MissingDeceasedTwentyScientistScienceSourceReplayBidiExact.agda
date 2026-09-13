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
import DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopySourceReplayDepthExact as MD
import DASHI.Physics.Materials.ZhouGuangyuanAerogelProcessPropertySourceReplayExact as ZH
import DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastSourceReplayDepthExact as ZXD
import DASHI.Physics.Astrophysics.GrillmairStellarStreamSourceReplayExact as G
import DASHI.Physics.Planetary.HicksSmallBodyPhotometrySourceReplayExact as H

------------------------------------------------------------------------
-- SOURCE-EXACT REPLAY ADAPTER
-- Source-exposed finite coordinates remain distinct from hidden arrays/code,
-- operational qualification, person possession, programme identity and events.
------------------------------------------------------------------------

data SourceReplayWitness : Set where
  zhangForecastReplay : ZX.ZhangForecastSourceReplay → SourceReplayWitness
  maiwaldValineReplay : M.MaiwaldValineSourceReplay → SourceReplayWitness
  fangInverseDesignReplay : F.FangInverseDesignSourceReplay → SourceReplayWitness
  yanThermalReplay : Y.YanThermalSourceReplay → SourceReplayWitness
  maiwaldDepthWitness : MD.MaiwaldDepthReplay → SourceReplayWitness
  zhouProcessPropertyWitness : ZH.ZhouProcessPropertyReplay → SourceReplayWitness
  zhangForecastDepthWitness : ZXD.ZhangForecastDepthReplay → SourceReplayWitness
  grillmairStreamWitness : G.GrillmairStreamReplay → SourceReplayWitness
  hicksPhotometryWitness : H.HicksPhotometryReplay → SourceReplayWitness

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

maiwaldDepthBinding : SourceReplayBinding
maiwaldDepthBinding = source-replay-binding
  "Frank W. Maiwald" B.frankMaiwaldFibre
  (maiwaldDepthWitness MD.maiwaldDepthReplay)
  "DOI 10.1021/acs.jpca.4c03552; ACS Supporting Information"
  "supporting-information inventory narrows the remaining replay to raw experimental intensities/calibration rather than unknown supplementary content"
  "raw experimental intensity array, absolute calibration and data/notebook custody"

zhouReplayBinding : SourceReplayBinding
zhouReplayBinding = source-replay-binding
  "Zhou Guangyuan" B.zhouGuangyuanFibre
  (zhouProcessPropertyWitness ZH.zhouProcessPropertyReplay)
  "DOI 10.1016/j.cej.2023.147642"
  "finite source property portfolio: 7.7% minimum shrinkage, >91% porosity, 674.8 m2/g surface area, Td5% >580 C, Tg >299 C, 54.3 mW m^-1 K^-1 at 200 C"
  "exact multi-sample table, synthesis recipe, uncertainty/batch variation and scale-up window"

zhangDepthBinding : SourceReplayBinding
zhangDepthBinding = source-replay-binding
  "Zhang Xiaoxin" B.zhangXiaoxinFibre
  (zhangForecastDepthWitness ZXD.zhangForecastDepthReplay)
  "DOI 10.1029/2023SW003522"
  "finite count witness for reported 77.7% recall: 129 correctly predicted of 166 storm events, within 229-event carrier"
  "CEEMDAN/CWT hyperparameters, precursor quantisation, runnable source code/data and operational threshold"

grillmairReplayBinding : SourceReplayBinding
grillmairReplayBinding = source-replay-binding
  "Carl J. Grillmair" B.carlGrillmairFibre
  (grillmairStreamWitness G.grillmairStreamReplay)
  "DOI 10.3847/1538-4357/aa8872; arXiv:1708.09029"
  "four stream candidates at ~20 kpc; 13-95 deg / 5-33 kpc lengths; 100-300 pc widths; 3000-8000 stars; Molonglo ~2.5 deg from ATLAS"
  "exact catalogue slice, matched-filter weights, distance scan and orbit-fit uncertainty"

hicksReplayBinding : SourceReplayBinding
hicksReplayBinding = source-replay-binding
  "Michael David Hicks" B.michaelHicksFibre
  (hicksPhotometryWitness H.hicksPhotometryReplay)
  "NASA/JPL CNEOS Florence campaign, 2017-09-11"
  "Hicks/Buratti Table Mountain lightcurve participation on 2017-08-30; multi-observer optical rotation estimate 2.4 h consistent with radar"
  "Hicks lightcurve array, viewing geometry, photometric calibration and reduction state"

sourceReplayBindings : List SourceReplayBinding
sourceReplayBindings =
  zhangReplayBinding ∷ maiwaldReplayBinding ∷ fangReplayBinding ∷ yanReplayBinding ∷
  maiwaldDepthBinding ∷ zhouReplayBinding ∷ zhangDepthBinding ∷
  grillmairReplayBinding ∷ hicksReplayBinding ∷ []

sourceReplayBindingsCount : Nat
sourceReplayBindingsCount = 9

sourceReplayRefinesSyntheticFiniteWitness : Bool
sourceReplayRefinesSyntheticFiniteWitness = true

sourceReplayDoesNotPayHistoricalDeployment : Bool
sourceReplayDoesNotPayHistoricalDeployment = false

sourceReplayDoesNotPayPersonPossession : Bool
sourceReplayDoesNotPayPersonPossession = false

sourceReplayDoesNotPayCommonProgramme : Bool
sourceReplayDoesNotPayCommonProgramme = false
