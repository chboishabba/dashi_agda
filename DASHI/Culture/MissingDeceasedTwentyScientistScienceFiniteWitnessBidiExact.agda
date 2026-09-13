module DASHI.Culture.MissingDeceasedTwentyScientistScienceFiniteWitnessBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistScienceCapabilityBidiExact as B
import DASHI.ComputerScience.ChenShumingGraphHardwareVerificationFiniteWitnessExact as Chen
import DASHI.Physics.Materials.ZhouGuangyuanPolyimideAerogelFiniteWitnessExact as Zhou
import DASHI.ComputerScience.LiuDonghaoDSMMFiniteWitnessExact as Liu
import DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastFiniteWitnessExact as ZhangX
import DASHI.Control.ZhangDaibingUAVControlFiniteWitnessExact as ZhangD
import DASHI.Biology.LiMinyongPhotopharmacologyFiniteWitnessExact as Li
import DASHI.Physics.Nuclear.LeBlancFSPICFiniteWitnessExact as LeBlanc
import DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopyFiniteWitnessExact as Maiwald
import DASHI.Physics.Planetary.HicksSmallBodyPhotometryFiniteWitnessExact as Hicks
import DASHI.Biology.JasonThomasSignallingFiniteWitnessExact as Thomas
import DASHI.Physics.ExoticGravity.NingLiYBCOApparatusComparisonFiniteWitnessExact as Ning
import DASHI.GameTheory.FengYangheClassificationFiniteWitnessExact as Feng
import DASHI.Physics.Materials.FangDainingInverseDesignFiniteWitnessExact as Fang
import DASHI.Physics.Aerospace.YanHongThermalExcitationFiniteWitnessExact as Yan

------------------------------------------------------------------------
-- FINITE-WITNESS ADAPTER INTO THE TWENTY-SCIENTIST BIDI
------------------------------------------------------------------------

data FiniteScienceWitness : Set where
  chenWitness : Chen.FiniteChenVerificationWitness → FiniteScienceWitness
  zhouWitness : Zhou.FiniteZhouAerogelWitness → FiniteScienceWitness
  liuWitness : Liu.FiniteLiuDSMMWitness → FiniteScienceWitness
  zhangXiaoxinWitness : ZhangX.FiniteZhangXiaoxinForecastWitness → FiniteScienceWitness
  zhangDaibingWitness : ZhangD.FiniteZhangDaibingControlWitness → FiniteScienceWitness
  liMinyongWitness : Li.FiniteLiMinyongPhotopharmWitness → FiniteScienceWitness
  leblancWitness : LeBlanc.FiniteLeBlancFSPICWitness → FiniteScienceWitness
  maiwaldWitness : Maiwald.FiniteMaiwaldActionWitness → FiniteScienceWitness
  hicksWitness : Hicks.FiniteHicksPhotometryWitness → FiniteScienceWitness
  thomasWitness : Thomas.FiniteThomasSignallingWitness → FiniteScienceWitness
  ningWitness : Ning.FiniteNingApparatusWitness → FiniteScienceWitness
  fengWitness : Feng.FiniteFengClassificationWitness → FiniteScienceWitness
  fangWitness : Fang.FiniteFangInverseDesignWitness → FiniteScienceWitness
  yanWitness : Yan.FiniteYanThermalExcitationWitness → FiniteScienceWitness

data FiniteWitnessEpistemicState : Set where
  sourceExactFiniteDatum : FiniteWitnessEpistemicState
  sourceExactCoordinatesWithSyntheticPayload : FiniteWitnessEpistemicState
  syntheticMechanismReconstruction : FiniteWitnessEpistemicState

record FiniteScienceWitnessBinding : Set where
  constructor finite-science-witness-binding
  field
    person : String
    fibre : B.ScientistTechnologyFibre
    witness : FiniteScienceWitness
    epistemicState : FiniteWitnessEpistemicState
    sourceReference : String
    whatItPays : String
    reverseReplacementLeaf : String

open FiniteScienceWitnessBinding public

chenFiniteBinding : FiniteScienceWitnessBinding
chenFiniteBinding = finite-science-witness-binding
  "Chen Shuming" B.chenShumingFibre
  (chenWitness Chen.finiteChenVerificationWitness)
  syntheticMechanismReconstruction
  "DOI 10.1155/2018/6398616"
  "Pays that the published stage topology can inhabit a finite verification carrier; does not reproduce paper numerics or processor deployment."
  "replace synthetic counts with source graph semantics, stimulus corpus, coverage metric and mismatch oracle"

zhouFiniteBinding : FiniteScienceWitnessBinding
zhouFiniteBinding = finite-science-witness-binding
  "Zhou Guangyuan" B.zhouGuangyuanFibre
  (zhouWitness Zhou.finiteZhouAerogelWitness)
  sourceExactFiniteDatum
  "DOI 10.1016/j.cej.2023.147642"
  "Carries the source-reported SI thermal datum and reported finite structure/property coordinates."
  "recover a multi-sample source table and synthesis/process-window relation before scale-up claims"

liuFiniteBinding : FiniteScienceWitnessBinding
liuFiniteBinding = finite-science-witness-binding
  "Liu Donghao" B.liuDonghaoFibre
  (liuWitness Liu.finiteLiuDSMMWitness)
  syntheticMechanismReconstruction
  "GB/T 37988-2019 context; Liu institutional DSMM work"
  "Pays a finite lifecycle/evidence maturity-assessment shape only."
  "replace synthetic evidence counts with Liu-authored rubric/scoring and one source-exact assessment"

zhangXiaoxinFiniteBinding : FiniteScienceWitnessBinding
zhangXiaoxinFiniteBinding = finite-science-witness-binding
  "Zhang Xiaoxin" B.zhangXiaoxinFibre
  (zhangXiaoxinWitness ZhangX.finiteZhangXiaoxinForecastWitness)
  syntheticMechanismReconstruction
  "DOI 10.1029/2023SW003522"
  "Pays a finite carrier through whitening, CEEMDAN, CWT, prediction and validation stages; source hyperparameters remain unpaid."
  "replace synthetic series with source dataset, parameters, prediction rule and validation metrics"

zhangDaibingFiniteBinding : FiniteScienceWitnessBinding
zhangDaibingFiniteBinding = finite-science-witness-binding
  "Zhang Daibing" B.zhangDaibingFibre
  (zhangDaibingWitness ZhangD.finiteZhangDaibingControlWitness)
  syntheticMechanismReconstruction
  "DOI 10.11887/j.cn.201801023; DOI 10.13700/j.bh.1001-5965.2016.0679; DOI 10.13973/j.cnki.robot.2017.0160"
  "Pays a finite sensing-to-guidance/control mechanism carrier, not one source flight reproduction."
  "select one DOI and replace synthetic counts with source dynamics, gains, geometry and error metrics"

liMinyongFiniteBinding : FiniteScienceWitnessBinding
liMinyongFiniteBinding = finite-science-witness-binding
  "Li Minyong" B.liMinyongFibre
  (liMinyongWitness Li.finiteLiMinyongPhotopharmWitness)
  syntheticMechanismReconstruction
  "DOI 10.1002/med.22120; CN201110101082.5; CN201110100874.0"
  "Pays a finite reversible light-state/binding/readout mechanism shape, not compound-specific efficacy."
  "replace synthetic states with one exact molecule/probe wavelength, affinity, dose, readout and kinetics"

leblancFiniteBinding : FiniteScienceWitnessBinding
leblancFiniteBinding = finite-science-witness-binding
  "Joshua Kyle LeBlanc" B.joshuaLeBlancFibre
  (leblancWitness LeBlanc.finiteLeBlancFSPICWitness)
  sourceExactFiniteDatum
  "NASA NTRS 20250008475"
  "Carries the source-exact notional in-core environmental envelope and sensor/function family; does not pay flight qualification."
  "acquire device-level candidate, qualification, failure and autonomous-response evidence"

maiwaldFiniteBinding : FiniteScienceWitnessBinding
maiwaldFiniteBinding = finite-science-witness-binding
  "Frank W. Maiwald" B.frankMaiwaldFibre
  (maiwaldWitness Maiwald.finiteMaiwaldActionWitness)
  sourceExactCoordinatesWithSyntheticPayload
  "JPL FY23 SURP; DOI 10.1021/acs.jpca.4c03552"
  "Carries source-exact target/trap bounds and stage topology with a synthetic finite action spectrum."
  "replace synthetic bins with source-exact tagged-ion action spectrum, calibration and isomer-reference comparison"

hicksFiniteBinding : FiniteScienceWitnessBinding
hicksFiniteBinding = finite-science-witness-binding
  "Michael David Hicks" B.michaelHicksFibre
  (hicksWitness Hicks.finiteHicksPhotometryWitness)
  syntheticMechanismReconstruction
  "Hicks small-body publication corpus"
  "Pays a finite multi-sample photometry/phase inference shape only."
  "select one source lightcurve and add viewing geometry/calibration before physical inference"

thomasFiniteBinding : FiniteScienceWitnessBinding
thomasFiniteBinding = finite-science-witness-binding
  "Jason R. Thomas" B.jasonThomasFibre
  (thomasWitness Thomas.finiteThomasSignallingWitness)
  syntheticMechanismReconstruction
  "DOI 10.1021/acschembio.7b01060; DOI 10.1038/ncb3053"
  "Pays a finite perturbation/readout/target-validation shape while keeping screen hit separate from validated mechanism."
  "replace synthetic assay counts with one Thomas-authored assay plus target-deconvolution and ferritinophagy validation receipts"

ningFiniteBinding : FiniteScienceWitnessBinding
ningFiniteBinding = finite-science-witness-binding
  "Ning Li" B.ningLiFibre
  (ningWitness Ning.finiteNingApparatusWitness)
  sourceExactFiniteDatum
  "DOI 10.1016/S0921-4534(97)01462-7; NASA NTRS 19990019627"
  "Carries a source-exact static-versus-rotating apparatus/regime comparison and both published null/no-positive-effect outcomes."
  "recover later AC Gravity apparatus identity, controls and Army continuity before any programme promotion"

fengFiniteBinding : FiniteScienceWitnessBinding
fengFiniteBinding = finite-science-witness-binding
  "Feng Yanghe" B.fengYangheFibre
  (fengWitness Feng.finiteFengClassificationWitness)
  syntheticMechanismReconstruction
  "NUDT Press ISBN 978-7-5673-0533-5; ISBN 978-7-5673-0611-0"
  "Pays a finite noisy-label/attribute-filtering classifier shape only."
  "replace synthetic sample counts with source model equations/data and independently test any War Skull software weld"

fangFiniteBinding : FiniteScienceWitnessBinding
fangFiniteBinding = finite-science-witness-binding
  "Fang Daining" B.fangDainingFibre
  (fangWitness Fang.finiteFangInverseDesignWitness)
  syntheticMechanismReconstruction
  "DOI 10.1016/j.jmps.2025.106144"
  "Pays a finite prescribed-mode/dispersion inverse-design shape with an explicit negative-group-velocity coordinate."
  "replace synthetic mode/dispersion counts with source energy functional, geometry and experimental band structure"

yanFiniteBinding : FiniteScienceWitnessBinding
yanFiniteBinding = finite-science-witness-binding
  "Yan Hong" B.yanHongFibre
  (yanWitness Yan.finiteYanThermalExcitationWitness)
  syntheticMechanismReconstruction
  "DOI 10.7638/kqdlxxb-2013.0102"
  "Pays a finite actuator/power/distance-to-shock response coordinate shape for the source-described Mach-5 study."
  "replace synthetic indices with source heat-release, actuator geometry and shock/separation response values"

finiteScienceWitnessBindings : List FiniteScienceWitnessBinding
finiteScienceWitnessBindings =
  chenFiniteBinding ∷ zhouFiniteBinding ∷ liuFiniteBinding ∷
  zhangXiaoxinFiniteBinding ∷ zhangDaibingFiniteBinding ∷ liMinyongFiniteBinding ∷
  leblancFiniteBinding ∷ maiwaldFiniteBinding ∷ hicksFiniteBinding ∷ thomasFiniteBinding ∷
  ningFiniteBinding ∷ fengFiniteBinding ∷ fangFiniteBinding ∷ yanFiniteBinding ∷ []

finiteScienceWitnessBindingsCount : Nat
finiteScienceWitnessBindingsCount = 14

sourceExactAndSyntheticWitnessesRemainDistinct : Bool
sourceExactAndSyntheticWitnessesRemainDistinct = true

syntheticFiniteWitnessCannotPaySourceReplication : Bool
syntheticFiniteWitnessCannotPaySourceReplication = false

finiteWitnessCannotPayHistoricalDeployment : Bool
finiteWitnessCannotPayHistoricalDeployment = false

finiteWitnessCannotPayCommonProgramme : Bool
finiteWitnessCannotPayCommonProgramme = false

finiteWitnessCanRefineReverseAcquisition : Bool
finiteWitnessCanRefineReverseAcquisition = true
