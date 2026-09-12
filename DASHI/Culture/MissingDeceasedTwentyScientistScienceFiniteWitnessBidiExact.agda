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

data FiniteWitnessEpistemicState : Set where
  sourceExactFiniteDatum : FiniteWitnessEpistemicState
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
  "Chen Shuming"
  B.chenShumingFibre
  (chenWitness Chen.finiteChenVerificationWitness)
  syntheticMechanismReconstruction
  "DOI 10.1155/2018/6398616"
  "Pays that the published stage topology can inhabit a finite verification carrier; does not reproduce paper numerics or processor deployment."
  "replace synthetic counts with source graph semantics, stimulus corpus, coverage metric and mismatch oracle"

zhouFiniteBinding : FiniteScienceWitnessBinding
zhouFiniteBinding = finite-science-witness-binding
  "Zhou Guangyuan"
  B.zhouGuangyuanFibre
  (zhouWitness Zhou.finiteZhouAerogelWitness)
  sourceExactFiniteDatum
  "DOI 10.1016/j.cej.2023.147642"
  "Carries the source-reported SI thermal datum and reported finite structure/property coordinates."
  "recover a multi-sample source table and synthesis/process-window relation before scale-up claims"

liuFiniteBinding : FiniteScienceWitnessBinding
liuFiniteBinding = finite-science-witness-binding
  "Liu Donghao"
  B.liuDonghaoFibre
  (liuWitness Liu.finiteLiuDSMMWitness)
  syntheticMechanismReconstruction
  "GB/T 37988-2019 context; Liu institutional DSMM work"
  "Pays a finite lifecycle/evidence maturity-assessment shape only."
  "replace synthetic evidence counts with Liu-authored rubric/scoring and one source-exact assessment"

zhangXiaoxinFiniteBinding : FiniteScienceWitnessBinding
zhangXiaoxinFiniteBinding = finite-science-witness-binding
  "Zhang Xiaoxin"
  B.zhangXiaoxinFibre
  (zhangXiaoxinWitness ZhangX.finiteZhangXiaoxinForecastWitness)
  syntheticMechanismReconstruction
  "DOI 10.1029/2023SW003522"
  "Pays a finite carrier through whitening, CEEMDAN, CWT, prediction and validation stages; source hyperparameters remain unpaid."
  "replace synthetic series with source dataset, parameters, prediction rule and validation metrics"

zhangDaibingFiniteBinding : FiniteScienceWitnessBinding
zhangDaibingFiniteBinding = finite-science-witness-binding
  "Zhang Daibing"
  B.zhangDaibingFibre
  (zhangDaibingWitness ZhangD.finiteZhangDaibingControlWitness)
  syntheticMechanismReconstruction
  "DOI 10.11887/j.cn.201801023; DOI 10.13700/j.bh.1001-5965.2016.0679; DOI 10.13973/j.cnki.robot.2017.0160"
  "Pays a finite sensing-to-guidance/control mechanism carrier, not one source flight reproduction."
  "select one DOI and replace synthetic counts with source dynamics, gains, geometry and error metrics"

liMinyongFiniteBinding : FiniteScienceWitnessBinding
liMinyongFiniteBinding = finite-science-witness-binding
  "Li Minyong"
  B.liMinyongFibre
  (liMinyongWitness Li.finiteLiMinyongPhotopharmWitness)
  syntheticMechanismReconstruction
  "DOI 10.1002/med.22120; CN201110101082.5; CN201110100874.0"
  "Pays a finite reversible light-state/binding/readout mechanism shape, not compound-specific efficacy."
  "replace synthetic states with one exact molecule/probe wavelength, affinity, dose, readout and kinetics"

finiteScienceWitnessBindings : List FiniteScienceWitnessBinding
finiteScienceWitnessBindings =
  chenFiniteBinding ∷ zhouFiniteBinding ∷ liuFiniteBinding ∷
  zhangXiaoxinFiniteBinding ∷ zhangDaibingFiniteBinding ∷ liMinyongFiniteBinding ∷ []

finiteScienceWitnessBindingsCount : Nat
finiteScienceWitnessBindingsCount = 6

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
