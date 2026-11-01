module DASHI.Culture.MissingDeceasedTwentyScientistHiddenProducerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistScienceCapabilityBidiExact as B
import DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopySupportingInfoExact as M
import DASHI.Physics.SpaceWeather.ZhangXiaoxinForecastAlgorithmProducerDepthExact as Z
import DASHI.Physics.Aerospace.YanHongThermalFullTextProducerDepthExact as Y
import DASHI.Physics.Materials.FangDainingInverseDesignHiddenProducerDebtExact as F

data HiddenProducerState : Set where
  manifestLocated : HiddenProducerState
  equationsVisibleDataMissing : HiddenProducerState
  fullTextVisibleArraysMissing : HiddenProducerState
  numericalProducerMissing : HiddenProducerState

data HiddenProducerWitness : Set where
  maiwaldHidden : M.MaiwaldSupportingInfoReceipt → HiddenProducerWitness
  zhangHidden : Z.ZhangForecastProducerDepth → HiddenProducerWitness
  yanHidden : Y.YanThermalFullTextProducerDepth → HiddenProducerWitness
  fangHidden : F.FangHiddenProducerDebt → HiddenProducerWitness

record HiddenProducerBinding : Set where
  constructor hidden-producer-binding
  field
    person : String
    fibre : B.ScientistTechnologyFibre
    state : HiddenProducerState
    witness : HiddenProducerWitness
    newlyPaid : String
    stillUnpaid : String

open HiddenProducerBinding public

maiwaldBinding = hidden-producer-binding
  "Frank W. Maiwald" B.frankMaiwaldFibre manifestLocated
  (maiwaldHidden M.maiwaldSupportingInfoReceipt)
  "free SI manifest with five figures, four tables, photodissociation times, coordinates and vibrational frequencies"
  "raw measured spectrum intensities and calibration files"

zhangBinding = hidden-producer-binding
  "Zhang Xiaoxin" B.zhangXiaoxinFibre equationsVisibleDataMissing
  (zhangHidden Z.zhangForecastProducerDepth)
  "public full-text algorithm topology and equations for SWM / CEEMDAN / CWT"
  "event-level rows, exact hyperparameters, precursor quantisation and runnable implementation"

yanBinding = hidden-producer-binding
  "Yan Hong" B.yanHongFibre fullTextVisibleArraysMissing
  (yanHidden Y.yanThermalFullTextProducerDepth)
  "publisher full text, four Mach-5 cases and governing numerical-method family"
  "machine-readable response curves, geometry, mesh and boundary conditions"

fangBinding = hidden-producer-binding
  "Fang Daining" B.fangDainingFibre numericalProducerMissing
  (fangHidden F.fangHiddenProducerDebt)
  "source-exact objective and experimental negative-group-velocity validation claim"
  "energy functional, unit-cell geometry, material constants, band arrays and solver/code"

hiddenProducerBindings : List HiddenProducerBinding
hiddenProducerBindings = maiwaldBinding ∷ zhangBinding ∷ yanBinding ∷ fangBinding ∷ []

hiddenProducerBindingsCount : Nat
hiddenProducerBindingsCount = 4

hiddenProducerDoesNotPaySourceAlgorithm : Bool
hiddenProducerDoesNotPaySourceAlgorithm = false

hiddenProducerDoesNotPayHistoricalDeployment : Bool
hiddenProducerDoesNotPayHistoricalDeployment = false

hiddenProducerDoesNotPayCustody : Bool
hiddenProducerDoesNotPayCustody = false

hiddenProducerCanRefineAcquisitionPareto : Bool
hiddenProducerCanRefineAcquisitionPareto = true
