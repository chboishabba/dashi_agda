module DASHI.Culture.MissingDeceasedTwentyScientistScienceReferenceKernelBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistScienceCapabilityBidiExact as B
import DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastReferenceKernelExact as ZX
import DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopyReferenceKernelExact as M
import DASHI.Physics.Materials.FangDainingInverseDesignReferenceKernelExact as F
import DASHI.Physics.Aerospace.YanHongThermalExcitationReferenceKernelExact as Y

data ReferenceKernelState : Set where
  sourceCoordinateProjection executableSourceSubkernel blockedOnHiddenProducer : ReferenceKernelState

record ReferenceKernelBinding : Set where
  constructor reference-kernel-binding
  field
    person : String
    fibre : B.ScientistTechnologyFibre
    kernelLabel : String
    state : ReferenceKernelState
    whatExecutes : String
    whatDoesNotExecute : String
    nextProducer : String

open ReferenceKernelBinding public

zhangReferenceBinding : ReferenceKernelBinding
zhangReferenceBinding = reference-kernel-binding
  "Zhang Xiaoxin" B.zhangXiaoxinFibre
  "aggregateProjection over source-exact 229-event carrier"
  executableSourceSubkernel
  "deterministic projection of source-exposed event counts, recall label, IMF selection and timescale"
  "the original whitening/CEEMDAN/CWT forecast algorithm"
  "source hyperparameters, event-level inputs/outputs and precursor rule"

maiwaldReferenceBinding : ReferenceKernelBinding
maiwaldReferenceBinding = reference-kernel-binding
  "Frank W. Maiwald" B.frankMaiwaldFibre
  "tag-temperature/spectral-anchor reference kernel"
  executableSourceSubkernel
  "source-exact tag-temperature selection plus spectral window and highlighted feature projection"
  "measured intensity spectrum or dissociation dynamics"
  "raw spectrum/calibration/dissociation-time arrays"

fangReferenceBinding : ReferenceKernelBinding
fangReferenceBinding = reference-kernel-binding
  "Fang Daining" B.fangDainingFibre
  "inverse-design objective/validation projection"
  blockedOnHiddenProducer
  "source objective, prescribed objects and negative-group-velocity validation claim"
  "the inverse-design solver or band-structure calculation"
  "energy functional, unit-cell geometry, material constants and band arrays"

yanReferenceBinding : ReferenceKernelBinding
yanReferenceBinding = reference-kernel-binding
  "Yan Hong" B.yanHongFibre
  "four-case thermal-excitation selector"
  executableSourceSubkernel
  "selection of the four source-exact E/N/S cases and source qualitative response class"
  "Navier-Stokes numerical replay or operational vehicle design"
  "geometry, mesh, boundary conditions, heat-source model and response curves"

referenceKernelBindings : List ReferenceKernelBinding
referenceKernelBindings =
  zhangReferenceBinding ∷ maiwaldReferenceBinding ∷ fangReferenceBinding ∷ yanReferenceBinding ∷ []

referenceKernelBindingsCount : Nat
referenceKernelBindingsCount = 4

referenceProjectionDoesNotEqualSourceAlgorithm : Bool
referenceProjectionDoesNotEqualSourceAlgorithm = false

referenceKernelDoesNotPayHistoricalDeployment : Bool
referenceKernelDoesNotPayHistoricalDeployment = false

referenceKernelDoesNotPayPersonPossession : Bool
referenceKernelDoesNotPayPersonPossession = false

hiddenProducerBlocksAlgorithmPromotion : Bool
hiddenProducerBlocksAlgorithmPromotion = true
