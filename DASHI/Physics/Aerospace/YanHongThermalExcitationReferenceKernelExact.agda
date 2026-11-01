module DASHI.Physics.Aerospace.YanHongThermalExcitationReferenceKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Aerospace.YanHongThermalExcitationSourceReplayExact as Y

data ThermalCaseLabel : Set where case1 case2 case3 case4 : ThermalCaseLabel

selectCase : ThermalCaseLabel → Y.ThermalExcitationCase
selectCase case1 = Y.YanThermalSourceReplay.case1 Y.sourceExactYanThermalReplay
selectCase case2 = Y.YanThermalSourceReplay.case2 Y.sourceExactYanThermalReplay
selectCase case3 = Y.YanThermalSourceReplay.case3 Y.sourceExactYanThermalReplay
selectCase case4 = Y.YanThermalSourceReplay.case4 Y.sourceExactYanThermalReplay

data QualitativeResponse : Set where
  higherPowerStrongerEffect moreActuatorsRedistributeEnergy
  upstreamPlacementEffective atShockPlacementWeak : QualitativeResponse

caseResponse : ThermalCaseLabel → List QualitativeResponse
caseResponse case1 = upstreamPlacementEffective ∷ []
caseResponse case2 = higherPowerStrongerEffect ∷ upstreamPlacementEffective ∷ []
caseResponse case3 = moreActuatorsRedistributeEnergy ∷ upstreamPlacementEffective ∷ []
caseResponse case4 = atShockPlacementWeak ∷ []

record YanThermalCaseReferenceKernel : Set where
  constructor yan-thermal-case-reference-kernel
  field
    sourceReference : String
    flowRegime : String
    selectableCases : List ThermalCaseLabel
    exactResponseCurvesPaid : Bool
    operationalVehicleDesignPaid : Bool

open YanThermalCaseReferenceKernel public

yanThermalCaseReferenceKernel : YanThermalCaseReferenceKernel
yanThermalCaseReferenceKernel = yan-thermal-case-reference-kernel
  (Y.YanThermalSourceReplay.sourceReference Y.sourceExactYanThermalReplay)
  (Y.YanThermalSourceReplay.flowRegime Y.sourceExactYanThermalReplay)
  (case1 ∷ case2 ∷ case3 ∷ case4 ∷ [])
  false
  false

nextExecutableLeaf : String
nextExecutableLeaf =
  "recover source shock-angle/separation curves plus geometry, mesh, boundary conditions and heat-source model before numerical flow replay"
