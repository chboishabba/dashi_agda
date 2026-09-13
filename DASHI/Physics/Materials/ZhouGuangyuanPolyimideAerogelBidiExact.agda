module DASHI.Physics.Materials.ZhouGuangyuanPolyimideAerogelBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (negsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.SI as SI
import DASHI.Core.ScientificCapabilityCarrierBidiExact as C
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T

------------------------------------------------------------------------
-- ZHOU GUANGYUAN: LOW-SHRINKAGE HIGH-TEMPERATURE POLYIMIDE AEROGELS
--
-- Source anchor: Chemical Engineering Journal 2023, article 147642,
-- DOI 10.1016/j.cej.2023.147642.
--
-- The source reports a structure/process/property relation.  This owner keeps
-- the measured example separate from an unearned universal process law.
------------------------------------------------------------------------

ThermalConductivity : SI.Dimension
ThermalConductivity =
  SI.dim SI.one SI.one SI.minusThree SI.zeroI SI.minusOne SI.zeroI SI.zeroI

conductivityScale : SI.DecimalScale
conductivityScale = SI.tenTo (negsuc 3)  -- 10^-4 W m^-1 K^-1

thermalConductivityAt200C : SI.Quantity ThermalConductivity conductivityScale
thermalConductivityAt200C = SI.posQ 543  -- 0.0543 W m^-1 K^-1 = 54.3 mW m^-1 K^-1

testTemperatureKelvin : SI.Quantity SI.Temperature SI.centiScale
testTemperatureKelvin = SI.posQ 47315    -- 473.15 K = 200 degrees Celsius

data AerogelScienceStage : Set where
  diamineDesign polyimideSynthesis networkFormation shrinkageAndPorosity
  thermalCharacterisation thermalStabilityCharacterisation : AerogelScienceStage

record PolyimideAerogelState : Set where
  constructor polyimide-aerogel-state
  field
    sourceReference : String
    designCoordinate : String
    stages : List AerogelScienceStage
    testTemperature : SI.Quantity SI.Temperature SI.centiScale
    thermalConductivity : SI.Quantity ThermalConductivity conductivityScale
    otherSourceReportedBounds : String
    openProcessLeaf : String

open PolyimideAerogelState public

canonicalZhouAerogelState : PolyimideAerogelState
canonicalZhouAerogelState = polyimide-aerogel-state
  "DOI 10.1016/j.cej.2023.147642"
  "benzhydrylidenefluorene-based paddle-shaped diamine design for low-shrinkage polyimide aerogels"
  (diamineDesign ∷ polyimideSynthesis ∷ networkFormation ∷ shrinkageAndPorosity ∷
   thermalCharacterisation ∷ thermalStabilityCharacterisation ∷ [])
  testTemperatureKelvin
  thermalConductivityAt200C
  "source reports shrinkage as low as 7.7%, porosity above 91%, specific surface area 674.8 m^2 g^-1, Td5% above 580 C and Tg above 299 C"
  "exact synthesis recipe/process window, batch variation, scale-up and patent/enterprise transfer"

zhouAerogelCarrier : C.ScientificCapabilityCarrier
zhouAerogelCarrier = C.scientific-capability-carrier
  "polymer/materials science"
  "polyimide-aerogel synthesis and structure-property process window"
  C.processWindow
  C.carrierPartial
  "monomer/synthesis -> network/shrinkage/porosity -> thermal response"
  "DOI 10.1016/j.cej.2023.147642"
  "Measured source points are public; a validated manufacturing/scale-up window is only partially exposed."

zhouAerogelTransformation : T.ApplicationTransformation
zhouAerogelTransformation = T.application-transformation
  "high-temperature lightweight thermal insulation"
  (T.governingPhysics ∷ T.constitutiveConfiguration ∷ [])
  (T.operatingWindow ∷ T.validationCorpus ∷ T.uncertaintyModel ∷
   T.qualificationEvidence ∷ T.tacitExecutionKnowledge ∷ [])
  "DOI 10.1016/j.cej.2023.147642; DICP DNL2200"
  "Application requires preserving the measured structure-property behaviour across geometry, processing, cycling and scale-up."

data ZhouAerogelReverseTarget : Set where
  acquireExactSynthesisRecipe acquireBatchVariation acquireThermalCycling
  acquireScaleUpWindow acquirePatentMapping acquireEnterpriseTransferReceipt : ZhouAerogelReverseTarget

measuredExampleImpliesUniversalProcessWindow : Bool
measuredExampleImpliesUniversalProcessWindow = false

measuredThermalConductivityImpliesEveryApplicationQualified : Bool
measuredThermalConductivityImpliesEveryApplicationQualified = false

siTypedThermalDatumPresent : Bool
siTypedThermalDatumPresent = true
