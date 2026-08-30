module DASHI.Culture.RastafariItalMaterialProvenanceConservationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.RastafariItalLivityExact as Ital
import DASHI.Culture.RastafariItalSocioEcologicalFlowBridgeExact as Flow
import DASHI.Environment.QuantitiesConservation as Conservation
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC

------------------------------------------------------------------------
-- ITAL MATERIAL PROVENANCE + CONSERVATION
--
-- This owner distinguishes value/practice language such as local, natural and
-- communal from actual material lineage.  A cultural quality may motivate a
-- provenance question; it does not answer that question by itself.
------------------------------------------------------------------------

data MaterialKind : Set where
  waterMaterial nitrogenMaterial carbonMaterial cropMaterial biomassMaterial : MaterialKind

data ProvenanceStage : Set where
  source production transformation transfer use returnOrExport : ProvenanceStage

record MaterialProvenanceReceipt : Set where
  constructor materialProvenanceReceipt
  field
    material : MaterialKind
    sourceReference : String
    productionReference : String
    transformationReference : String
    transferReference : String
    useReference : String
    returnOrExportReference : String
    validationReference : String

open MaterialProvenanceReceipt public

record ItalMaterialConservationRealization
    (flow : Flow.ItalSocioEcologicalFlowRealization) : Set where
  constructor italMaterialConservationRealization
  field
    waterProvenance : MaterialProvenanceReceipt
    nitrogenProvenance : MaterialProvenanceReceipt
    carbonProvenance : MaterialProvenanceReceipt
    cropProvenance : MaterialProvenanceReceipt
    biomassProvenance : MaterialProvenanceReceipt

    waterBalance : Conservation.WaterBalance
    nitrogenBalance : Conservation.NitrogenBalance
    carbonBalance : Conservation.CarbonBalance
    cropOutput : Conservation.Quantity Conservation.cropGrams

    waterBalanceAgreesWithPhysicalBundle :
      waterBalance ≡ Conservation.water (SPAC.conservation (Flow.physicalSystem flow))
    nitrogenBalanceAgreesWithPhysicalBundle :
      nitrogenBalance ≡ Conservation.nitrogen (SPAC.conservation (Flow.physicalSystem flow))
    carbonBalanceAgreesWithPhysicalBundle :
      carbonBalance ≡ Conservation.carbon (SPAC.conservation (Flow.physicalSystem flow))

    cropMeasurementReference : String
    householdOrCommunityDestinationReference : String
    residualInterpretationReference : String

open ItalMaterialConservationRealization public

------------------------------------------------------------------------
-- BIDI / non-promotion gates.
------------------------------------------------------------------------

data LocalLabelProvesLocalProvenance : Set where

data NaturalLabelProvesUntransformedMaterial : Set where

data CommunalUseProvesClosedMaterialCycle : Set where

data ConservationBalanceIdentifiesCulturalLivity : Set where

localLabelDoesNotProveLocalProvenance : LocalLabelProvesLocalProvenance → ⊥
localLabelDoesNotProveLocalProvenance ()

naturalLabelDoesNotProveUntransformedMaterial :
  NaturalLabelProvesUntransformedMaterial → ⊥
naturalLabelDoesNotProveUntransformedMaterial ()

communalUseDoesNotProveClosedMaterialCycle :
  CommunalUseProvesClosedMaterialCycle → ⊥
communalUseDoesNotProveClosedMaterialCycle ()

conservationBalanceDoesNotIdentifyCulturalLivity :
  ConservationBalanceIdentifiesCulturalLivity → ⊥
conservationBalanceDoesNotIdentifyCulturalLivity ()

------------------------------------------------------------------------
-- Positive weld: the flow's physical realization already carries the canonical
-- conservation bundle.  The Ital material layer consumes it rather than making
-- an independent ecological accounting system.
------------------------------------------------------------------------

physicalConservationBundle :
  (flow : Flow.ItalSocioEcologicalFlowRealization) →
  Conservation.ConservationBundle
physicalConservationBundle flow = SPAC.conservation (Flow.physicalSystem flow)

record ItalMaterialProvenanceBoundary : Set where
  constructor italMaterialProvenanceBoundary
  field
    localQualityIsMaterialLineage : Bool
    localQualityIsMaterialLineageIsFalse : localQualityIsMaterialLineage ≡ false

    naturalQualityMeansNoTransformation : Bool
    naturalQualityMeansNoTransformationIsFalse : naturalQualityMeansNoTransformation ≡ false

    communalUseMeansClosedLoop : Bool
    communalUseMeansClosedLoopIsFalse : communalUseMeansClosedLoop ≡ false

    conservationReceiptIsReused : Bool
    conservationReceiptIsReusedIsTrue : conservationReceiptIsReused ≡ true

    residualsRemainExplicit : Bool
    residualsRemainExplicitIsTrue : residualsRemainExplicit ≡ true

canonicalItalMaterialProvenanceBoundary : ItalMaterialProvenanceBoundary
canonicalItalMaterialProvenanceBoundary =
  italMaterialProvenanceBoundary
    false refl
    false refl
    false refl
    true refl
    true refl
