module DASHI.Culture.RastafariItalReturnFlowCircularityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.RastafariItalMaterialProvenanceConservationExact as Material
import DASHI.Culture.RastafariItalSocioEcologicalFlowBridgeExact as Flow
import DASHI.Environment.QuantitiesConservation as Conservation

------------------------------------------------------------------------
-- ITAL RETURN FLOW / CIRCULARITY
--
-- Repository-native cross-pollination owner.  No external Rastafari source is
-- credited with the conservation/circularity theorems below.
--
-- The intended distinction is:
--
--   reuse != measured return != closed loop != regeneration.
--
-- A cultural preference for local/natural/communal practice can motivate these
-- measurements, but cannot replace a quantity or provenance receipt.
------------------------------------------------------------------------

data ReturnKind : Set where
  compostReturn cropResidueReturn foodWasteReturn waterReuse seedRetention communityRedistribution : ReturnKind

data ReturnStatus : Set where
  generated recoveredUnverified transformedForReturn reintroducedVerified exportedOrLost : ReturnStatus

data CircularityClass : Set where
  linearFlow reuseOnly partialMeasuredCycle measuredClosedCycle regenerativeClaim : CircularityClass

record ReturnFlowReceipt (u : Conservation.Unit) : Set where
  constructor returnFlowReceipt
  field
    kind : ReturnKind
    generatedQuantity : Conservation.Quantity u
    recoveredQuantity : Conservation.Quantity u
    reintroducedQuantity : Conservation.Quantity u
    exportedOrResidualQuantity : Conservation.Quantity u

    sourceMaterialProvenance : Material.MaterialProvenanceReceipt
    generationReference : String
    recoveryReference : String
    transformationReference : String
    reintroductionReference : String
    destinationReference : String
    residualReference : String
    validationReference : String

open ReturnFlowReceipt public

------------------------------------------------------------------------
-- History-qualified return eligibility.
--
-- Material may exist and may even have been recovered without yet being
-- qualified for reintroduction.  This is a local specialization of the repo's
-- recurring history-qualified-access pattern, without importing draft PR #662.
------------------------------------------------------------------------

data ReturnEligibility : ReturnStatus → Set where
  transformedIsEligible : ReturnEligibility transformedForReturn
  reintroducedIsEligible : ReturnEligibility reintroducedVerified

recoveredIsNotYetQualified : ReturnEligibility recoveredUnverified → ⊥
recoveredIsNotYetQualified ()

generatedIsNotYetQualified : ReturnEligibility generated → ⊥
generatedIsNotYetQualified ()

exportedIsNotQualifiedForReturn : ReturnEligibility exportedOrLost → ⊥
exportedIsNotQualifiedForReturn ()

------------------------------------------------------------------------
-- Circularity evidence package.
------------------------------------------------------------------------

record ItalCircularMaterialRealization
    (flow : Flow.ItalSocioEcologicalFlowRealization) : Set where
  constructor italCircularMaterialRealization
  field
    materialRealization : Material.ItalMaterialConservationRealization flow

    compostOrResidueReturn : ReturnFlowReceipt Conservation.cropGrams
    waterReturn : ReturnFlowReceipt Conservation.waterLitres
    nitrogenReturn : ReturnFlowReceipt Conservation.nitrogenGrams
    carbonReturn : ReturnFlowReceipt Conservation.carbonGrams

    declaredClass : CircularityClass
    classEvidenceReference : String
    boundaryReference : String
    observationPeriodReference : String
    validationReference : String

open ItalCircularMaterialRealization public

------------------------------------------------------------------------
-- Same-object conservation reuse.
------------------------------------------------------------------------

circularityWaterBalance :
  {flow : Flow.ItalSocioEcologicalFlowRealization} →
  ItalCircularMaterialRealization flow →
  Conservation.WaterBalance
circularityWaterBalance realization =
  Material.waterBalance (materialRealization realization)

circularityNitrogenBalance :
  {flow : Flow.ItalSocioEcologicalFlowRealization} →
  ItalCircularMaterialRealization flow →
  Conservation.NitrogenBalance
circularityNitrogenBalance realization =
  Material.nitrogenBalance (materialRealization realization)

circularityCarbonBalance :
  {flow : Flow.ItalSocioEcologicalFlowRealization} →
  ItalCircularMaterialRealization flow →
  Conservation.CarbonBalance
circularityCarbonBalance realization =
  Material.carbonBalance (materialRealization realization)

------------------------------------------------------------------------
-- Non-collapse / BIDI gates.
------------------------------------------------------------------------

data ReuseProvesClosedLoop : Set where

data PartialCycleProvesClosedLoop : Set where

data ClosedLoopProvesRegeneration : Set where

data ReturnQuantityIdentifiesCulturalLivity : Set where

data SeedRetentionProvesGeneticOrCulturalContinuity : Set where

data CommunityRedistributionProvesEquitableDistribution : Set where

reuseDoesNotProveClosedLoop : ReuseProvesClosedLoop → ⊥
reuseDoesNotProveClosedLoop ()

partialCycleDoesNotProveClosedLoop : PartialCycleProvesClosedLoop → ⊥
partialCycleDoesNotProveClosedLoop ()

closedLoopDoesNotProveRegeneration : ClosedLoopProvesRegeneration → ⊥
closedLoopDoesNotProveRegeneration ()

returnQuantityDoesNotIdentifyCulturalLivity : ReturnQuantityIdentifiesCulturalLivity → ⊥
returnQuantityDoesNotIdentifyCulturalLivity ()

seedRetentionDoesNotProveGeneticOrCulturalContinuity :
  SeedRetentionProvesGeneticOrCulturalContinuity → ⊥
seedRetentionDoesNotProveGeneticOrCulturalContinuity ()

communityRedistributionDoesNotProveEquitableDistribution :
  CommunityRedistributionProvesEquitableDistribution → ⊥
communityRedistributionDoesNotProveEquitableDistribution ()

------------------------------------------------------------------------
-- Constructor-disjoint circularity facts.
------------------------------------------------------------------------

reuseIsNotMeasuredClosedCycle : reuseOnly ≡ measuredClosedCycle → ⊥
reuseIsNotMeasuredClosedCycle ()

partialCycleIsNotMeasuredClosedCycle : partialMeasuredCycle ≡ measuredClosedCycle → ⊥
partialCycleIsNotMeasuredClosedCycle ()

measuredClosedCycleIsNotRegenerativeClaim : measuredClosedCycle ≡ regenerativeClaim → ⊥
measuredClosedCycleIsNotRegenerativeClaim ()

record ItalReturnFlowBoundary : Set where
  constructor italReturnFlowBoundary
  field
    recoveredMaterialIsAutomaticallyReturnEligible : Bool
    recoveredMaterialIsAutomaticallyReturnEligibleIsFalse :
      recoveredMaterialIsAutomaticallyReturnEligible ≡ false

    reuseMeansClosedLoop : Bool
    reuseMeansClosedLoopIsFalse : reuseMeansClosedLoop ≡ false

    measuredClosedLoopMeansRegeneration : Bool
    measuredClosedLoopMeansRegenerationIsFalse : measuredClosedLoopMeansRegeneration ≡ false

    returnFlowReusesCanonicalConservation : Bool
    returnFlowReusesCanonicalConservationIsTrue : returnFlowReusesCanonicalConservation ≡ true

    returnFlowRequiresProvenance : Bool
    returnFlowRequiresProvenanceIsTrue : returnFlowRequiresProvenance ≡ true

canonicalItalReturnFlowBoundary : ItalReturnFlowBoundary
canonicalItalReturnFlowBoundary =
  italReturnFlowBoundary
    false refl
    false refl
    false refl
    true refl
    true refl
