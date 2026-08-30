module DASHI.Culture.RastafariItalSocioEcologicalFlowBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.RastafariItalLivityExact as Ital
import DASHI.Culture.RastafariItalInhabitedLandscapeBridgeExact as ItalLandscape
import DASHI.Environment.LESSituatedObservationInteractionExact as Observe
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC
import DASHI.Environment.LESAdmissibleTransitionMDLCrossPollinationExact as SoilTransition
import DASHI.Environment.SoilBiogeochemistryProcessNetworkExact as SoilBio
import DASHI.Planning.InhabitedLandscapeExact as Landscape

------------------------------------------------------------------------
-- ITAL / SOCIO-ECOLOGICAL FLOW BRIDGE
--
-- This module attaches an Ital livity profile to repository-owned physical
-- soil/water/plant process carriers without treating the cultural orientation
-- as a mechanistic or empirical law.
--
--   Ital livity profile
--        |
--        | cultural/practice orientation
--        v
--   inhabited landscape practice
--        |
--        | explicit physical realization required
--        v
--   soil-plant-atmosphere + soil biogeochemistry
--        |
--        | typed process enablement required
--        v
--   admissible ecological transition
--
-- The arrows are typed requirements, not source-attribution identities.
------------------------------------------------------------------------

record ItalSocioEcologicalFlowRealization : Set₁ where
  constructor italSocioEcologicalFlowRealization
  field
    livity : Ital.ItalLivityProfile
    situatedPractice : ItalLandscape.ItalSituatedLandscapePractice
    physicalSystem : SPAC.SPACDomainRealization

    foodFlowReference : String
    waterFlowReference : String
    soilNutrientFlowReference : String
    biomassOrMaterialFlowReference : String
    householdOrCommunityUseReference : String
    conservationInterpretationReference : String
    validationReference : String

open ItalSocioEcologicalFlowRealization public

record ItalSoilProcessRealization
    (flow : ItalSocioEcologicalFlowRealization)
    (process : SoilBio.SoilCNProcess) : Set₁ where
  constructor italSoilProcessRealization
  field
    enabledProcess : SoilTransition.SoilProcessEnablement process
    practiceToProcessIdentificationReference : String
    interventionIdentificationReference : String
    outcomeObservationReference : String
    causalDiscrepancyReference : String

open ItalSoilProcessRealization public

------------------------------------------------------------------------
-- Positive structural facts inherited from the Ital and landscape owners.
------------------------------------------------------------------------

italFlowRetainsLifeAndLandDimensions :
  (flow : ItalSocioEcologicalFlowRealization) →
  Ital.dimension (livity flow) Ital.food ×
  Ital.dimension (livity flow) Ital.land →
  Ital.dimension (livity flow) Ital.food ×
  Ital.dimension (livity flow) Ital.land
italFlowRetainsLifeAndLandDimensions flow evidence = evidence

italFlowCanReuseMultifunctionalMarketGardenCarrier :
  Landscape.InhabitedLandscape.Role Landscape.landscape Landscape.marketGarden Landscape.foodProduction ×
  (Landscape.InhabitedLandscape.Role Landscape.landscape Landscape.marketGarden Landscape.ecologicalPatch ×
   Landscape.InhabitedLandscape.Role Landscape.landscape Landscape.marketGarden Landscape.workplace)
italFlowCanReuseMultifunctionalMarketGardenCarrier =
  ItalLandscape.marketGardenSupportsFoodEcologyLivelihoodCarrier

italFlowRetainsSituatedObservationBoundary :
  INF.FactorsThrough
    Observe.anonymousReading
    Observe.situatedObservationSignature → ⊥
italFlowRetainsSituatedObservationBoundary =
  Observe.anonymousReadingCannotRecoverSituatedSignature

------------------------------------------------------------------------
-- Mechanism gates.
--
-- An Ital-oriented food/land practice does not itself prove hydraulic
-- continuity, soil-process enablement, or a causal environmental outcome.
-- Those must come through the existing SPAC and admissible-transition owners.
------------------------------------------------------------------------

data ItalOrientationProvesSPACMechanism : Set where

data ItalOrientationProvesSoilProcessEnablement : Set where

data ItalOrientationProvesEnvironmentalOutcome : Set where

italOrientationDoesNotProveSPACMechanism :
  ItalOrientationProvesSPACMechanism → ⊥
italOrientationDoesNotProveSPACMechanism ()

italOrientationDoesNotProveSoilProcessEnablement :
  ItalOrientationProvesSoilProcessEnablement → ⊥
italOrientationDoesNotProveSoilProcessEnablement ()

italOrientationDoesNotProveEnvironmentalOutcome :
  ItalOrientationProvesEnvironmentalOutcome → ⊥
italOrientationDoesNotProveEnvironmentalOutcome ()

------------------------------------------------------------------------
-- BIDI reading.
--
-- Forward:
--   cultural orientation + declared practice + physical realization
--   -> a typed socio-ecological flow object.
--
-- Backward:
--   observing a soil/water/plant outcome does not recover or identify the
--   cultural livity that motivated the practice.
------------------------------------------------------------------------

data EnvironmentalOutcomeIdentifiesItalLivity : Set where

environmentalOutcomeDoesNotIdentifyItalLivity :
  EnvironmentalOutcomeIdentifiesItalLivity → ⊥
environmentalOutcomeDoesNotIdentifyItalLivity ()

record ItalSocioEcologicalFlowBoundary : Set where
  constructor italSocioEcologicalFlowBoundary
  field
    italIsHydrologyModel : Bool
    italIsHydrologyModelIsFalse : italIsHydrologyModel ≡ false

    italIsSoilBiogeochemistryModel : Bool
    italIsSoilBiogeochemistryModelIsFalse : italIsSoilBiogeochemistryModel ≡ false

    ecologicalOutcomeIdentifiesCulturalLivity : Bool
    ecologicalOutcomeIdentifiesCulturalLivityIsFalse :
      ecologicalOutcomeIdentifiesCulturalLivity ≡ false

    explicitPhysicalRealizationIsRequired : Bool
    explicitPhysicalRealizationIsRequiredIsTrue :
      explicitPhysicalRealizationIsRequired ≡ true

    explicitProcessEnablementIsRequired : Bool
    explicitProcessEnablementIsRequiredIsTrue :
      explicitProcessEnablementIsRequired ≡ true

canonicalItalSocioEcologicalFlowBoundary : ItalSocioEcologicalFlowBoundary
canonicalItalSocioEcologicalFlowBoundary =
  italSocioEcologicalFlowBoundary
    false refl
    false refl
    false refl
    true refl
    true refl
