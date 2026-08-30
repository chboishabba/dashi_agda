module DASHI.Environment.RootSoilSaltLineageBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Environment.RootSoilFungalIonWaterPhysiologyExact as Root
import DASHI.Geology.SaltGeochemistryExact as Salt
import DASHI.Geology.SaltConservationSpineExact as Spine
import DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact as PNP

------------------------------------------------------------------------
-- ROOT/SOIL SALT LINEAGE BIDI WELD
--
-- Forward direction:
--   one geological SaltMaterialLineage
--   -> exact Na+/Cl- chemistry/PNP weld
--   -> soil-pore/root PNP applications
--   -> root-soil physiological interface.
--
-- Backward direction:
--   a root/soil ion observation does not identify a geological source lineage
--   unless the explicit lineage and conservation receipts are supplied.
------------------------------------------------------------------------

record RootSoilSaltSpeciesWeld
    (lineage : Salt.SaltMaterialLineage)
    (ions : Spine.ExactSaltIonDynamicWeld)
    (rootInterface : Root.RootSoilIonInterface) : Set₁ where
  constructor rootSoilSaltSpeciesWeld
  field
    soilSodiumTransport : PNP.ElectrodiffusionApplicationReceipt
    rootSodiumTransport : PNP.ElectrodiffusionApplicationReceipt
    soilChlorideTransport : PNP.ElectrodiffusionApplicationReceipt
    rootChlorideTransport : PNP.ElectrodiffusionApplicationReceipt

    soilSodiumIsSoilPore :
      PNP.application soilSodiumTransport ≡ PNP.soilPoreElectrochemistry
    rootSodiumIsPlantRoot :
      PNP.application rootSodiumTransport ≡ PNP.plantRootIonTransport
    soilChlorideIsSoilPore :
      PNP.application soilChlorideTransport ≡ PNP.soilPoreElectrochemistry
    rootChlorideIsPlantRoot :
      PNP.application rootChlorideTransport ≡ PNP.plantRootIonTransport

    soilSodiumDynamicIsCanonical :
      PNP.species soilSodiumTransport ≡ Spine.sodiumDynamic ions
    rootSodiumDynamicIsCanonical :
      PNP.species rootSodiumTransport ≡ Spine.sodiumDynamic ions
    soilChlorideDynamicIsCanonical :
      PNP.species soilChlorideTransport ≡ Spine.chlorideDynamic ions
    rootChlorideDynamicIsCanonical :
      PNP.species rootChlorideTransport ≡ Spine.chlorideDynamic ions

    rootInterfaceSpeciesReference : String
    sodiumInterfaceConservationReference : String
    chlorideInterfaceConservationReference : String
    commonWaterStateReference : String
    commonSpaceTimeReference : String
    validationReference : String

open RootSoilSaltSpeciesWeld public

record RootSoilSaltConservationWeld
    (lineage : Salt.SaltMaterialLineage)
    (spine : Spine.SaltCrossDomainConservationSpine lineage) : Set₁ where
  constructor rootSoilSaltConservationWeld
  field
    soilReceipt : Spine.SaltDomainMaterialReceipt lineage Spine.soilPoreTransport
    rootReceipt : Spine.SaltDomainMaterialReceipt lineage Spine.plantRootTransport

    soilReceiptIsSpineSoil : soilReceipt ≡ Spine.soil spine
    rootReceiptIsSpineRoot : rootReceipt ≡ Spine.root spine

    sodiumSoilRootFluxBalanceReference : String
    chlorideSoilRootFluxBalanceReference : String
    uptakeExclusionPartitionReference : String
    waterFluxCouplingReference : String
    tissueOrXylemObservationReference : String
    validationReference : String

open RootSoilSaltConservationWeld public

record RootSoilSaltBidi
    (lineage : Salt.SaltMaterialLineage)
    (ions : Spine.ExactSaltIonDynamicWeld)
    (conservation : Spine.SaltCrossDomainConservationSpine lineage)
    (mechanism : Root.RootSoilIonWaterMechanism) : Set₁ where
  constructor rootSoilSaltBidi
  field
    speciesWeld :
      RootSoilSaltSpeciesWeld lineage ions (Root.ionInterface mechanism)
    conservationWeld : RootSoilSaltConservationWeld lineage conservation

    forwardLineageReference : String
    reverseSourceAttributionReference : String
    salinityObservationModelReference : String
    osmoticSaltCouplingReference : String
    transporterSelectivityReference : String
    heldOutValidationReference : String

open RootSoilSaltBidi public

------------------------------------------------------------------------
-- Explicit anti-promotion boundary.
------------------------------------------------------------------------

record RootSoilSaltBoundary : Set where
  constructor rootSoilSaltBoundary
  field
    measuredSalinityDeterminesNaClOnlyComposition : Bool
    measuredSalinityDeterminesNaClOnlyCompositionIsFalse :
      measuredSalinityDeterminesNaClOnlyComposition ≡ false

    rootSodiumObservationIdentifiesGeologicalSaltSource : Bool
    rootSodiumObservationIdentifiesGeologicalSaltSourceIsFalse :
      rootSodiumObservationIdentifiesGeologicalSaltSource ≡ false

    rootChlorideObservationIdentifiesGeologicalSaltSource : Bool
    rootChlorideObservationIdentifiesGeologicalSaltSourceIsFalse :
      rootChlorideObservationIdentifiesGeologicalSaltSource ≡ false

    samePNPSpeciesProvesSameMaterialProvenance : Bool
    samePNPSpeciesProvesSameMaterialProvenanceIsFalse :
      samePNPSpeciesProvesSameMaterialProvenance ≡ false

    exactSaltLineageStillNeedsPhysiologyValidation : Bool
    exactSaltLineageStillNeedsPhysiologyValidationIsTrue :
      exactSaltLineageStillNeedsPhysiologyValidation ≡ true

canonicalRootSoilSaltBoundary : RootSoilSaltBoundary
canonicalRootSoilSaltBoundary =
  rootSoilSaltBoundary false refl false refl false refl false refl true refl
