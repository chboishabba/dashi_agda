module DASHI.Environment.SpringfieldLakesInterventionGeometryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Environment.SpringfieldLakesAquaticWeedMechanicalRemovalExact as Springfield

------------------------------------------------------------------------
-- SPRINGFIELD INTERVENTION GEOMETRY
--
-- The Ipswich record supplies two source-bound local operational examples:
-- spider excavator at the hard-access Viewpoint Drive pond and an aquatic weed
-- harvester at the Vistula Circuit pond.  The finite witness below is DASHI
-- mathematics over those declared operational roles; it does not generalise
-- efficacy across weed species or sites.
------------------------------------------------------------------------

data TreatmentType : Set where
  mechanicalRemoval : TreatmentType

data AccessGeometry : Set where
  steepHardAccess : AccessGeometry
  shallowSurfaceMat : AccessGeometry

data EquipmentChoice : Set where
  spiderExcavator : EquipmentChoice
  aquaticWeedHarvester : EquipmentChoice

record OperationalWorld : Set where
  constructor operationalWorld
  field
    treatment : TreatmentType
    access : AccessGeometry
    equipment : EquipmentChoice
    sourceReference : String

open OperationalWorld public

viewpointWorld : OperationalWorld
viewpointWorld = operationalWorld
  mechanicalRemoval
  steepHardAccess
  spiderExcavator
  "Ipswich City Council source-bound Viewpoint Drive spider-excavator operation"

vistulaWorld : OperationalWorld
vistulaWorld = operationalWorld
  mechanicalRemoval
  shallowSurfaceMat
  aquaticWeedHarvester
  "Ipswich City Council source-bound Vistula Circuit aquatic-weed-harvester operation"

viewpointSourceReceipt : Springfield.SpringfieldMechanicalRemovalReceipt
viewpointSourceReceipt = Springfield.viewpointSpiderReceipt

vistulaSourceReceipt : Springfield.SpringfieldMechanicalRemovalReceipt
vistulaSourceReceipt = Springfield.vistulaHarvesterReceipt

------------------------------------------------------------------------
-- Treatment type alone is too coarse for equipment-choice in this finite
-- fixture; retaining access geometry repairs exactly this declared consumer.
------------------------------------------------------------------------

treatmentObserver : OperationalWorld → TreatmentType
treatmentObserver = treatment

equipmentConsumer : OperationalWorld → EquipmentChoice
equipmentConsumer = equipment

treatmentAccessObserver : OperationalWorld → TreatmentType × AccessGeometry
treatmentAccessObserver world = treatment world , access world

treatmentTypeNonFactorabilityWitness :
  NonFactor.NonFactorabilityWitness treatmentObserver equipmentConsumer
treatmentTypeNonFactorabilityWitness = NonFactor.nonFactorabilityWitness
  viewpointWorld
  vistulaWorld
  refl
  (λ ())

equipmentDoesNotFactorThroughTreatmentType :
  NonFactor.FactorsThrough treatmentObserver equipmentConsumer → ⊥
equipmentDoesNotFactorThroughTreatmentType =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    treatmentTypeNonFactorabilityWitness

equipmentFromTreatmentAndAccess :
  TreatmentType × AccessGeometry → EquipmentChoice
equipmentFromTreatmentAndAccess (mechanicalRemoval , steepHardAccess) = spiderExcavator
equipmentFromTreatmentAndAccess (mechanicalRemoval , shallowSurfaceMat) = aquaticWeedHarvester

equipmentFactorsThroughTreatmentAndAccess :
  NonFactor.FactorsThrough treatmentAccessObserver equipmentConsumer
equipmentFactorsThroughTreatmentAndAccess = NonFactor.factorsThrough
  equipmentFromTreatmentAndAccess
  factorisation
  where
    factorisation : (world : OperationalWorld) →
      equipmentConsumer world ≡
      equipmentFromTreatmentAndAccess (treatmentAccessObserver world)
    factorisation (operationalWorld mechanicalRemoval steepHardAccess spiderExcavator ref) = refl
    factorisation (operationalWorld mechanicalRemoval steepHardAccess aquaticWeedHarvester ref) = refl
    factorisation (operationalWorld mechanicalRemoval shallowSurfaceMat spiderExcavator ref) = refl
    factorisation (operationalWorld mechanicalRemoval shallowSurfaceMat aquaticWeedHarvester ref) = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record SpringfieldInterventionGeometryBoundary : Set where
  constructor springfieldInterventionGeometryBoundary
  field
    treatmentTypeAloneDeterminesEquipmentChoice : Bool
    treatmentTypeAloneDeterminesEquipmentChoiceIsFalse :
      treatmentTypeAloneDeterminesEquipmentChoice ≡ false

    treatmentPlusAccessCanPayDeclaredFiniteEquipmentConsumer : Bool
    treatmentPlusAccessCanPayDeclaredFiniteEquipmentConsumerIsTrue :
      treatmentPlusAccessCanPayDeclaredFiniteEquipmentConsumer ≡ true

    finiteFactorisationProvesUniversalEquipmentOptimality : Bool
    finiteFactorisationProvesUniversalEquipmentOptimalityIsFalse :
      finiteFactorisationProvesUniversalEquipmentOptimality ≡ false

    salviniaOperationalRecordProvesWaterHyacinthEfficacy : Bool
    salviniaOperationalRecordProvesWaterHyacinthEfficacyIsFalse :
      salviniaOperationalRecordProvesWaterHyacinthEfficacy ≡ false

    accessGeometryIsPartOfInterventionFibre : Bool
    accessGeometryIsPartOfInterventionFibreIsTrue :
      accessGeometryIsPartOfInterventionFibre ≡ true

canonicalSpringfieldInterventionGeometryBoundary :
  SpringfieldInterventionGeometryBoundary
canonicalSpringfieldInterventionGeometryBoundary =
  springfieldInterventionGeometryBoundary
    false refl
    true refl
    false refl
    false refl
    true refl
