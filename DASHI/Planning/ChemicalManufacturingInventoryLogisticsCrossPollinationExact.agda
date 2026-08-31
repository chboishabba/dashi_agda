module DASHI.Planning.ChemicalManufacturingInventoryLogisticsCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Chemistry.SaltPetroleumIndustrialChemistryNetworkExact as Chemistry
import DASHI.Planning.NetworkFlowCapacityCongestionExact as Network
import DASHI.Planning.PlanningAdmissibleTransitionBridgeExact as Admission

------------------------------------------------------------------------
-- CHEMICAL MANUFACTURING INVENTORY / LOGISTICS CROSS-POLLINATION
--
-- Structural inspiration from Corkysoft's canonical inventory-execution
-- workflow is deliberately operational only:
-- planned requirement != allocated stock != physically claimed stock != loaded
-- / in-transit / delivered stock; shortages remain visible; substitution is a
-- governed path rather than a silent correction; custody history is additive.
--
-- No removals-domain quantity, rule or authority is imported as a chemical
-- manufacturing fact.  Chemical identities, process compatibility and safety
-- remain owned by chemistry/application receipts.
------------------------------------------------------------------------

data MaterialCustodyStage : Set where
  required
  allocated
  physicallyClaimed
  tankFarmReady
  unitFeedReady
  inProcess
  intermediateStorage
  loadedForTransfer
  inTransit
  deliveredToDownstreamUnit
  quarantinedOrException
  : MaterialCustodyStage

data MaterialRole : Set where
  chlorineFeed
  causticFeed
  hydrogenFeed
  ethyleneFeed
  propyleneFeed
  intermediateFeed
  catalystOrReagent
  productInventory
  : MaterialRole

data ShortageClass : Set where
  noShortage substitutableShortage nonSubstitutableShortage : ShortageClass

data Readiness : Set where
  ready overrideRequired blocked : Readiness

readinessFromShortage : ShortageClass → Readiness
readinessFromShortage noShortage = ready
readinessFromShortage substitutableShortage = overrideRequired
readinessFromShortage nonSubstitutableShortage = blocked

nonSubstitutableDoesNotBecomeReady :
  readinessFromShortage nonSubstitutableShortage ≡ ready → ⊥
nonSubstitutableDoesNotBecomeReady ()

------------------------------------------------------------------------
-- Planned versus physical inventory truth.
------------------------------------------------------------------------

record ChemicalInventoryLine : Set where
  constructor chemical-inventory-line
  field
    material : Chemistry.MaterialFamily
    role : MaterialRole
    requiredQuantityReference : String
    allocatedQuantityReference : String
    physicallyAvailableQuantityReference : String
    custodyStage : MaterialCustodyStage
    lotOrBatchReference : String
    specificationReference : String
    compatibilityReference : String
    storageEnvelopeReference : String
    shortage : ShortageClass

open ChemicalInventoryLine public

data PlanSurface : Set where plannedAvailable : PlanSurface

data PhysicalAvailability : Set where physicallyUnavailable physicallyAvailable : PhysicalAvailability

data InventoryState : Set where planOnly planAndPhysical : InventoryState

planSurface : InventoryState → PlanSurface
planSurface _ = plannedAvailable

physicalAvailability : InventoryState → PhysicalAvailability
physicalAvailability planOnly = physicallyUnavailable
physicalAvailability planAndPhysical = physicallyAvailable

samePlanSurface : planSurface planOnly ≡ planSurface planAndPhysical
samePlanSurface = refl

physicalStateDiffers :
  physicalAvailability planOnly ≡ physicalAvailability planAndPhysical → ⊥
physicalStateDiffers ()

------------------------------------------------------------------------
-- Joint-feed readiness: the downstream unit can be blocked by one missing
-- co-feed despite abundance of another stream.
------------------------------------------------------------------------

data ChlorineAvailability : Set where chlorineAvailable chlorineUnavailable : ChlorineAvailability

data EthyleneAvailability : Set where ethyleneAvailable ethyleneUnavailable : EthyleneAvailability

data PVCUnitState : Set where pvcUnitBlocked pvcUnitReady : PVCUnitState

pvcReadiness : ChlorineAvailability → EthyleneAvailability → PVCUnitState
pvcReadiness chlorineAvailable ethyleneAvailable = pvcUnitReady
pvcReadiness _ _ = pvcUnitBlocked

chlorineAbundanceCannotReplaceEthylene :
  pvcReadiness chlorineAvailable ethyleneUnavailable ≡ pvcUnitReady → ⊥
chlorineAbundanceCannotReplaceEthylene ()

ethyleneAbundanceCannotReplaceChlorine :
  pvcReadiness chlorineUnavailable ethyleneAvailable ≡ pvcUnitReady → ⊥
ethyleneAbundanceCannotReplaceChlorine ()

------------------------------------------------------------------------
-- Substitution is governed by chemical compatibility, not by generic stock
-- availability.  A proposed substitute needs an application-specific receipt.
------------------------------------------------------------------------

record ChemicalSubstitutionReceipt : Set where
  constructor chemical-substitution-receipt
  field
    originalMaterial : Chemistry.MaterialFamily
    substituteMaterial : Chemistry.MaterialFamily
    sameRequiredFunctionReference : String
    reactionCompatibilityReference : String
    impurityCompatibilityReference : String
    equipmentCompatibilityReference : String
    productSpecificationPreservedReference : String
    safetyEnvelopePreservedReference : String
    approvalAuthorityReference : String
    validationReference : String

------------------------------------------------------------------------
-- Co-product coupling: chlor-alkali creates chlorine, caustic and hydrogen
-- together, so downstream demand/storage constraints can feed back into plant
-- scheduling even when one product has strong demand.
------------------------------------------------------------------------

data CoproductInventoryPressure : Set where
  chlorineStoragePressure
  causticStoragePressure
  hydrogenDispositionPressure
  balancedDisposition
  : CoproductInventoryPressure

record CoproductPlanningReceipt : Set where
  constructor coproduct-planning-receipt
  field
    chlorineDemandReference : String
    causticDemandReference : String
    hydrogenDemandOrDispositionReference : String
    chlorineStorageReference : String
    causticStorageReference : String
    hydrogenHandlingReference : String
    electricityAvailabilityReference : String
    operatingRateReference : String
    validationReference : String

------------------------------------------------------------------------
-- Network-planning weld.
------------------------------------------------------------------------

data ChemicalNetworkStage : Set where
  saltMineOrBrine
  chlorAlkaliPlant
  crackerOrRefinery
  intermediatePlant
  polymerPlant
  formulationPlant
  warehouseOrTankFarm
  transportCorridor
  customerOrDownstreamPlant
  : ChemicalNetworkStage

record ChemicalNetworkLeg : Set where
  constructor chemical-network-leg
  field
    from : ChemicalNetworkStage
    to : ChemicalNetworkStage
    material : Chemistry.MaterialFamily
    capacityReference : String
    inventoryReference : String
    transportModeReference : String
    hazardClassReference : String
    temperaturePressureReference : String
    custodyTraceReference : String
    validationReference : String

networkBoundary : Network.CoupledNetworkBoundary
networkBoundary = Network.canonicalCoupledNetworkBoundary

planningAdmissionBoundary : Admission.PlanningAdmissibleTransitionBoundary
planningAdmissionBoundary = Admission.canonicalPlanningAdmissibleTransitionBoundary

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record ChemicalManufacturingInventoryLogisticsBoundary : Set where
  constructor chemical-manufacturing-inventory-logistics-boundary
  field
    plannedInventoryEqualsPhysicalInventory : Bool
    plannedInventoryEqualsPhysicalInventoryIsFalse :
      plannedInventoryEqualsPhysicalInventory ≡ false
    oneFeedAbundanceGuaranteesJointProcessReadiness : Bool
    oneFeedAbundanceGuaranteesJointProcessReadinessIsFalse :
      oneFeedAbundanceGuaranteesJointProcessReadiness ≡ false
    genericSubstitutabilityImpliesChemicalSubstitutability : Bool
    genericSubstitutabilityImpliesChemicalSubstitutabilityIsFalse :
      genericSubstitutabilityImpliesChemicalSubstitutability ≡ false
    individualPlantFeasibilityImpliesWholeNetworkFeasibility : Bool
    individualPlantFeasibilityImpliesWholeNetworkFeasibilityIsFalse :
      individualPlantFeasibilityImpliesWholeNetworkFeasibility ≡ false
    coproductDemandCanBePlannedIndependently : Bool
    coproductDemandCanBePlannedIndependentlyIsFalse :
      coproductDemandCanBePlannedIndependently ≡ false
    chemicalManufacturingNeedsCustodySpecificationAndCapacityReceipts : Bool
    chemicalManufacturingNeedsCustodySpecificationAndCapacityReceiptsIsTrue :
      chemicalManufacturingNeedsCustodySpecificationAndCapacityReceipts ≡ true

canonicalChemicalManufacturingInventoryLogisticsBoundary :
  ChemicalManufacturingInventoryLogisticsBoundary
canonicalChemicalManufacturingInventoryLogisticsBoundary =
  chemical-manufacturing-inventory-logistics-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
