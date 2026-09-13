module DASHI.Biology.FruitBoundaryResourcePaidRepairExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_)
open import Data.Empty using (⊥)

import DASHI.Biology.FruitSkinAgenticBoundaryCrossPollinationExact as Skin
import DASHI.Biology.FruitEmbodiedEnergyHistoryFibreExact as Energy
import DASHI.Environment.KNFPermacultureEmbodiedEnergyBridgeExact as KNF

------------------------------------------------------------------------
-- RESOURCE-PAID BREACH -> REPAIR
--
-- SI energy remains the physical carrier.  The Nat arithmetic below is only a
-- finite bookkeeping regression showing the shape of an accounted repair:
-- prior stock + new input = retained stock + captured/exported share + repair
-- expenditure + residual.  It is not a calibrated fruit energy budget.
------------------------------------------------------------------------

record RepairEnergyLedger : Set where
  constructor repair-energy-ledger
  field
    priorInvestment : Nat
    newInput : Nat
    retainedInvestment : Nat
    attackerCapture : Nat
    repairExpenditure : Nat
    residual : Nat
    balance :
      priorInvestment + newInput ≡
      retainedInvestment + attackerCapture + repairExpenditure + residual

open RepairEnergyLedger public

canonicalBreachedRepairLedger : RepairEnergyLedger
canonicalBreachedRepairLedger =
  repair-energy-ledger
    14
    6
    11
    2
    7
    0
    refl

record ResourcePaidSkinRepair : Set where
  constructor resource-paid-skin-repair
  field
    before : Skin.FruitSkinState
    afterAttack : Skin.FruitSkinState
    afterRepair : Skin.FruitSkinState
    beforeIsIntact : before ≡ Skin.skinIntact
    attackBreaches : afterAttack ≡ Skin.skinBreached
    repairReseals : afterRepair ≡ Skin.skinResealed
    physicalInvestment : Energy.EmbodiedEnergy
    accounting : RepairEnergyLedger
    repairNeedsPositiveBookkeepingCoordinate : Nat

open ResourcePaidSkinRepair public

canonicalResourcePaidSkinRepair : ResourcePaidSkinRepair
canonicalResourcePaidSkinRepair =
  resource-paid-skin-repair
    Skin.skinIntact
    Skin.skinBreached
    Skin.skinResealed
    refl refl refl
    (Energy.joules 14)
    canonicalBreachedRepairLedger
    7

------------------------------------------------------------------------
-- KNF/permaculture may alter the provenance of repair-supporting resource
-- flows, but cannot make repair cost disappear.  The bridge is deliberately
-- existential/application-supplied: no KNF preparation is asserted to repair
-- fruit skin by definition.
------------------------------------------------------------------------

record LocalRepairSupportAdapter : Set where
  constructor local-repair-support-adapter
  field
    repair : ResourcePaidSkinRepair
    localFlow : KNF.LocalFlowTransformation
    supportsRepairResourcePool : Bool
    supportEvidenceRequired : Bool

open LocalRepairSupportAdapter public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ResealingMeansFreeRepairPermission : Set where

data AccountedRepairMeansRestoredHistoryPermission : Set where

data KNFInputMeansFruitRepairPermission : Set where

data ZeroResidualMeansCompletePhysicalModelPermission : Set where

resealingIsNotFreeRepair : ResealingMeansFreeRepairPermission → ⊥
resealingIsNotFreeRepair ()

accountedRepairDoesNotRestoreHistory : AccountedRepairMeansRestoredHistoryPermission → ⊥
accountedRepairDoesNotRestoreHistory ()

knfInputDoesNotDefinitionallyRepairFruit : KNFInputMeansFruitRepairPermission → ⊥
knfInputDoesNotDefinitionallyRepairFruit ()

zeroRegressionResidualDoesNotProveCompletePhysics :
  ZeroResidualMeansCompletePhysicalModelPermission → ⊥
zeroRegressionResidualDoesNotProveCompletePhysics ()

record FruitBoundaryResourcePaidRepairBoundary : Set where
  constructor fruit-boundary-resource-paid-repair-boundary
  field
    breachMayExposePriorEmbodiedInvestment : Bool
    repairRequiresAdditionalResourceAccounting : Bool
    resealedSurfaceMayHideRepairHistory : Bool
    localResourceFlowsMaySupportRepairPool : Bool
    localResourceFlowAutomaticallyRepairsFruit : Bool
    finiteZeroResidualIsCompletePhysicalCalibration : Bool

canonicalFruitBoundaryResourcePaidRepairBoundary :
  FruitBoundaryResourcePaidRepairBoundary
canonicalFruitBoundaryResourcePaidRepairBoundary =
  fruit-boundary-resource-paid-repair-boundary
    true true true true false false
