{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.FieldGeometryMatterKernelValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Foundations.SameObjectConservationLedgerExact as Ledger
import DASHI.Physics.Foundations.ControlledPhysicalTransitionExact as Control

intervalIsSameObject : Ledger.SameObjectInterval
intervalIsSameObject = Ledger.canonicalSameObjectInterval

energyLedgerIsSeparate : Ledger.EnergyLedger
energyLedgerIsSeparate = Ledger.canonicalEnergyLedger

momentumLedgerIsSeparate : Ledger.MomentumLedger
momentumLedgerIsSeparate = Ledger.canonicalMomentumLedger

entropyLedgerIsSeparate : Ledger.EntropyLedger
entropyLedgerIsSeparate = Ledger.canonicalEntropyLedger

chargeLedgerIsSeparate : Ledger.ChargeLedger
chargeLedgerIsSeparate = Ledger.canonicalChargeLedger

coarseObserverMissesNuisance :
  Ledger.coarseObserved Ledger.thermalWorld
    ≡ Ledger.coarseObserved Ledger.forceWorld
coarseObserverMissesNuisance = refl

consumerStillSeparatesWorlds :
  Ledger.consumerRelevant Ledger.thermalWorld
    ≡ Ledger.consumerRelevant Ledger.forceWorld →
  ⊥
consumerStillSeparatesWorlds = Ledger.consumerDistinguishesFixture

controlDoesNotImplyEquilibrium : Bool
controlDoesNotImplyEquilibrium =
  Control.controlPathDoesNotImplyEquilibrium Control.canonicalControlBoundary
