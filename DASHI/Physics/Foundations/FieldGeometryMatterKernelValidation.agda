{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.FieldGeometryMatterKernelValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Physics.Foundations.SameObjectConservationLedgerExact as Ledger
import DASHI.Physics.Foundations.ControlledPhysicalTransitionExact as Control
import DASHI.Physics.Foundations.PhysicalResidualPromotionExact as Promotion

intervalIsSameObject : Ledger.SameObjectInterval
intervalIsSameObject = Ledger.canonicalSameObjectInterval

sameObjectIdentityIsProved :
  Ledger.startApparatusId Ledger.canonicalSameObjectInterval
    ≡ Ledger.endApparatusId Ledger.canonicalSameObjectInterval
sameObjectIdentityIsProved =
  Ledger.sameApparatusIdentity Ledger.canonicalSameObjectInterval

energyLedgerIsSeparate : Ledger.EnergyLedger
energyLedgerIsSeparate = Ledger.canonicalEnergyLedger

momentumLedgerIsSeparate : Ledger.MomentumLedger
momentumLedgerIsSeparate = Ledger.canonicalMomentumLedger

entropyLedgerIsSeparate : Ledger.EntropyLedger
entropyLedgerIsSeparate = Ledger.canonicalEntropyLedger

chargeLedgerIsSeparate : Ledger.ChargeLedger
chargeLedgerIsSeparate = Ledger.canonicalChargeLedger

coarseResidualIsFour : Ledger.coarseFiniteResidual ≡ 4
coarseResidualIsFour = Ledger.coarseFiniteResidualIsFour

refinedResidualIsOne : Ledger.refinedFiniteResidual ≡ 1
refinedResidualIsOne = Ledger.refinedFiniteResidualIsOne

addingAdmittedChannelChangesResidual :
  Ledger.coarseFiniteResidual ≡ Ledger.refinedFiniteResidual → ⊥
addingAdmittedChannelChangesResidual = Ledger.finiteResidualRefinementDistinguishes

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

residualCandidateExists : Promotion.AnomalousMomentumCandidate
residualCandidateExists = Promotion.canonicalAnomalousMomentumCandidate

residualDoesNotPromoteToAntigravity : Bool
residualDoesNotPromoteToAntigravity =
  Promotion.residualDoesNotDirectlyPromoteToAntigravity
    Promotion.canonicalResidualPromotionBoundary

residualDoesNotPromoteToReactionless : Bool
residualDoesNotPromoteToReactionless =
  Promotion.residualDoesNotDirectlyPromoteToReactionless
    Promotion.canonicalResidualPromotionBoundary

residualDoesNotPromoteToNewPhysics : Bool
residualDoesNotPromoteToNewPhysics =
  Promotion.residualDoesNotDirectlyPromoteToNewPhysics
    Promotion.canonicalResidualPromotionBoundary
