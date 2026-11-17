{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.FieldGeometryMatterKernelValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
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

strongPromotionNeedsClosedNuisance :
  {candidate : Promotion.AnomalousMomentumCandidate} →
  (evidence : Promotion.StrongResidualPromotionEvidence candidate) →
  Promotion.nuisanceStatus candidate ≡ Promotion.nuisanceClosedByReceipt
strongPromotionNeedsClosedNuisance evidence =
  Promotion.candidateNuisanceClosed evidence

strongPromotionNeedsRepetition :
  {candidate : Promotion.AnomalousMomentumCandidate} →
  (evidence : Promotion.StrongResidualPromotionEvidence candidate) →
  Promotion.repeatedOnSameApparatus (Promotion.replication candidate) ≡ true
strongPromotionNeedsRepetition evidence =
  Promotion.candidateRepeatedIsTrue evidence

strongPromotionNeedsIndependentReplication :
  {candidate : Promotion.AnomalousMomentumCandidate} →
  (evidence : Promotion.StrongResidualPromotionEvidence candidate) →
  Promotion.independentlyReplicated (Promotion.replication candidate) ≡ true
strongPromotionNeedsIndependentReplication evidence =
  Promotion.candidateIndependentReplicationIsTrue evidence

strongPromotionRemainsMechanismNeutral :
  {candidate : Promotion.AnomalousMomentumCandidate} →
  (evidence : Promotion.StrongResidualPromotionEvidence candidate) →
  Promotion.remainsMechanismNeutral candidate ≡ true
strongPromotionRemainsMechanismNeutral evidence =
  Promotion.candidateRemainsMechanismNeutral evidence

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
