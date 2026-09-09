module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScientificWallValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScientificWallBidiExact as Wall
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScientificWallProgressionExact as Progress

currentWallStartsAtMassCurrent :
  Wall.currentScientificWallDiscriminator
    ≡ Wall.componentResolvedMassCurrent
currentWallStartsAtMassCurrent = Wall.currentScientificWallStartsAtMassCurrent

currentWallRequestsEmpiricalEvidence :
  Wall.currentScientificWallProducer ≡ Search.empiricalEvidenceProducer
currentWallRequestsEmpiricalEvidence = Wall.currentScientificWallProducerIsEmpiricalEvidence

chargeCollisionSelectsMassCurrent :
  Wall.requiredDiscriminator Wall.chargeVsMassCurrentCollision
    ≡ Wall.componentResolvedMassCurrent
chargeCollisionSelectsMassCurrent = Wall.chargeCurrentCollisionNeedsMassCurrentDiscriminator

sourceConstitutiveCollisionSelectsIndependentAxes :
  Wall.requiredDiscriminator Wall.sourceVsConstitutiveCollision
    ≡ Wall.independentSourceMaterialAxes
sourceConstitutiveCollisionSelectsIndependentAxes = Wall.singleFieldCollisionNeedsIndependentAxes

finiteScalingCollisionSelectsModelSeparation :
  Wall.requiredDiscriminator Wall.finiteScalingModelCollision
    ≡ Wall.scalingModelClassSeparation
finiteScalingCollisionSelectsModelSeparation = Wall.finiteScalingCollisionNeedsModelSeparation

stagedCurrentWallStartsAtMassCurrent :
  Progress.firstOpenScientificWallLeaf Progress.currentWallState
    ≡ Progress.massCurrentLeaf
stagedCurrentWallStartsAtMassCurrent = Progress.currentWallFirstOpen

afterMassCurrentWallAdvancesToStressEnergy :
  Progress.firstOpenScientificWallLeaf Progress.afterMassCurrent
    ≡ Progress.stressEnergyLeaf
afterMassCurrentWallAdvancesToStressEnergy = Progress.afterMassCurrentFirstOpen

afterStressEnergyWallAdvancesToIndependentAxes :
  Progress.firstOpenScientificWallLeaf Progress.afterStressEnergy
    ≡ Progress.sourceMaterialAxesLeaf
afterStressEnergyWallAdvancesToIndependentAxes = Progress.afterStressEnergyFirstOpen

afterIndependentAxesWallAdvancesToModelSeparation :
  Progress.firstOpenScientificWallLeaf Progress.afterIndependentAxes
    ≡ Progress.modelClassSeparationLeaf
afterIndependentAxesWallAdvancesToModelSeparation = Progress.afterIndependentAxesFirstOpen

afterModelSeparationWallAdvancesToReplicationIdentity :
  Progress.firstOpenScientificWallLeaf Progress.afterModelSeparation
    ≡ Progress.scalingReplicationIdentityLeaf
afterModelSeparationWallAdvancesToReplicationIdentity = Progress.afterModelSeparationFirstOpen

fullyPaidWallStopsSchedulingAcquisition :
  Progress.decisionForLeaf (Progress.firstOpenScientificWallLeaf Progress.fullyPaidWall)
    ≡ Progress.noFurtherScientificWallAcquisition
fullyPaidWallStopsSchedulingAcquisition = Progress.closedWallHasNoFurtherAcquisition

fullyPaidWallUsesNoSearchProducer :
  Progress.producerForDecision
    (Progress.decisionForLeaf (Progress.firstOpenScientificWallLeaf Progress.fullyPaidWall))
    ≡ Search.noSearchProducer
fullyPaidWallUsesNoSearchProducer = Progress.closedWallProducerIsNoSearch

closedWallDoesNotProveNegativeG :
  Progress.closedWallAutomaticallyProvesNegativeEffectiveG
    Progress.canonicalScientificWallProgressionBoundary ≡ false
closedWallDoesNotProveNegativeG = refl

missingDatasetIsNotOneOpaqueResidual :
  Wall.missingDatasetIsOneOpaqueResidual
    Wall.canonicalScientificWallBidiBoundary ≡ false
missingDatasetIsNotOneOpaqueResidual = refl

eachMissingReceiptNeedsCollisionJustification :
  Wall.eachMissingReceiptNeedsCollisionJustification
    Wall.canonicalScientificWallBidiBoundary ≡ true
eachMissingReceiptNeedsCollisionJustification = refl

solvingOneCollisionDoesNotSolveLaterCollisions :
  Wall.solvingOneCollisionAutomaticallySolvesLaterCollisions
    Wall.canonicalScientificWallBidiBoundary ≡ false
solvingOneCollisionDoesNotSolveLaterCollisions = refl

empiricalPaymentsStillNeedProvenance :
  Wall.empiricalPaymentsStillNeedCarrierSensitiveProvenance
    Wall.canonicalScientificWallBidiBoundary ≡ true
empiricalPaymentsStillNeedProvenance = refl

discriminatorDoesNotProveNegativeG :
  Wall.discriminatorReceiptAutomaticallyProvesNegativeEffectiveG
    Wall.canonicalScientificWallBidiBoundary ≡ false
discriminatorDoesNotProveNegativeG = refl
