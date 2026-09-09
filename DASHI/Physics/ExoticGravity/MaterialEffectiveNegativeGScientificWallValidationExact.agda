module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScientificWallValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScientificWallBidiExact as Wall

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
