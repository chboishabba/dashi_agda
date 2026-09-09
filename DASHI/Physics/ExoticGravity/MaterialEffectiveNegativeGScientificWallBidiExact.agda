module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScientificWallBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Interop.SourceAttributionShapePolicyExact as Shape
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Physics.ExoticGravity.SuperconductingChargeMassCurrentBidiExact as Current
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryStressEnergyCompilationExact as Stress
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGDiscriminatorCutsetExact as Cutset
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScalingModelDiscriminatorExact as Scaling
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScalingReplicationIdentityWeldExact as Replication

------------------------------------------------------------------------
-- SCIENTIFIC WALL AS A BIDI
--
-- Forward direction: a promoted interpretation needs explicit same-object
-- receipts. Reverse direction: every absent receipt is justified by a concrete
-- observer collision that it must discriminate. This is a scheduler over
-- existing owners, not a new experimental ontology.
------------------------------------------------------------------------

data ScientificWallCollision : Set where
  chargeVsMassCurrentCollision : ScientificWallCollision
  massCurrentVsStressEnergyCollision : ScientificWallCollision
  sourceVsConstitutiveCollision : ScientificWallCollision
  finiteScalingModelCollision : ScientificWallCollision
  replicationIdentityCollision : ScientificWallCollision

data ScientificWallDiscriminator : Set where
  componentResolvedMassCurrent : ScientificWallDiscriminator
  fullLaboratoryStressEnergy : ScientificWallDiscriminator
  independentSourceMaterialAxes : ScientificWallDiscriminator
  scalingModelClassSeparation : ScientificWallDiscriminator
  exactScalingReplicationIdentity : ScientificWallDiscriminator

requiredDiscriminator : ScientificWallCollision → ScientificWallDiscriminator
requiredDiscriminator chargeVsMassCurrentCollision = componentResolvedMassCurrent
requiredDiscriminator massCurrentVsStressEnergyCollision = fullLaboratoryStressEnergy
requiredDiscriminator sourceVsConstitutiveCollision = independentSourceMaterialAxes
requiredDiscriminator finiteScalingModelCollision = scalingModelClassSeparation
requiredDiscriminator replicationIdentityCollision = exactScalingReplicationIdentity

producerForScientificWall : ScientificWallDiscriminator → Search.ProducerClass
producerForScientificWall componentResolvedMassCurrent = Search.empiricalEvidenceProducer
producerForScientificWall fullLaboratoryStressEnergy = Search.empiricalEvidenceProducer
producerForScientificWall independentSourceMaterialAxes = Search.discriminatorProducer
producerForScientificWall scalingModelClassSeparation = Search.discriminatorProducer
producerForScientificWall exactScalingReplicationIdentity = Search.identityProducer

------------------------------------------------------------------------
-- Existing collision witnesses reused directly.
------------------------------------------------------------------------

chargeCurrentSurfaceReallyCollides :
  Current.netChargeCurrent Current.chargeCancelsMassRemainsFixture
    ≡ Current.netChargeCurrent Current.chargeCancelsMassCancelsFixture
chargeCurrentSurfaceReallyCollides = Current.chargeCurrentCollision

chargeCurrentCollisionNeedsMassCurrentDiscriminator :
  requiredDiscriminator chargeVsMassCurrentCollision
    ≡ componentResolvedMassCurrent
chargeCurrentCollisionNeedsMassCurrentDiscriminator = refl

massCurrentAloneStillLeavesStressEnergyOpen :
  Stress.massCurrentAloneConstructsStressEnergy
    Stress.canonicalLaboratoryStressEnergyCompilationBoundary ≡ false
massCurrentAloneStillLeavesStressEnergyOpen = refl

singleFieldSurfaceReallyCollides :
  Cutset.singlePointObserve Cutset.sourceFixture
    ≡ Cutset.singlePointObserve Cutset.constitutiveFixture
singleFieldSurfaceReallyCollides = Cutset.sourceVsConstitutiveSinglePointCollision

singleFieldCollisionNeedsIndependentAxes :
  requiredDiscriminator sourceVsConstitutiveCollision
    ≡ independentSourceMaterialAxes
singleFieldCollisionNeedsIndependentAxes = refl

finiteScalingSurfaceReallyCollides :
  Scaling.sweepSignature Scaling.sourceDependentAdditiveResidual
    ≡ Scaling.sweepSignature Scaling.multiplicativeConstitutiveCoefficient
finiteScalingSurfaceReallyCollides = Scaling.sourceDependentAdditiveVsMultiplicativeCollision

finiteScalingCollisionNeedsModelSeparation :
  requiredDiscriminator finiteScalingModelCollision
    ≡ scalingModelClassSeparation
finiteScalingCollisionNeedsModelSeparation = refl

replicationLabelsDoNotPayIdentity :
  Replication.sameLabelMaySubstituteForSameReplicationCarrier
    Replication.canonicalScalingReplicationIdentityBoundary ≡ false
replicationLabelsDoNotPayIdentity = refl

------------------------------------------------------------------------
-- Current shortest reverse-search entry.
------------------------------------------------------------------------

currentScientificWallCollision : ScientificWallCollision
currentScientificWallCollision = chargeVsMassCurrentCollision

currentScientificWallDiscriminator : ScientificWallDiscriminator
currentScientificWallDiscriminator = requiredDiscriminator currentScientificWallCollision

currentScientificWallStartsAtMassCurrent :
  currentScientificWallDiscriminator ≡ componentResolvedMassCurrent
currentScientificWallStartsAtMassCurrent = refl

currentScientificWallProducer : Search.ProducerClass
currentScientificWallProducer = producerForScientificWall currentScientificWallDiscriminator

currentScientificWallProducerIsEmpiricalEvidence :
  currentScientificWallProducer ≡ Search.empiricalEvidenceProducer
currentScientificWallProducerIsEmpiricalEvidence = refl

------------------------------------------------------------------------
-- Attribution shape.
------------------------------------------------------------------------

scientificWallAttributionShape : Shape.RequiredAttributionShape
scientificWallAttributionShape =
  Shape.requiredAttributionShape Shape.internalDerivedTheorem

record ScientificWallBidiBoundary : Set where
  constructor scientific-wall-bidi-boundary
  field
    missingDatasetIsOneOpaqueResidual : Bool
    eachMissingReceiptNeedsCollisionJustification : Bool
    currentFirstDiscriminatorIsComponentResolvedMassCurrent : Bool
    solvingOneCollisionAutomaticallySolvesLaterCollisions : Bool
    internalCollisionTheoremsNeedFreshExternalCitation : Bool
    empiricalPaymentsStillNeedCarrierSensitiveProvenance : Bool
    discriminatorReceiptAutomaticallyProvesNegativeEffectiveG : Bool

canonicalScientificWallBidiBoundary : ScientificWallBidiBoundary
canonicalScientificWallBidiBoundary =
  scientific-wall-bidi-boundary
    false true true false false true false
