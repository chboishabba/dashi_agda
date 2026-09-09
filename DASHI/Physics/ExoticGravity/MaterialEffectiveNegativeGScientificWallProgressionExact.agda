module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScientificWallProgressionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScientificWallBidiExact as Wall

------------------------------------------------------------------------
-- SCIENTIFIC-WALL PROGRESSION
--
-- This is only a first-open scheduler over the already-defined wall
-- discriminators. It does not create new experimental semantics and it does not
-- allow payment of one coordinate to synthesize later coordinates.
------------------------------------------------------------------------

record ScientificWallPaymentState : Set where
  constructor scientific-wall-payment-state
  field
    massCurrentPaid : Bool
    stressEnergyPaid : Bool
    sourceMaterialAxesPaid : Bool
    modelClassSeparationPaid : Bool
    scalingReplicationIdentityPaid : Bool

open ScientificWallPaymentState public

data ScientificWallLeaf : Set where
  massCurrentLeaf : ScientificWallLeaf
  stressEnergyLeaf : ScientificWallLeaf
  sourceMaterialAxesLeaf : ScientificWallLeaf
  modelClassSeparationLeaf : ScientificWallLeaf
  scalingReplicationIdentityLeaf : ScientificWallLeaf
  scientificWallClosed : ScientificWallLeaf

firstOpenScientificWallLeaf : ScientificWallPaymentState → ScientificWallLeaf
firstOpenScientificWallLeaf (scientific-wall-payment-state false _ _ _ _) = massCurrentLeaf
firstOpenScientificWallLeaf (scientific-wall-payment-state true false _ _ _) = stressEnergyLeaf
firstOpenScientificWallLeaf (scientific-wall-payment-state true true false _ _) = sourceMaterialAxesLeaf
firstOpenScientificWallLeaf (scientific-wall-payment-state true true true false _) = modelClassSeparationLeaf
firstOpenScientificWallLeaf (scientific-wall-payment-state true true true true false) = scalingReplicationIdentityLeaf
firstOpenScientificWallLeaf (scientific-wall-payment-state true true true true true) = scientificWallClosed

collisionForLeaf : ScientificWallLeaf → Wall.ScientificWallCollision
collisionForLeaf massCurrentLeaf = Wall.chargeVsMassCurrentCollision
collisionForLeaf stressEnergyLeaf = Wall.massCurrentVsStressEnergyCollision
collisionForLeaf sourceMaterialAxesLeaf = Wall.sourceVsConstitutiveCollision
collisionForLeaf modelClassSeparationLeaf = Wall.finiteScalingModelCollision
collisionForLeaf scalingReplicationIdentityLeaf = Wall.replicationIdentityCollision
collisionForLeaf scientificWallClosed = Wall.replicationIdentityCollision

discriminatorForLeaf : ScientificWallLeaf → Wall.ScientificWallDiscriminator
discriminatorForLeaf massCurrentLeaf = Wall.componentResolvedMassCurrent
discriminatorForLeaf stressEnergyLeaf = Wall.fullLaboratoryStressEnergy
discriminatorForLeaf sourceMaterialAxesLeaf = Wall.independentSourceMaterialAxes
discriminatorForLeaf modelClassSeparationLeaf = Wall.scalingModelClassSeparation
discriminatorForLeaf scalingReplicationIdentityLeaf = Wall.exactScalingReplicationIdentity
discriminatorForLeaf scientificWallClosed = Wall.exactScalingReplicationIdentity

producerForLeaf : ScientificWallLeaf → Search.ProducerClass
producerForLeaf leaf = Wall.producerForScientificWall (discriminatorForLeaf leaf)

------------------------------------------------------------------------
-- Canonical staged recomputation.
------------------------------------------------------------------------

currentWallState : ScientificWallPaymentState
currentWallState = scientific-wall-payment-state false false false false false

currentWallFirstOpen :
  firstOpenScientificWallLeaf currentWallState ≡ massCurrentLeaf
currentWallFirstOpen = refl

afterMassCurrent : ScientificWallPaymentState
afterMassCurrent = scientific-wall-payment-state true false false false false

afterMassCurrentFirstOpen :
  firstOpenScientificWallLeaf afterMassCurrent ≡ stressEnergyLeaf
afterMassCurrentFirstOpen = refl

afterStressEnergy : ScientificWallPaymentState
afterStressEnergy = scientific-wall-payment-state true true false false false

afterStressEnergyFirstOpen :
  firstOpenScientificWallLeaf afterStressEnergy ≡ sourceMaterialAxesLeaf
afterStressEnergyFirstOpen = refl

afterIndependentAxes : ScientificWallPaymentState
afterIndependentAxes = scientific-wall-payment-state true true true false false

afterIndependentAxesFirstOpen :
  firstOpenScientificWallLeaf afterIndependentAxes ≡ modelClassSeparationLeaf
afterIndependentAxesFirstOpen = refl

afterModelSeparation : ScientificWallPaymentState
afterModelSeparation = scientific-wall-payment-state true true true true false

afterModelSeparationFirstOpen :
  firstOpenScientificWallLeaf afterModelSeparation ≡ scalingReplicationIdentityLeaf
afterModelSeparationFirstOpen = refl

fullyPaidWall : ScientificWallPaymentState
fullyPaidWall = scientific-wall-payment-state true true true true true

fullyPaidWallIsClosed :
  firstOpenScientificWallLeaf fullyPaidWall ≡ scientificWallClosed
fullyPaidWallIsClosed = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

record ScientificWallProgressionBoundary : Set where
  constructor scientific-wall-progression-boundary
  field
    paymentOrderMayBeSkippedByLabel : Bool
    payingMassCurrentAutomaticallyPaysStressEnergy : Bool
    payingStressEnergyAutomaticallyPaysSourceMaterialAxes : Bool
    payingIndependentAxesAutomaticallyPaysModelSeparation : Bool
    payingModelSeparationAutomaticallyPaysReplicationIdentity : Bool
    closedWallAutomaticallyProvesNegativeEffectiveG : Bool

canonicalScientificWallProgressionBoundary : ScientificWallProgressionBoundary
canonicalScientificWallProgressionBoundary =
  scientific-wall-progression-boundary false false false false false false
