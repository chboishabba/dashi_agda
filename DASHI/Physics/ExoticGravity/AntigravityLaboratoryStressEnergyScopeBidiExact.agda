module DASHI.Physics.ExoticGravity.AntigravityLaboratoryStressEnergyScopeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.StressEnergyCompatibility as GRStress
import DASHI.Physics.ExoticGravity.SuperconductingChargeMassCurrentBidiExact as Current
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- LABORATORY SOURCE STRESS-ENERGY != THEOREM-FACING W4 STRESS-ENERGY
--
-- The antigravity experiment needs a measured/reconstructed source object for
-- one apparatus.  The existing GR StressEnergyCompatibility owner is a
-- theorem-facing W4 interface and remains blocked at its own exact primitives.
-- Neither receipt pays the other by naming the same tensor symbol T_{mu nu}.
------------------------------------------------------------------------

data StressEnergyScope : Set where
  laboratoryApparatusStressEnergy : StressEnergyScope
  theoremFacingW4StressEnergyInterface : StressEnergyScope

data CoarseStressEnergyLabel : Set where
  stressEnergyTensor : CoarseStressEnergyLabel

data ScopeFixture : Set where
  laboratoryFixture w4Fixture : ScopeFixture

coarseObserve : ScopeFixture → CoarseStressEnergyLabel
coarseObserve _ = stressEnergyTensor

scopeConsumer : ScopeFixture → StressEnergyScope
scopeConsumer laboratoryFixture = laboratoryApparatusStressEnergy
scopeConsumer w4Fixture = theoremFacingW4StressEnergyInterface

coarseCollision : coarseObserve laboratoryFixture ≡ coarseObserve w4Fixture
coarseCollision = refl

coarseStressEnergyNameDoesNotDetermineScope :
  scopeConsumer laboratoryFixture ≡ scopeConsumer w4Fixture → ⊥
coarseStressEnergyNameDoesNotDetermineScope ()

------------------------------------------------------------------------
-- Laboratory source receipt.
------------------------------------------------------------------------

record LaboratoryStressEnergyReceipt : Set₁ where
  constructor laboratory-stress-energy-receipt
  field
    apparatusIdentity : String
    massCurrentSource : Current.MassCurrentSourceReconstructionReceipt

    EnergyDensityReceipt : Set
    energyDensityReceipt : EnergyDensityReceipt

    MomentumDensityReceipt : Set
    momentumDensityReceipt : MomentumDensityReceipt

    StressComponentReceipt : Set
    stressComponentReceipt : StressComponentReceipt

    FrameAndConventionReceipt : Set
    frameAndConventionReceipt : FrameAndConventionReceipt

    TensorAssemblyReceipt : Set
    tensorAssemblyReceipt : TensorAssemblyReceipt

    SameApparatusIdentityReceipt : Set
    sameApparatusIdentityReceipt : SameApparatusIdentityReceipt

open LaboratoryStressEnergyReceipt public

------------------------------------------------------------------------
-- Existing theorem-facing boundary is retained by identity.
------------------------------------------------------------------------

existingGRStressEnergyBoundary : GRStress.StressEnergyBoundaryInterface
existingGRStressEnergyBoundary = GRStress.canonicalStressEnergyBoundaryInterface

existingGRMatterStressEnergyFrontier : GRStress.MatterStressEnergyResidualFrontier
existingGRMatterStressEnergyFrontier = GRStress.canonicalMatterStressEnergyResidualFrontier

------------------------------------------------------------------------
-- Reverse-search residuals are scope-specific.
------------------------------------------------------------------------

data LaboratoryStressEnergyResidual : Set where
  missingEnergyDensity : LaboratoryStressEnergyResidual
  missingMomentumDensity : LaboratoryStressEnergyResidual
  missingStressComponents : LaboratoryStressEnergyResidual
  missingFrameConvention : LaboratoryStressEnergyResidual
  missingTensorAssembly : LaboratoryStressEnergyResidual
  missingSameApparatusIdentity : LaboratoryStressEnergyResidual

producerForLaboratoryStressEnergyResidual :
  LaboratoryStressEnergyResidual → Search.ProducerClass
producerForLaboratoryStressEnergyResidual missingEnergyDensity = Search.empiricalEvidenceProducer
producerForLaboratoryStressEnergyResidual missingMomentumDensity = Search.empiricalEvidenceProducer
producerForLaboratoryStressEnergyResidual missingStressComponents = Search.empiricalEvidenceProducer
producerForLaboratoryStressEnergyResidual missingFrameConvention = Search.identityProducer
producerForLaboratoryStressEnergyResidual missingTensorAssembly = Search.discriminatorProducer
producerForLaboratoryStressEnergyResidual missingSameApparatusIdentity = Search.identityProducer

record LaboratoryStressEnergyScopeBoundary : Set where
  constructor laboratory-stress-energy-scope-boundary
  field
    sameTensorNameMeansSameConsumer : Bool
    laboratoryReceiptPaysW4MatterInterface : Bool
    w4MatterInterfacePaysLaboratorySourceMeasurement : Bool
    laboratoryStressEnergyRequiredForSameApparatusGRComparator : Bool
    theoremFacingW4BoundaryRemainsIndependent : Bool
    laboratoryReceiptAutomaticallyPromotesSourcedEinsteinTheorem : Bool

canonicalLaboratoryStressEnergyScopeBoundary : LaboratoryStressEnergyScopeBoundary
canonicalLaboratoryStressEnergyScopeBoundary =
  laboratory-stress-energy-scope-boundary false false false true true false
