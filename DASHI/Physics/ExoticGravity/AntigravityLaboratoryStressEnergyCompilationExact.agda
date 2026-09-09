module DASHI.Physics.ExoticGravity.AntigravityLaboratoryStressEnergyCompilationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.SuperconductingChargeMassCurrentBidiExact as Current
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryStressEnergyScopeBidiExact as Stress
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- MASS-CURRENT -> LABORATORY STRESS-ENERGY COMPILER
--
-- J_m is a necessary source coordinate, but it is not by itself a full
-- apparatus stress-energy tensor.  A downstream compilation must still bind
-- energy density, momentum density, stress components, frame/conventions, and
-- exact same-apparatus identity.
------------------------------------------------------------------------

record LaboratoryStressEnergyCompilationInput : Set₁ where
  constructor laboratory-stress-energy-compilation-input
  field
    apparatusIdentity : String
    massCurrent : Current.MassCurrentSourceReconstructionReceipt

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

open LaboratoryStressEnergyCompilationInput public

compileLaboratoryStressEnergy :
  LaboratoryStressEnergyCompilationInput → Stress.LaboratoryStressEnergyReceipt
compileLaboratoryStressEnergy input =
  Stress.laboratory-stress-energy-receipt
    (LaboratoryStressEnergyCompilationInput.apparatusIdentity input)
    (LaboratoryStressEnergyCompilationInput.massCurrent input)
    (LaboratoryStressEnergyCompilationInput.EnergyDensityReceipt input)
    (LaboratoryStressEnergyCompilationInput.energyDensityReceipt input)
    (LaboratoryStressEnergyCompilationInput.MomentumDensityReceipt input)
    (LaboratoryStressEnergyCompilationInput.momentumDensityReceipt input)
    (LaboratoryStressEnergyCompilationInput.StressComponentReceipt input)
    (LaboratoryStressEnergyCompilationInput.stressComponentReceipt input)
    (LaboratoryStressEnergyCompilationInput.FrameAndConventionReceipt input)
    (LaboratoryStressEnergyCompilationInput.frameAndConventionReceipt input)
    (LaboratoryStressEnergyCompilationInput.TensorAssemblyReceipt input)
    (LaboratoryStressEnergyCompilationInput.tensorAssemblyReceipt input)
    (LaboratoryStressEnergyCompilationInput.SameApparatusIdentityReceipt input)
    (LaboratoryStressEnergyCompilationInput.sameApparatusIdentityReceipt input)

------------------------------------------------------------------------
-- Reverse-search residuals after J_m is known.
------------------------------------------------------------------------

data PostMassCurrentStressEnergyResidual : Set where
  missingEnergyDensityAfterMassCurrent : PostMassCurrentStressEnergyResidual
  missingMomentumDensityAfterMassCurrent : PostMassCurrentStressEnergyResidual
  missingStressComponentsAfterMassCurrent : PostMassCurrentStressEnergyResidual
  missingFrameConventionAfterMassCurrent : PostMassCurrentStressEnergyResidual
  missingTensorAssemblyAfterMassCurrent : PostMassCurrentStressEnergyResidual
  missingSameApparatusIdentityAfterMassCurrent : PostMassCurrentStressEnergyResidual

producerForPostMassCurrentResidual :
  PostMassCurrentStressEnergyResidual → Search.ProducerClass
producerForPostMassCurrentResidual missingEnergyDensityAfterMassCurrent = Search.empiricalEvidenceProducer
producerForPostMassCurrentResidual missingMomentumDensityAfterMassCurrent = Search.empiricalEvidenceProducer
producerForPostMassCurrentResidual missingStressComponentsAfterMassCurrent = Search.empiricalEvidenceProducer
producerForPostMassCurrentResidual missingFrameConventionAfterMassCurrent = Search.identityProducer
producerForPostMassCurrentResidual missingTensorAssemblyAfterMassCurrent = Search.discriminatorProducer
producerForPostMassCurrentResidual missingSameApparatusIdentityAfterMassCurrent = Search.identityProducer

record LaboratoryStressEnergyCompilationBoundary : Set where
  constructor laboratory-stress-energy-compilation-boundary
  field
    massCurrentAloneConstructsStressEnergy : Bool
    energyDensityStillRequired : Bool
    momentumDensityStillRequired : Bool
    stressComponentsStillRequired : Bool
    frameConventionStillRequired : Bool
    tensorAssemblyStillRequired : Bool
    sameApparatusIdentityStillRequired : Bool
    compiledLabStressEnergyPaysW4Interface : Bool
    compiledLabStressEnergyProvesNegativeEffectiveG : Bool

canonicalLaboratoryStressEnergyCompilationBoundary :
  LaboratoryStressEnergyCompilationBoundary
canonicalLaboratoryStressEnergyCompilationBoundary =
  laboratory-stress-energy-compilation-boundary
    false true true true true true true false false
