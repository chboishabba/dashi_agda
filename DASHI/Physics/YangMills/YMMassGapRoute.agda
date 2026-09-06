module DASHI.Physics.YangMills.YMMassGapRoute where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanSU2GeometryQ0Bundle
import DASHI.Physics.YangMills.BalabanFiniteOneStepFrontierBundle
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

open import DASHI.Geometry.Gauge.SUNPrimitives
open import DASHI.Geometry.Gauge.SUNLane
open import DASHI.Physics.YangMills.YMMassGapTarget
open import DASHI.Physics.YangMills.LatticeYangMills
open import DASHI.Physics.YangMills.BalabanRGLane
open import DASHI.Physics.YangMills.OSAxiomBundle
open import DASHI.Physics.YangMills.WightmanReconstructionLane
open import DASHI.Physics.YangMills.MassGapSpectralStatement
open import DASHI.Physics.YangMills.O4RestorationLane

record YMMassGapRoute (N : Nat) : Setω where
  field
    sunLane : SUNLane N
    target : YMMassGapTarget N
    lattice : LatticeYangMills N
    balabanRG : BalabanRGLane
    osBundle : OSAxiomBundle
    wightman : WightmanReconstructionLane
    spectralGap : MassGapSpectralStatement
    o4Restoration : O4RestorationLane
    operatorContinuumFrontier : Frontier.YMOperatorContinuumFrontier

    eq119CompilerThroughRound184Available : Bool
    eq119SelectedBackgroundAndCutPhysicalInstantiationClosed : Bool

    gaugeInvariantSubspaceCarrierSelected : Bool
    gaugeOrbitConfigurationQuotientRequired : Bool
    finiteSelectedHodgeVariationPairingAvailable : Bool
    physicalSelectedVariationPairingPromoted : Bool
    physicalActionVariationHamiltonianSameObjectClosed : Bool

    generatorUniquenessAvailable : Bool
    symmetryNullPreservationAvailable : Bool
    gaugeInvariantCarrierAvailable : Bool
    boundedStrongLimitGapTransportAvailable : Bool
    vacuumRecoveryGapCompilerAvailable : Bool
    denseCoreSpectralExclusionCompilerAvailable : Bool

    physicalPartialDomainHamiltonianClosed : Bool
    physicalCommonInvariantDenseCoreClosed : Bool
    physicalSelfAdjointSelectedYMFormClosed : Bool
    physicalVacuumRecoverySystemClosed : Bool
    physicalDenseCoreProducerClosed : Bool
    ymEqualsOSEvolutionClosed : Bool
    physicalClosedFormOrResolventIdentificationClosed : Bool
    finiteToContinuumConstructionClosed : Bool
    physicalContinuumOSWightmanClosed : Bool

    logSobolev : Bool
    witten : Bool
    qit : Bool
    clayYangMillsPromotedRoute : Bool

    eq119CompilerThroughRound184AvailableIsTrue :
      eq119CompilerThroughRound184Available ≡ true
    eq119SelectedBackgroundAndCutPhysicalInstantiationClosedIsFalse :
      eq119SelectedBackgroundAndCutPhysicalInstantiationClosed ≡ false

    gaugeInvariantSubspaceCarrierSelectedIsTrue :
      gaugeInvariantSubspaceCarrierSelected ≡ true
    gaugeOrbitConfigurationQuotientRequiredIsFalse :
      gaugeOrbitConfigurationQuotientRequired ≡ false
    finiteSelectedHodgeVariationPairingAvailableIsTrue :
      finiteSelectedHodgeVariationPairingAvailable ≡ true
    physicalSelectedVariationPairingPromotedIsFalse :
      physicalSelectedVariationPairingPromoted ≡ false
    physicalActionVariationHamiltonianSameObjectClosedIsFalse :
      physicalActionVariationHamiltonianSameObjectClosed ≡ false

    generatorUniquenessAvailableIsTrue : generatorUniquenessAvailable ≡ true
    symmetryNullPreservationAvailableIsTrue : symmetryNullPreservationAvailable ≡ true
    gaugeInvariantCarrierAvailableIsTrue : gaugeInvariantCarrierAvailable ≡ true
    boundedStrongLimitGapTransportAvailableIsTrue : boundedStrongLimitGapTransportAvailable ≡ true
    vacuumRecoveryGapCompilerAvailableIsTrue : vacuumRecoveryGapCompilerAvailable ≡ true
    denseCoreSpectralExclusionCompilerAvailableIsTrue : denseCoreSpectralExclusionCompilerAvailable ≡ true

    physicalPartialDomainHamiltonianClosedIsFalse : physicalPartialDomainHamiltonianClosed ≡ false
    physicalCommonInvariantDenseCoreClosedIsFalse : physicalCommonInvariantDenseCoreClosed ≡ false
    physicalSelfAdjointSelectedYMFormClosedIsFalse : physicalSelfAdjointSelectedYMFormClosed ≡ false
    physicalVacuumRecoverySystemClosedIsFalse : physicalVacuumRecoverySystemClosed ≡ false
    physicalDenseCoreProducerClosedIsFalse : physicalDenseCoreProducerClosed ≡ false
    ymEqualsOSEvolutionClosedIsFalse : ymEqualsOSEvolutionClosed ≡ false
    physicalClosedFormOrResolventIdentificationClosedIsFalse : physicalClosedFormOrResolventIdentificationClosed ≡ false
    finiteToContinuumConstructionClosedIsFalse : finiteToContinuumConstructionClosed ≡ false
    physicalContinuumOSWightmanClosedIsFalse : physicalContinuumOSWightmanClosed ≡ false

    logSobolevIsFalse : logSobolev ≡ false
    wittenIsFalse : witten ≡ false
    qitIsFalse : qit ≡ false
    clayYangMillsPromotedRouteIsFalse : clayYangMillsPromotedRoute ≡ false
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalYMMassGapRoute : (N : Nat) → YMMassGapRoute N
canonicalYMMassGapRoute N = record
  { sunLane = canonicalSUNLane N
  ; target = canonicalYMMassGapTarget N
  ; lattice = canonicalLatticeYangMills N
  ; balabanRG = canonicalBalabanRGLane
  ; osBundle = canonicalOSAxiomBundle
  ; wightman = canonicalWightmanReconstructionLane
  ; spectralGap = canonicalMassGapSpectralStatement
  ; o4Restoration = canonicalO4RestorationLane
  ; operatorContinuumFrontier = Frontier.canonicalYMOperatorContinuumFrontier

  ; eq119CompilerThroughRound184Available = Frontier.cmp98Equation119CompilerThroughRound184Closed Frontier.canonicalYMOperatorContinuumFrontier
  ; eq119SelectedBackgroundAndCutPhysicalInstantiationClosed = Frontier.cmp98SelectedBackgroundAndCutPhysicalInstantiationClosed Frontier.canonicalYMOperatorContinuumFrontier

  ; gaugeInvariantSubspaceCarrierSelected = Frontier.gaugeInvariantSubspaceCarrierRouteSelected Frontier.canonicalYMOperatorContinuumFrontier
  ; gaugeOrbitConfigurationQuotientRequired = Frontier.gaugeOrbitConfigurationQuotientRequiredForSelectedCarrier Frontier.canonicalYMOperatorContinuumFrontier
  ; finiteSelectedHodgeVariationPairingAvailable = Frontier.finiteSelectedHodgeVariationPairingClosed Frontier.canonicalYMOperatorContinuumFrontier
  ; physicalSelectedVariationPairingPromoted = Frontier.physicalSelectedVariationPairingPromoted Frontier.canonicalYMOperatorContinuumFrontier
  ; physicalActionVariationHamiltonianSameObjectClosed = Frontier.physicalActionVariationHamiltonianSameObjectClosed Frontier.canonicalYMOperatorContinuumFrontier

  ; generatorUniquenessAvailable = Frontier.generatorUniquenessClosedWithoutBoundednessHypothesisOnTotalMaps Frontier.canonicalYMOperatorContinuumFrontier
  ; symmetryNullPreservationAvailable = Frontier.symmetryImpliesNullPreservationClosedForTotalLinearMaps Frontier.canonicalYMOperatorContinuumFrontier
  ; gaugeInvariantCarrierAvailable = Frontier.gaugeInvariantL2CarrierClosed Frontier.canonicalYMOperatorContinuumFrontier
  ; boundedStrongLimitGapTransportAvailable = Frontier.boundedStrongLimitFormGapTransportClosed Frontier.canonicalYMOperatorContinuumFrontier
  ; vacuumRecoveryGapCompilerAvailable = Frontier.vacuumOrthogonalRecoveryGapCompilerClosed Frontier.canonicalYMOperatorContinuumFrontier
  ; denseCoreSpectralExclusionCompilerAvailable = Frontier.denseCoreSpectralExclusionCompilerClosed Frontier.canonicalYMOperatorContinuumFrontier

  ; physicalPartialDomainHamiltonianClosed = Frontier.genuinePartialDomainHamiltonianFormalized Frontier.canonicalYMOperatorContinuumFrontier
  ; physicalCommonInvariantDenseCoreClosed = Frontier.commonInvariantDensePhysicalCoreConstructed Frontier.canonicalYMOperatorContinuumFrontier
  ; physicalSelfAdjointSelectedYMFormClosed = Frontier.physicalSelfAdjointSelectedYMFormClosed Frontier.canonicalYMOperatorContinuumFrontier
  ; physicalVacuumRecoverySystemClosed = Frontier.physicalVacuumRecoverySystemConstructed Frontier.canonicalYMOperatorContinuumFrontier
  ; physicalDenseCoreProducerClosed = Frontier.physicalDenseCoreClusteringContinuityProducerClosed Frontier.canonicalYMOperatorContinuumFrontier
  ; ymEqualsOSEvolutionClosed = Frontier.ymEvolutionEqualsOSReconstructedEvolutionClosed Frontier.canonicalYMOperatorContinuumFrontier
  ; physicalClosedFormOrResolventIdentificationClosed = Frontier.physicalClosedFormOrResolventIdentificationClosed Frontier.canonicalYMOperatorContinuumFrontier
  ; finiteToContinuumConstructionClosed = Frontier.finiteToContinuumYMConstructionClosed Frontier.canonicalYMOperatorContinuumFrontier
  ; physicalContinuumOSWightmanClosed = Frontier.continuumOSWightmanPackageClosed Frontier.canonicalYMOperatorContinuumFrontier

  ; logSobolev = false
  ; witten = false
  ; qit = false
  ; clayYangMillsPromotedRoute = false

  ; eq119CompilerThroughRound184AvailableIsTrue = refl
  ; eq119SelectedBackgroundAndCutPhysicalInstantiationClosedIsFalse = refl
  ; gaugeInvariantSubspaceCarrierSelectedIsTrue = refl
  ; gaugeOrbitConfigurationQuotientRequiredIsFalse = refl
  ; finiteSelectedHodgeVariationPairingAvailableIsTrue = refl
  ; physicalSelectedVariationPairingPromotedIsFalse = refl
  ; physicalActionVariationHamiltonianSameObjectClosedIsFalse = refl
  ; generatorUniquenessAvailableIsTrue = refl
  ; symmetryNullPreservationAvailableIsTrue = refl
  ; gaugeInvariantCarrierAvailableIsTrue = refl
  ; boundedStrongLimitGapTransportAvailableIsTrue = refl
  ; vacuumRecoveryGapCompilerAvailableIsTrue = refl
  ; denseCoreSpectralExclusionCompilerAvailableIsTrue = refl
  ; physicalPartialDomainHamiltonianClosedIsFalse = refl
  ; physicalCommonInvariantDenseCoreClosedIsFalse = refl
  ; physicalSelfAdjointSelectedYMFormClosedIsFalse = refl
  ; physicalVacuumRecoverySystemClosedIsFalse = refl
  ; physicalDenseCoreProducerClosedIsFalse = refl
  ; ymEqualsOSEvolutionClosedIsFalse = refl
  ; physicalClosedFormOrResolventIdentificationClosedIsFalse = refl
  ; finiteToContinuumConstructionClosedIsFalse = refl
  ; physicalContinuumOSWightmanClosedIsFalse = refl
  ; logSobolevIsFalse = refl
  ; wittenIsFalse = refl
  ; qitIsFalse = refl
  ; clayYangMillsPromotedRouteIsFalse = refl
  ; noClayPromotion = refl
  }
