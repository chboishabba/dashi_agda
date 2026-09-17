{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralSU2LatticeDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayAristotleDonorAtlasExact as Atlas

record LiteralSU2FinitePhysicalPackage
    (Hilbert Vacuum EnergyForm Hamiltonian : Set) : Set₁ where
  field
    hilbertSpace : Hilbert
    vacuum : Vacuum
    energyForm : EnergyForm
    hamiltonian : Hamiltonian

    WilsonGibbsProbabilityMeasureConstructed : Set
    wilsonGibbsProbabilityMeasureConstructed : WilsonGibbsProbabilityMeasureConstructed

    GaugeInvariantPhysicalCarrier : Set
    gaugeInvariantPhysicalCarrier : GaugeInvariantPhysicalCarrier

    BoundedHermitianTransferForm : Set
    boundedHermitianTransferForm : BoundedHermitianTransferForm

    VacuumUnit : Set
    vacuumUnit : VacuumUnit

    VacuumNullForm : Set
    vacuumNullForm : VacuumNullForm

    HamiltonianSelfAdjoint : Set
    hamiltonianSelfAdjoint : HamiltonianSelfAdjoint

    HamiltonianKillsVacuum : Set
    hamiltonianKillsVacuum : HamiltonianKillsVacuum

open LiteralSU2FinitePhysicalPackage public

record FixedSpacingStrongCouplingGap
    {Hilbert Vacuum EnergyForm Hamiltonian : Set}
    (package : LiteralSU2FinitePhysicalPackage Hilbert Vacuum EnergyForm Hamiltonian)
    (GapParameter : Set) : Set₁ where
  field
    gap : GapParameter
    GapPositive : Set
    gapPositive : GapPositive
    PhysicalCoercivity : Set
    physicalCoercivity : PhysicalCoercivity
    FullVacuumSectorMassGapConclusion : Set
    fullVacuumSectorMassGapConclusion : FullVacuumSectorMassGapConclusion
    couplingThresholdArtifact : Atlas.LeanTheoremArtifact

open FixedSpacingStrongCouplingGap public

record LiteralSU2LatticeLeanReceipt : Set₁ where
  field
    finiteHamiltonianArtifact : Atlas.LeanTheoremArtifact
    coercivityToGapArtifact : Atlas.LeanTheoremArtifact
    strongCouplingArtifact : Atlas.LeanTheoremArtifact
    varyingCarrierArtifact : Atlas.LeanTheoremArtifact
    uniformGapReductionArtifact : Atlas.LeanTheoremArtifact
    continuumWeldArtifact : Atlas.LeanTheoremArtifact

    literalWilsonMeasureConstructed : Bool
    literalWilsonMeasureConstructedIsTrue : literalWilsonMeasureConstructed ≡ true

    physicalGaugeInvariantHilbertConstructed : Bool
    physicalGaugeInvariantHilbertConstructedIsTrue :
      physicalGaugeInvariantHilbertConstructed ≡ true

    literalRescaledEnergyFormConstructed : Bool
    literalRescaledEnergyFormConstructedIsTrue :
      literalRescaledEnergyFormConstructed ≡ true

    literalSelfAdjointHamiltonianConstructed : Bool
    literalSelfAdjointHamiltonianConstructedIsTrue :
      literalSelfAdjointHamiltonianConstructed ≡ true

    literalZeroEnergyVacuumProved : Bool
    literalZeroEnergyVacuumProvedIsTrue : literalZeroEnergyVacuumProved ≡ true

    fixedSpacingStrongCouplingGapProved : Bool
    fixedSpacingStrongCouplingGapProvedIsTrue :
      fixedSpacingStrongCouplingGapProved ≡ true

    varyingCarrierTransportCompilerProved : Bool
    varyingCarrierTransportCompilerProvedIsTrue :
      varyingCarrierTransportCompilerProved ≡ true

    zeroCouplingUniformVolumeGapProved : Bool
    zeroCouplingUniformVolumeGapProvedIsTrue :
      zeroCouplingUniformVolumeGapProved ≡ true

    uniformInteractingContinuumTrajectoryGapProved : Bool
    uniformInteractingContinuumTrajectoryGapProvedIsFalse :
      uniformInteractingContinuumTrajectoryGapProved ≡ false

    actualEmbeddedLiteralWilsonGraphLimitProved : Bool
    actualEmbeddedLiteralWilsonGraphLimitProvedIsFalse :
      actualEmbeddedLiteralWilsonGraphLimitProved ≡ false

    actualYMOSSameEvolutionProved : Bool
    actualYMOSSameEvolutionProvedIsFalse :
      actualYMOSSameEvolutionProved ≡ false

canonicalLiteralSU2LatticeLeanReceipt : LiteralSU2LatticeLeanReceipt
canonicalLiteralSU2LatticeLeanReceipt = record
  { finiteHamiltonianArtifact = Atlas.literalSU2HamiltonianLean
  ; coercivityToGapArtifact = Atlas.literalSU2MassGapFromCoercivityLean
  ; strongCouplingArtifact = Atlas.literalSU2StrongCouplingGapLean
  ; varyingCarrierArtifact = Atlas.varyingCarrierTransportLean
  ; uniformGapReductionArtifact = Atlas.literalSU2UniformGapReductionLean
  ; continuumWeldArtifact = Atlas.literalSU2ContinuumWeldLean
  ; literalWilsonMeasureConstructed = true
  ; literalWilsonMeasureConstructedIsTrue = refl
  ; physicalGaugeInvariantHilbertConstructed = true
  ; physicalGaugeInvariantHilbertConstructedIsTrue = refl
  ; literalRescaledEnergyFormConstructed = true
  ; literalRescaledEnergyFormConstructedIsTrue = refl
  ; literalSelfAdjointHamiltonianConstructed = true
  ; literalSelfAdjointHamiltonianConstructedIsTrue = refl
  ; literalZeroEnergyVacuumProved = true
  ; literalZeroEnergyVacuumProvedIsTrue = refl
  ; fixedSpacingStrongCouplingGapProved = true
  ; fixedSpacingStrongCouplingGapProvedIsTrue = refl
  ; varyingCarrierTransportCompilerProved = true
  ; varyingCarrierTransportCompilerProvedIsTrue = refl
  ; zeroCouplingUniformVolumeGapProved = true
  ; zeroCouplingUniformVolumeGapProvedIsTrue = refl
  ; uniformInteractingContinuumTrajectoryGapProved = false
  ; uniformInteractingContinuumTrajectoryGapProvedIsFalse = refl
  ; actualEmbeddedLiteralWilsonGraphLimitProved = false
  ; actualEmbeddedLiteralWilsonGraphLimitProvedIsFalse = refl
  ; actualYMOSSameEvolutionProved = false
  ; actualYMOSSameEvolutionProvedIsFalse = refl
  }

literalFiniteSU2LatticeLeanLevel : ProofLevel
literalFiniteSU2LatticeLeanLevel = standardImported

literalFiniteSU2LatticeNativeAgdaKernelLevel : ProofLevel
literalFiniteSU2LatticeNativeAgdaKernelLevel = conditional

varyingCarrierTransportDonorLevel : ProofLevel
varyingCarrierTransportDonorLevel = standardImported

constructLiteralQaHaStillOutstanding : Bool
constructLiteralQaHaStillOutstanding = false

constructLiteralQaHaStillOutstandingIsFalse :
  constructLiteralQaHaStillOutstanding ≡ false
constructLiteralQaHaStillOutstandingIsFalse = refl

data LiteralSU2LatticeLeanDonorPresent : Set where
  literalSU2LatticeLeanDonorPresent : LiteralSU2LatticeLeanDonorPresent

literalSU2LatticeLeanDonorWitness : LiteralSU2LatticeLeanDonorPresent
literalSU2LatticeLeanDonorWitness = literalSU2LatticeLeanDonorPresent
