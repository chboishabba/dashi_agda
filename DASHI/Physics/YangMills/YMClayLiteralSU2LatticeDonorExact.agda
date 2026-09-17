{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralSU2LatticeDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayAristotleDonorAtlasExact as Atlas

------------------------------------------------------------------------
-- Literal finite-spacing SU(2) Wilson Yang-Mills donor parity.
--
-- The supplied Lean archive constructs the literal finite theory.  Agda keeps
-- the exact semantic coordinates and theorem provenance without pretending that
-- the Mathlib measure/Lp construction is definitionally an Agda object.
------------------------------------------------------------------------

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

    uniformContinuumTrajectoryGapProved : Bool
    uniformContinuumTrajectoryGapProvedIsFalse :
      uniformContinuumTrajectoryGapProved ≡ false

    varyingHilbertCommonCarrierConstructed : Bool
    varyingHilbertCommonCarrierConstructedIsFalse :
      varyingHilbertCommonCarrierConstructed ≡ false

canonicalLiteralSU2LatticeLeanReceipt : LiteralSU2LatticeLeanReceipt
canonicalLiteralSU2LatticeLeanReceipt = record
  { finiteHamiltonianArtifact = Atlas.literalSU2HamiltonianLean
  ; coercivityToGapArtifact = Atlas.literalSU2MassGapFromCoercivityLean
  ; strongCouplingArtifact = Atlas.literalSU2StrongCouplingGapLean
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
  ; uniformContinuumTrajectoryGapProved = false
  ; uniformContinuumTrajectoryGapProvedIsFalse = refl
  ; varyingHilbertCommonCarrierConstructed = false
  ; varyingHilbertCommonCarrierConstructedIsFalse = refl
  }

-- Exact donor normalization retained in prose/type ownership:
--   q_a = a^-1 (1 - 1/2 (T + T*))
-- and the explicit fixed-spacing sufficient condition is
--   64 |beta| (n+1)^4 <= 1/10.
-- These are donor theorem coordinates, not generic continuum hypotheses.
literalFiniteSU2LatticeLeanLevel : ProofLevel
literalFiniteSU2LatticeLeanLevel = standardImported

literalFiniteSU2LatticeNativeAgdaKernelLevel : ProofLevel
literalFiniteSU2LatticeNativeAgdaKernelLevel = conditional

constructLiteralQaHaStillOutstanding : Bool
constructLiteralQaHaStillOutstanding = false

constructLiteralQaHaStillOutstandingIsFalse :
  constructLiteralQaHaStillOutstanding ≡ false
constructLiteralQaHaStillOutstandingIsFalse = refl

data LiteralSU2LatticeLeanDonorPresent : Set where
  literalSU2LatticeLeanDonorPresent : LiteralSU2LatticeLeanDonorPresent

literalSU2LatticeLeanDonorWitness : LiteralSU2LatticeLeanDonorPresent
literalSU2LatticeLeanDonorWitness = literalSU2LatticeLeanDonorPresent
