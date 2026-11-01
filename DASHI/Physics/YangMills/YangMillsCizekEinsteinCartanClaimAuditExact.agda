module DASHI.Physics.YangMills.YangMillsCizekEinsteinCartanClaimAuditExact where

------------------------------------------------------------------------
-- SOURCE AUDIT
--
-- Emmanouil Karolos Čižek,
-- "A Constructive Einstein–Cartan–Yang–Mills Theory with Positive Mass Gap
-- in Four Dimensions", version 1.1.0, self-hosted monograph / Zenodo deposit.
-- DOI: 10.5281/zenodo.17246443.
--
-- Emmanouil Karolos Čižek,
-- "A Structural and Conceptual Overview of A Constructive
-- Einstein–Cartan–Yang–Mills Theory with Positive Mass Gap in Four
-- Dimensions".
-- DOI: 10.5281/zenodo.17718647.
--
-- Emmanouil Karolos Čižek,
-- "Mixing of Boundary Langevin Dynamics for Regulated Four-Dimensional
-- Yang–Mills Slabs".
-- DOI: 10.5281/zenodo.18280110.
--
-- The monograph claims a reflection-positive continuum construction and a
-- positive Hamiltonian mass gap after decoupling Einstein–Cartan torsion by a
-- BRST-doublet argument.  The later slab paper is narrower and explicitly
-- separates an auxiliary boundary sampler from the Euclidean transfer kernel;
-- it records fixed-thickness/fixed-regulator or strong-coupling results and
-- does not construct the full R^4 continuum or long-time limit.
--
-- DASHI records both sources as mathematical claims to audit.  Neither the
-- gravitational/torsion extension nor either boundary operator is
-- definitionally the Clay theory or its reconstructed Hamiltonian.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.List.Base using (length)

import DASHI.Physics.YangMills.YangMillsPaperClaimAuditCarrierExact as Audit

data CizekSource : Set where
  einsteinCartanMonograph : CizekSource
  boundarySlabMixingPaper : CizekSource

data CizekClaim : Set where
  continuumEinsteinCartanYMWithGap : CizekClaim
  regulatedSlabTransferContraction : CizekClaim

data CizekAssumption : Set where
  regulatorUniformHarrisConstants : CizekAssumption
  reflectionPositiveGaugeInvariantSubalgebra : CizekAssumption
  nonperturbativeBRSTDoubletDecoupling : CizekAssumption
  slabDisintegrationDefinesTransferKernel : CizekAssumption
  fixedPositiveSlabThickness : CizekAssumption
  finiteRangeWilsonRegulator : CizekAssumption
  strongCouplingKPCorridor : CizekAssumption
  spatialThermodynamicUniformity : CizekAssumption

data CizekMissingBridge : Set where
  torsionGravitySectorExactlyDecouplesToPureYM : CizekMissingBridge
  auxiliarySamplerIntertwinesPhysicalTransferKernel : CizekMissingBridge
  ultravioletContinuumOnR4ActuallyConstructed : CizekMissingBridge
  longTimeSlabSemigroupLimitActuallyConstructed : CizekMissingBridge
  slabGapHasUniformPhysicalScaling : CizekMissingBridge
  localOperatorsStressTensorAndOPEConstructed : CizekMissingBridge
  everyCompactSimpleGroupHasDerivedConstants : CizekMissingBridge

monographAssumptions : List CizekAssumption
monographAssumptions =
  regulatorUniformHarrisConstants
  ∷ reflectionPositiveGaugeInvariantSubalgebra
  ∷ nonperturbativeBRSTDoubletDecoupling
  ∷ slabDisintegrationDefinesTransferKernel
  ∷ spatialThermodynamicUniformity
  ∷ []

monographAssumptionCountExact : length monographAssumptions ≡ 5
monographAssumptionCountExact = refl

monographRequiredBridges : List Audit.BridgeObligation
monographRequiredBridges = Audit.requiredPromotionBridges

monographBridgeCountExact : length monographRequiredBridges ≡ 10
monographBridgeCountExact = Audit.requiredPromotionBridgeCountExact

monographAudit : Audit.PaperClaimAudit
monographAudit = record
  { Audit.PaperClaimAudit.Source = CizekSource
  ; Audit.PaperClaimAudit.Claim = CizekClaim
  ; Audit.PaperClaimAudit.Assumption = CizekAssumption
  ; Audit.PaperClaimAudit.MissingBridge = CizekMissingBridge
  ; Audit.PaperClaimAudit.sourceStatus = Audit.repositoryDeposit
  ; Audit.PaperClaimAudit.sourceTheory =
      Audit.einsteinCartanYangMillsTheory
  ; Audit.PaperClaimAudit.claimedOperator =
      Audit.physicalReconstructedHamiltonian
  ; Audit.PaperClaimAudit.evidence = Audit.proofSketch
  ; Audit.PaperClaimAudit.outcome = Audit.firstDependencyOpen
  ; Audit.PaperClaimAudit.assumptions = monographAssumptions
  ; Audit.PaperClaimAudit.requiredBridges = monographRequiredBridges
  ; Audit.PaperClaimAudit.firstOpenDependency =
      torsionGravitySectorExactlyDecouplesToPureYM
  }

slabAssumptions : List CizekAssumption
slabAssumptions =
  slabDisintegrationDefinesTransferKernel
  ∷ fixedPositiveSlabThickness
  ∷ finiteRangeWilsonRegulator
  ∷ strongCouplingKPCorridor
  ∷ spatialThermodynamicUniformity
  ∷ []

slabAssumptionCountExact : length slabAssumptions ≡ 5
slabAssumptionCountExact = refl

slabRequiredBridges : List Audit.BridgeObligation
slabRequiredBridges =
  Audit.sameOperatorIntertwining
  ∷ Audit.continuumCutoffRemoval
  ∷ Audit.physicalGapScaleCompatibility
  ∷ Audit.noCircularGapInput
  ∷ Audit.allCompactSimpleGroupCoverage
  ∷ Audit.localOperatorAndOPEConstruction
  ∷ []

slabBridgeCountExact : length slabRequiredBridges ≡ 6
slabBridgeCountExact = refl

slabAudit : Audit.PaperClaimAudit
slabAudit = record
  { Audit.PaperClaimAudit.Source = CizekSource
  ; Audit.PaperClaimAudit.Claim = CizekClaim
  ; Audit.PaperClaimAudit.Assumption = CizekAssumption
  ; Audit.PaperClaimAudit.MissingBridge = CizekMissingBridge
  ; Audit.PaperClaimAudit.sourceStatus = Audit.repositoryDeposit
  ; Audit.PaperClaimAudit.sourceTheory = Audit.latticeYangMillsFixedSpacing
  ; Audit.PaperClaimAudit.claimedOperator = Audit.boundarySlabTransferKernel
  ; Audit.PaperClaimAudit.evidence = Audit.conditionalDerivation
  ; Audit.PaperClaimAudit.outcome = Audit.conditionalTheorem
  ; Audit.PaperClaimAudit.assumptions = slabAssumptions
  ; Audit.PaperClaimAudit.requiredBridges = slabRequiredBridges
  ; Audit.PaperClaimAudit.firstOpenDependency =
      ultravioletContinuumOnR4ActuallyConstructed
  }

monographTheoryIsNotDefinitionallyPureYM :
  Audit.sourceTheory monographAudit ≡ Audit.pureFourDimensionalYangMills → ⊥
monographTheoryIsNotDefinitionallyPureYM =
  Audit.einsteinCartanYangMillsIsNotDefinitionallyPureYangMills

slabKernelIsNotPhysicalHamiltonian :
  Audit.claimedOperator slabAudit ≡ Audit.physicalReconstructedHamiltonian → ⊥
slabKernelIsNotPhysicalHamiltonian =
  Audit.boundarySlabTransferKernelIsNotPhysicalHamiltonian

auxiliarySamplerCannotReplaceSlabKernel :
  Audit.auxiliaryBoundaryLangevinGenerator
  ≡ Audit.claimedOperator slabAudit → ⊥
auxiliarySamplerCannotReplaceSlabKernel =
  Audit.auxiliaryBoundaryLangevinIsNotSlabTransferKernel

monographEvidenceIsNotKernelProof :
  Audit.evidence monographAudit ≡ Audit.formalKernelProof → ⊥
monographEvidenceIsNotKernelProof ()

slabEvidenceIsNotKernelProof :
  Audit.evidence slabAudit ≡ Audit.formalKernelProof → ⊥
slabEvidenceIsNotKernelProof ()

monographOutcomeNotCheckedClayTheorem :
  Audit.outcome monographAudit ≡ Audit.checkedTheorem → ⊥
monographOutcomeNotCheckedClayTheorem ()

slabOutcomeRemainsConditional :
  Audit.outcome slabAudit ≡ Audit.conditionalTheorem
slabOutcomeRemainsConditional = refl
