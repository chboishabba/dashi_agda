module DASHI.EverythingTOESymmetryResolved369 where
import DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact as ParetoSnowballTOE
import DASHI.Unified.FleetFormalGapTargetTOEExact as FleetGapTOE
import DASHI.Unified.TOE369MaxCutKernelBidiTernaryExact as MaxCut369
import DASHI.Unified.SingularBasinCoarseRGTOEExact as SingularBasinTOE

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)
open import Data.Nat.Base using (ℕ)

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (false)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact
import DASHI.Unified.TOE369CoarseFineIntertwinerMaxCutExact as TOE369
import DASHI.Unified.TOE369CoarseFineIntertwinerMaxCutValidation
import DASHI.Unified.TOE369EisensteinReuseExact
-- Reuse existing selected-3B full-grade and projected-action NO-PROMOTION
-- proofs. A character or 90-dimensional carrier is not an action witness.
-- These imports are read-only. The original theorem owners are unchanged.
import DASHI.Reasoning.Trialectic369Selected3BFullGradeActionMaxCutExact as FullGrade
import DASHI.Reasoning.Trialectic369Selected3BProjectedActionMaxCutExact as Projected
import DASHI.Moonshine.MonsterGradedVOAActual3BKernelSameElementBidiExact as KernelSame
import DASHI.Moonshine.Base369Monster3BSingleActionProducerBidiExact as SingleAction
import DASHI.Wikimedia.IbrahimMonster3BLinearShortestFrontierCorrectionExact as Ibrahim
import DASHI.Reasoning.Trialectic369SchrodingerHZetaRecognitionMaxCutExact as HZeta
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Ternary27

-- Reuse the existing exact finite GR/quantum proof-term regression.
-- It contains a terminal physical non-promotion theorem.
-- Do not replace this import with DASHI.Unifier placeholder axioms.
import DASHI.Unified.GRQuantumProofTermRegression

-- Reuse the strict Balaban RG normalization and its fail-closed continuum boundary.
import DASHI.Unified.BalabanRGTOERegression as BalabanRGTOE

open BalabanRGTOE public using
  ( sourceCouplingIsBetaHistoryCoupling
  ; sourceSmallnessIsDerivedFromBetaHistory
  ; betaHistoryGivesRepositoryCouplingCap
  ; canonicalStateRunningCouplingIsBetaHistory
  ; betaHistoryAndSourceTheoremGiveLiteralInvariantRegion
  ; selectedDensityRepresentsExactBC1Potential
  ; selectedDensityRepresentsBC2InitialPotential
  ; stressSelectedDensityIndexIsUnifiedActionIndex
  ; sourceDerivativeBelowExistingMarkedShell
  ; stressCoefficientEnergyUniformBound
  ; stressPairingSquaredCauchyFromShellEnergy
  ; selectedRegularEIsLocalizedCompositeSum
  ; universalCompactSimpleCasimirFloor
  ; universalCompactSimpleBetaFloor
  ; classificationAdjointCasimirAtLeastTwo
  ; classificationGroupUniversalCoefficientAtLeastElevenTwelfths
  ; uniformRemainderBelowEveryCompactSimpleCoefficient
  )

toeBalabanRGBlockSpinTransferStillOpen :
  BalabanRGTOE.balabanRGBlockSpinTransferOpenFlag ≡ false
toeBalabanRGBlockSpinTransferStillOpen =
  BalabanRGTOE.balabanRGBlockSpinTransferStillOpen

toeBalabanRGUniformKPAbsorptionStillOpen :
  BalabanRGTOE.balabanRGUniformKPAbsorptionOpenFlag
  ≡ false
toeBalabanRGUniformKPAbsorptionStillOpen =
  BalabanRGTOE.balabanRGUniformKPAbsorptionStillOpen

toeBalabanRGContinuumConstructionStillOpen :
  BalabanRGTOE.balabanRGContinuumConstructionOpenFlag ≡ false
toeBalabanRGContinuumConstructionStillOpen =
  BalabanRGTOE.balabanRGContinuumConstructionStillOpen

toeBalabanRGContinuumMassGapStillOpen :
  BalabanRGTOE.balabanRGContinuumMassGapOpenFlag
  ≡ false
toeBalabanRGContinuumMassGapStillOpen =
  BalabanRGTOE.balabanRGContinuumMassGapStillOpen

toeBalabanRGClayPromotionStillFalse :
  BalabanRGTOE.balabanRGClayPromotionFlag ≡ false
toeBalabanRGClayPromotionStillFalse =
  BalabanRGTOE.balabanRGClayPromotionStillFalse

toeBalabanRGZKPFrame : BalabanRGTOE.BalabanTOEZKPFrame
toeBalabanRGZKPFrame =
  BalabanRGTOE.canonicalBalabanTOEZKPFrame

toeBalabanRGReceipt : BalabanRGTOE.BalabanRGTOEReceipt
toeBalabanRGReceipt =
  BalabanRGTOE.canonicalBalabanRGTOEReceipt

------------------------------------------------------------------------
-- Normalized Balaban density, regular-E, stress, and continuum surfaces.
------------------------------------------------------------------------

toeBalabanGeneratedActionDensityCompilerLevel : ProofLevel
toeBalabanGeneratedActionDensityCompilerLevel =
  BalabanRGTOE.balabanGeneratedActionDensityCompilerLevel

toeBalabanCombinedRGEffectiveActionCompilerLevel : ProofLevel
toeBalabanCombinedRGEffectiveActionCompilerLevel =
  BalabanRGTOE.balabanCombinedRGEffectiveActionCompilerLevel

toeBalabanGeneratedActionStressScaleCompilerLevel : ProofLevel
toeBalabanGeneratedActionStressScaleCompilerLevel =
  BalabanRGTOE.balabanGeneratedActionStressScaleCompilerLevel

toeBalabanPublishedFlowRegularEProjectionCompilerLevel : ProofLevel
toeBalabanPublishedFlowRegularEProjectionCompilerLevel =
  BalabanRGTOE.balabanPublishedFlowRegularEProjectionCompilerLevel

toeBalabanRegularESection2PredicateCompilerLevel : ProofLevel
toeBalabanRegularESection2PredicateCompilerLevel =
  BalabanRGTOE.balabanRegularESection2PredicateCompilerLevel

toeBalabanConcreteRegularELocalizationWitnessLevel : ProofLevel
toeBalabanConcreteRegularELocalizationWitnessLevel =
  BalabanRGTOE.balabanConcreteRegularELocalizationWitnessLevel

toeBalabanPublishedNonlinearRGCoreLevel : ProofLevel
toeBalabanPublishedNonlinearRGCoreLevel =
  BalabanRGTOE.balabanPublishedNonlinearRGCoreLevel

toeBalabanPublishedRGPhysicalSameObjectLevel : ProofLevel
toeBalabanPublishedRGPhysicalSameObjectLevel =
  BalabanRGTOE.balabanPublishedRGPhysicalSameObjectLevel

toeBalabanPublishedRGContinuumTransferStillOpen :
  BalabanRGTOE.balabanPublishedRGContinuumTransferOpenFlag ≡ false
toeBalabanPublishedRGContinuumTransferStillOpen =
  BalabanRGTOE.balabanPublishedRGContinuumTransferStillOpen

toeBalabanOSWightmanContinuumConstructionStillOpen :
  BalabanRGTOE.balabanOSWightmanContinuumConstructionOpenFlag ≡ false
toeBalabanOSWightmanContinuumConstructionStillOpen =
  BalabanRGTOE.balabanOSWightmanContinuumConstructionStillOpen

toeBalabanContinuumRouteMassGapPromotionStillOpen :
  BalabanRGTOE.balabanContinuumRouteMassGapPromotionOpenFlag ≡ false
toeBalabanContinuumRouteMassGapPromotionStillOpen =
  BalabanRGTOE.balabanContinuumRouteMassGapPromotionStillOpen

toeBalabanTerminalPromotionStillOpen :
  BalabanRGTOE.balabanTerminalPromotionOpenFlag ≡ false
toeBalabanTerminalPromotionStillOpen =
  BalabanRGTOE.balabanTerminalPromotionStillOpen
