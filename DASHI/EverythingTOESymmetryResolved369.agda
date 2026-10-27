module DASHI.EverythingTOESymmetryResolved369 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (false)

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact

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

toeBalabanGeneratedActionDensityCompilerLevel =
  BalabanRGTOE.balabanGeneratedActionDensityCompilerLevel

toeBalabanCombinedRGEffectiveActionCompilerLevel =
  BalabanRGTOE.balabanCombinedRGEffectiveActionCompilerLevel

toeBalabanGeneratedActionStressScaleCompilerLevel =
  BalabanRGTOE.balabanGeneratedActionStressScaleCompilerLevel

toeBalabanPublishedFlowRegularEProjectionCompilerLevel =
  BalabanRGTOE.balabanPublishedFlowRegularEProjectionCompilerLevel

toeBalabanRegularESection2PredicateCompilerLevel =
  BalabanRGTOE.balabanRegularESection2PredicateCompilerLevel

toeBalabanConcreteRegularELocalizationWitnessLevel =
  BalabanRGTOE.balabanConcreteRegularELocalizationWitnessLevel

toeBalabanPublishedNonlinearRGCoreLevel =
  BalabanRGTOE.balabanPublishedNonlinearRGCoreLevel

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
