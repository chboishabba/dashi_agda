module DASHI.EverythingTOESymmetryResolved369 where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)

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
import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Exact as YMTOE
import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Validation
import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound578Exact as YMCritical
import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound578Validation



------------------------------------------------------------------------
-- Exact Yang-Mills theorem-owner exports.
--
-- These names come from the normalized YM TOE owner.
-- No proof is copied here.
------------------------------------------------------------------------

open YMTOE public using
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

open YMTOE public using
  ( SourceFamily
  ; a1CurrentStepVariation
  ; a2HistoryCoordinate
  ; a3ProjectiveRepresentation
  ; finiteT1AndPublishedOS
  ; quantitativeT5CMP119Alignment
  ; bWilsonWEXT
  ; bSameHamiltonianEnergyDecay
  ; actualGroupCompleteSource
  ; densityToNormalizedFiniteMeasure
  ; c0WilsonLocalObservable
  ; c1MarkedCurvature
  ; c2PhysicalRemainderTail
  ; c3AFRecurrence
  ; c4DensityAnchoredStress
  ; CriticalFamily
  ; a3SelectedRepresentation
  ; t1FiniteOSSameFamily
  ; t5QuantitativeSameFamily
  ; b1SourceFirstWilsonWEXT
  ; b2SameHamiltonian
  ; g1ActualCompactSimple
  ; h6MinimalWardNontriviality
  )


------------------------------------------------------------------------
-- Direct Yang-Mills TOE exports.
--
-- These aliases keep the root fail-closed.
-- They do not create a second theorem owner.
------------------------------------------------------------------------

toe369YangMillsBetaDrivenSourceFlowLevel : ProofLevel
toe369YangMillsBetaDrivenSourceFlowLevel =
  YMTOE.toeBetaDrivenSourceFlowLevel

toe369YangMillsBetaHistorySameStateCouplingLevel : ProofLevel
toe369YangMillsBetaHistorySameStateCouplingLevel =
  YMTOE.toeBetaHistorySameStateCouplingLevel

toe369YangMillsCanonicalCompleteDensityLevel : ProofLevel
toe369YangMillsCanonicalCompleteDensityLevel =
  YMTOE.toeBetaHistoryToCanonicalCompleteDensityLevel

toe369YangMillsGeneratedActionDensityCompilerLevel : ProofLevel
toe369YangMillsGeneratedActionDensityCompilerLevel =
  YMTOE.toeUnifiedGeneratedActionDensityCompilerLevel

toe369YangMillsCombinedRGUnifiedActionCompilerLevel : ProofLevel
toe369YangMillsCombinedRGUnifiedActionCompilerLevel =
  YMTOE.toeCompleteDensityEffectiveActionRealizationCompilerLevel

toe369YangMillsRegularEProjectionLevel : ProofLevel
toe369YangMillsRegularEProjectionLevel =
  YMTOE.toePublishedFlowToRegularEProjectionCompilerLevel

toe369YangMillsRegularELocalizationSourceLevel : ProofLevel
toe369YangMillsRegularELocalizationSourceLevel =
  YMTOE.toeCMP119RegularELocalizationSourceLevel

toe369YangMillsStressScaleCompilerLevel : ProofLevel
toe369YangMillsStressScaleCompilerLevel =
  YMTOE.toeUnifiedGeneratedActionStressScaleCompilerLevel

toe369YangMillsStrictCasimirCarrierLevel : ProofLevel
toe369YangMillsStrictCasimirCarrierLevel =
  YMTOE.toeStrictCasimirCarrierCompilerLevel

toe369YangMillsPublishedRGDoesNotPromoteContinuum :
  YMTOE.toeFlat4DContinuumTransferProvedHere ≡ false
toe369YangMillsPublishedRGDoesNotPromoteContinuum =
  YMTOE.toePublishedRGDoesNotPromoteContinuum

toe369YangMillsGeneratedActionDensityDoesNotPromoteContinuum :
  YMTOE.toeFlat4DContinuumTransferProvedHere ≡ false
toe369YangMillsGeneratedActionDensityDoesNotPromoteContinuum =
  YMTOE.toeGeneratedActionDensityDoesNotPromoteContinuum

toe369YangMillsCombinedRGUnifiedActionDoesNotPromoteContinuum :
  YMTOE.toeFlat4DContinuumTransferProvedHere ≡ false
toe369YangMillsCombinedRGUnifiedActionDoesNotPromoteContinuum =
  YMTOE.toeCombinedRGUnifiedActionDoesNotPromoteContinuum

toe369YangMillsOSWightmanContinuumNotConstructed :
  YMTOE.toeOSWightmanContinuumConstructionProvedHere ≡ false
toe369YangMillsOSWightmanContinuumNotConstructed =
  YMTOE.toeOSWightmanContinuumConstructionProvedHereIsFalse

toe369YangMillsContinuumMassGapNotPromoted :
  YMTOE.toeContinuumMassGapPromoted ≡ false
toe369YangMillsContinuumMassGapNotPromoted =
  YMTOE.toeContinuumMassGapPromotedIsFalse

toe369YangMillsClayNotPromoted :
  YMTOE.toeClayYangMillsPromoted ≡ false
toe369YangMillsClayNotPromoted =
  YMTOE.toeClayYangMillsPromotedIsFalse

toe369YangMillsUniversalBetaFloorLevel : ProofLevel
toe369YangMillsUniversalBetaFloorLevel =
  YMTOE.toeCompactSimpleUniversalBetaFloorLevel

toe369YangMillsLiteralUniformRemainderFloorLevel : ProofLevel
toe369YangMillsLiteralUniformRemainderFloorLevel =
  YMTOE.toeLiteralUniformRegularRemainderBelowUniversalFloorLevel

toe369YangMillsStressMarkedShellBoundLevel : ProofLevel
toe369YangMillsStressMarkedShellBoundLevel =
  YMTOE.toeStressFirstVariationMarkedShellBoundLevel

toe369YangMillsStressShellEnergyHilbertLevel : ProofLevel
toe369YangMillsStressShellEnergyHilbertLevel =
  YMTOE.toeStressShellEnergyToHilbertCompilerLevel

toe369YangMillsLiteralStressActivityEntropyLevel : ProofLevel
toe369YangMillsLiteralStressActivityEntropyLevel =
  YMTOE.toeLiteralStressActivityEntropyInstantiationLevel


------------------------------------------------------------------------
-- Authoritative Goal-1 R485 maximum cut via normalized R559 owner.
------------------------------------------------------------------------

toe369YangMillsGoal1FiniteSymmetryAndRPSourceLevel : ProofLevel
toe369YangMillsGoal1FiniteSymmetryAndRPSourceLevel =
  YMTOE.toeGoal1FiniteSymmetryAndRPSourceLevel

toe369YangMillsGoal1A1CurrentStepBetaSourceLevel : ProofLevel
toe369YangMillsGoal1A1CurrentStepBetaSourceLevel =
  YMTOE.toeGoal1A1CurrentStepBetaSourceLevel

toe369YangMillsGoal1A3SourceNativeContinuumOSLevel : ProofLevel
toe369YangMillsGoal1A3SourceNativeContinuumOSLevel =
  YMTOE.toeGoal1A3SourceNativeContinuumOSLevel

toe369YangMillsGoal1A3CountablyAdditiveRepresentationLevel : ProofLevel
toe369YangMillsGoal1A3CountablyAdditiveRepresentationLevel =
  YMTOE.toeGoal1A3CountablyAdditiveRepresentationLevel

toe369YangMillsGoal1A4FiniteRegularityLevel : ProofLevel
toe369YangMillsGoal1A4FiniteRegularityLevel =
  YMTOE.toeGoal1A4FiniteRegularityLevel

toe369YangMillsGoal1A5FiniteGrowthLevel : ProofLevel
toe369YangMillsGoal1A5FiniteGrowthLevel =
  YMTOE.toeGoal1A5FiniteGrowthLevel

toe369YangMillsGoal1BWilsonTwoInsertionConnectedShellLevel : ProofLevel
toe369YangMillsGoal1BWilsonTwoInsertionConnectedShellLevel =
  YMTOE.toeGoal1BWilsonTwoInsertionConnectedShellLevel

toe369YangMillsGoal1BGeometricDecayCompilerLevel : ProofLevel
toe369YangMillsGoal1BGeometricDecayCompilerLevel =
  YMTOE.toeGoal1BGeometricDecayCompilerLevel

toe369YangMillsGoal1BStandardSpectralTransferLevel : ProofLevel
toe369YangMillsGoal1BStandardSpectralTransferLevel =
  YMTOE.toeGoal1BStandardSpectralTransferLevel

toe369YangMillsGoal1CSameFamilySourceInstantiationLevel : ProofLevel
toe369YangMillsGoal1CSameFamilySourceInstantiationLevel =
  YMTOE.toeGoal1CSameFamilySourceInstantiationLevel

toe369YangMillsGoal1G1ArbitraryCompactSimpleSourceMapLevel : ProofLevel
toe369YangMillsGoal1G1ArbitraryCompactSimpleSourceMapLevel =
  YMTOE.toeGoal1G1ArbitraryCompactSimpleSourceMapLevel

toe369YangMillsGoal1G2SameSystemNontrivialitySemanticsLevel : ProofLevel
toe369YangMillsGoal1G2SameSystemNontrivialitySemanticsLevel =
  YMTOE.toeGoal1G2SameSystemNontrivialitySemanticsLevel

toe369YangMillsGoal1MaximumCutCompilerLevel : ProofLevel
toe369YangMillsGoal1MaximumCutCompilerLevel =
  YMTOE.toeGoal1MaximumCutCompilerLevel

toe369YangMillsGoal1ProjectiveProkhorovNotMandatory :
  YMTOE.toeGoal1ProjectiveProkhorovMandatory ≡ false
toe369YangMillsGoal1ProjectiveProkhorovNotMandatory = refl

toe369YangMillsGoal1CompatibilityBRouteNotMandatory :
  YMTOE.toeGoal1CompatibilityBRouteMandatory ≡ false
toe369YangMillsGoal1CompatibilityBRouteNotMandatory = refl

toe369YangMillsGoal1ClayCompletionNotClaimed :
  YMTOE.toeGoal1ClayCompletionClaimed ≡ false
toe369YangMillsGoal1ClayCompletionNotClaimed = refl



------------------------------------------------------------------------
-- Current R578 Yang-Mills critical-path overlay.
-- R559 remains the canonical TOE owner.
-- R578 supplies the current shortest-source frontier.
------------------------------------------------------------------------

toe369YangMillsCurrentT1FiniteOSLevel : ProofLevel
toe369YangMillsCurrentT1FiniteOSLevel =
  YMCritical.criticalLevel YMCritical.t1FiniteOSSameFamily

toe369YangMillsCurrentT5LiteralMomentProducerLevel : ProofLevel
toe369YangMillsCurrentT5LiteralMomentProducerLevel =
  YMCritical.t5LiteralMomentProducerLevel

toe369YangMillsCurrentB1PointwiseWilsonLocalizationLevel : ProofLevel
toe369YangMillsCurrentB1PointwiseWilsonLocalizationLevel =
  YMCritical.b1PointwiseWilsonJetLocalizationLevel

toe369YangMillsCurrentB1ConnectingWeightTailLevel : ProofLevel
toe369YangMillsCurrentB1ConnectingWeightTailLevel =
  YMCritical.b1ConnectingWeightTailLevel

toe369YangMillsCurrentB2SameHamiltonianTransferLevel : ProofLevel
toe369YangMillsCurrentB2SameHamiltonianTransferLevel =
  YMCritical.b2TransferCoordinateOfReconstructedHamiltonianLevel

toe369YangMillsCurrentG1QuantitativeBoundsLevel : ProofLevel
toe369YangMillsCurrentG1QuantitativeBoundsLevel =
  YMCritical.g1ActualQuantitativeBoundsLevel

toe369YangMillsCurrentH6WardKernelLevel : ProofLevel
toe369YangMillsCurrentH6WardKernelLevel =
  YMCritical.h6SameFamilyWardKernelLevel

toe369YangMillsCurrentCriticalPathCompilerLevel : ProofLevel
toe369YangMillsCurrentCriticalPathCompilerLevel =
  YMCritical.round578CriticalPathCompilerLevel

toe369YangMillsCurrentArbitraryObservableDetourRequired :
  YMCritical.arbitraryObservableRepresentationRequired ≡ false
toe369YangMillsCurrentArbitraryObservableDetourRequired = refl

toe369YangMillsCurrentFiniteHamiltonianMoscoDetourRequired :
  YMCritical.finiteHamiltonianMoscoRouteRequired ≡ false
toe369YangMillsCurrentFiniteHamiltonianMoscoDetourRequired = refl

toe369YangMillsCurrentSU2ToGenericPromotionRequired :
  YMCritical.su2ToGenericPromotionRequired ≡ false
toe369YangMillsCurrentSU2ToGenericPromotionRequired = refl

------------------------------------------------------------------------
-- Canonical R546/R558 family dispatch via R559.
------------------------------------------------------------------------

toe369YangMillsIrreducibleFamilyLevel :
  SourceFamily → ProofLevel
toe369YangMillsIrreducibleFamilyLevel =
  YMTOE.toeIrreducibleFamilyLevel

toe369YangMillsCriticalFamilyLevel :
  CriticalFamily → ProofLevel
toe369YangMillsCriticalFamilyLevel =
  YMTOE.toeCriticalFamilyLevel

-- Literal two-Wilson source-native path.
open YMTOE public using
  ( LiteralTwoWilsonR413FourStageSource
  ; toeLiteralTwoWilsonR413ToR444
  ; LiteralTwoWilsonQuarterDyadicFamily
  ; toeLiteralTwoWilsonQuarterDyadicToR556
  ; toeLiteralTwoWilsonFiniteCovarianceBelowCanonicalDyadicShell
  ; LiteralTwoWilsonGeneralGeometricFamily
  ; toeLiteralTwoWilsonFiniteCovarianceGeneralGeometricBound
  ; toeLiteralTwoWilsonGeneralGeometricTrajectory
  )


open YMTOE public using
  ( toeLiteralTwoWilsonR415CompilerLevel
  ; toeLiteralTwoWilsonR444TermConstructionLevel
  ; toeLiteralTwoWilsonR445MixedLogIdentificationLevel
  ; toeLiteralTwoWilsonR453ConnectedCoreLevel
  ; toeLiteralTwoWilsonR451PhysicalCalibrationLevel
  )
