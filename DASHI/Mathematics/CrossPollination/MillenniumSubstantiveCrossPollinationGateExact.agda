module DASHI.Mathematics.CrossPollination.MillenniumSubstantiveCrossPollinationGateExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Central audit for the seven Clay Millennium problems plus the adjacent
-- graded-VOA/Moonshine research lane.  Each problem receives an exact local
-- core, an explicit conjecture/theorem boundary, and named bridges into
-- existing repository owners.  The status constructors prevent a checked
-- finite identity from being confused with a solved Millennium problem.
--
-- This file now includes Navier--Stokes and Yang--Mills explicitly rather than
-- leaving those two deep standalone programmes outside the central index.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Analysis.RiemannMaassMoonshineCrossPollinationExact
import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineHodgeDiamondExact
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineCycleClassExact
import DASHI.Mathematics.AlgebraicGeometry.HodgeNoetherianVOACrossPollination
import DASHI.Mathematics.Arithmetic.EllipticCurveF5PointEnumerationExact
import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact
import DASHI.Mathematics.Arithmetic.BirchSwinnertonDyerBoundary
import DASHI.Mathematics.Arithmetic.EllipticCurveHodgeFrobeniusCrossPollination
import DASHI.Mathematics.Complexity.DeterministicNondeterministicMachineExact
import DASHI.Mathematics.Complexity.PolynomialReductionExact
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary
import DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact
import DASHI.Mathematics.NumberTheory.RiemannCompletedZetaBoundary
import DASHI.Mathematics.Topology.RoundThreeSphereRicciFlowExact
import DASHI.Mathematics.Topology.PoincareGeometrizationExactBoundary
import DASHI.Mathematics.Topology.QuaternionS3PoincareCrossPollination
import DASHI.Moonshine.TrivialRationalGradedVertexAlgebraExact
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary
import DASHI.Moonshine.MonsterGradedVOABridgeExact

import DASHI.Papers.NavierStokes.TheoremInterface as NS
import DASHI.Physics.YangMills.YangMillsSubmissionExactCutset as YM
import DASHI.Physics.YangMills.CompactLieProofLevel as YMLevel

import DASHI.Mathematics.CrossPollination.EisensteinObserverRecoverableQuotientExact as EisensteinObserver

------------------------------------------------------------------------
-- The seven Clay lanes, with one explicitly adjacent non-Clay research lane.
------------------------------------------------------------------------

data ProblemLane : Set where
  riemannLane
  hodgeLane
  bsdLane
  pVersusNPLane
  navierStokesLane
  yangMillsLane
  poincareHistoricalLane
  gradedVOAMoonshineLane

clayProblemLaneCount : Nat
clayProblemLaneCount = 7

openClayProblemLaneCount : Nat
openClayProblemLaneCount = 6

data LocalSurfaceKind : Set where
  exactFiniteCore
  proofBearingGenericTheorem
  analyticOrGeometricBoundary
  externalClassificationBoundary
  completedMillenniumProof

record LaneStatus : Set where
  constructor laneStatus
  field
    lane : ProblemLane
    exactCorePresent : LocalSurfaceKind
    conjectureBoundaryPresent : LocalSurfaceKind
    crossPollinationPresent : LocalSurfaceKind
    finalClosureStatus : LocalSurfaceKind

open LaneStatus public

riemannStatus : LaneStatus
riemannStatus = laneStatus
  riemannLane
  exactFiniteCore
  analyticOrGeometricBoundary
  proofBearingGenericTheorem
  analyticOrGeometricBoundary

hodgeStatus : LaneStatus
hodgeStatus = laneStatus
  hodgeLane
  exactFiniteCore
  analyticOrGeometricBoundary
  proofBearingGenericTheorem
  analyticOrGeometricBoundary

bsdStatus : LaneStatus
bsdStatus = laneStatus
  bsdLane
  exactFiniteCore
  analyticOrGeometricBoundary
  proofBearingGenericTheorem
  analyticOrGeometricBoundary

pVersusNPStatus : LaneStatus
pVersusNPStatus = laneStatus
  pVersusNPLane
  proofBearingGenericTheorem
  analyticOrGeometricBoundary
  proofBearingGenericTheorem
  analyticOrGeometricBoundary

navierStokesStatus : LaneStatus
navierStokesStatus = laneStatus
  navierStokesLane
  proofBearingGenericTheorem
  analyticOrGeometricBoundary
  proofBearingGenericTheorem
  analyticOrGeometricBoundary

yangMillsStatus : LaneStatus
yangMillsStatus = laneStatus
  yangMillsLane
  proofBearingGenericTheorem
  analyticOrGeometricBoundary
  proofBearingGenericTheorem
  analyticOrGeometricBoundary

poincareHistoricalStatus : LaneStatus
poincareHistoricalStatus = laneStatus
  poincareHistoricalLane
  exactFiniteCore
  externalClassificationBoundary
  proofBearingGenericTheorem
  externalClassificationBoundary

gradedVOAStatus : LaneStatus
gradedVOAStatus = laneStatus
  gradedVOAMoonshineLane
  exactFiniteCore
  analyticOrGeometricBoundary
  proofBearingGenericTheorem
  analyticOrGeometricBoundary

------------------------------------------------------------------------
-- Backward-compatible four-lane theorem retained, then the complete six-open
-- Clay theorem.
------------------------------------------------------------------------

allOpenLanesRemainUncompleted :
  finalClosureStatus riemannStatus ≡ analyticOrGeometricBoundary
  × finalClosureStatus hodgeStatus ≡ analyticOrGeometricBoundary
  × finalClosureStatus bsdStatus ≡ analyticOrGeometricBoundary
  × finalClosureStatus pVersusNPStatus ≡ analyticOrGeometricBoundary
allOpenLanesRemainUncompleted = refl , refl , refl , refl

allOpenClayLanesRemainUncompleted :
  finalClosureStatus riemannStatus ≡ analyticOrGeometricBoundary
  × finalClosureStatus hodgeStatus ≡ analyticOrGeometricBoundary
  × finalClosureStatus bsdStatus ≡ analyticOrGeometricBoundary
  × finalClosureStatus pVersusNPStatus ≡ analyticOrGeometricBoundary
  × finalClosureStatus navierStokesStatus ≡ analyticOrGeometricBoundary
  × finalClosureStatus yangMillsStatus ≡ analyticOrGeometricBoundary
allOpenClayLanesRemainUncompleted =
  refl , refl , refl , refl , refl , refl

gradedVOANowHasExactFiniteCore :
  exactCorePresent gradedVOAStatus ≡ exactFiniteCore
gradedVOANowHasExactFiniteCore = refl

poincareUsesExternalSolvedTheoremBoundary :
  finalClosureStatus poincareHistoricalStatus
  ≡ externalClassificationBoundary
poincareUsesExternalSolvedTheoremBoundary = refl

------------------------------------------------------------------------
-- Same-object terminal guards imported from the mature standalone NS/YM lanes.
------------------------------------------------------------------------

navierStokesClayTerminalPromotionStillFalse :
  NS.NSPaperTheoremStatus.clayTerminalPromotion
    NS.canonicalNSPaperTheoremStatus
  ≡ false
navierStokesClayTerminalPromotionStillFalse =
  NS.NSPaperTheoremStatus.clayTerminalPromotionIsFalse
    NS.canonicalNSPaperTheoremStatus

yangMillsFullCutsetInhabitantsRemainConditional :
  YM.submissionFullCutsetInhabitantsLevel ≡ YMLevel.conditional
yangMillsFullCutsetInhabitantsRemainConditional = refl

------------------------------------------------------------------------
-- Cross-pollination edges.
------------------------------------------------------------------------

data CrossPollinationEdge : Set where
  maassSpectrumToRiemannHilbertPolya
  gradedVOATraceToModularSeries
  voaModularityToRiemannTransform
  noetherianityToAlgebraicCycles
  projectiveLineCyclesToH11
  ellipticCurveToHodgeRealization
  arithmeticFrobeniusToLocalEulerFactor
  localEulerFactorsToBSDGlobalLFunction
  deterministicMachineToNondeterministicMachine
  kleinInvariantToGCTOrbitSeparation
  unitQuaternionsToRoundThreeSphere
  ricciGeometrizationToPoincare
  eisensteinPhaseToConsumerDescent

record ImplementedEdge : Set where
  constructor implementedEdge
  field
    edge : CrossPollinationEdge
    exactLocalTheoremOrTypedBridge : LocalSurfaceKind

riemannMaassEdge : ImplementedEdge
riemannMaassEdge =
  implementedEdge maassSpectrumToRiemannHilbertPolya
    proofBearingGenericTheorem

projectiveLineCycleEdge : ImplementedEdge
projectiveLineCycleEdge =
  implementedEdge projectiveLineCyclesToH11 exactFiniteCore

hodgeEllipticEdge : ImplementedEdge
hodgeEllipticEdge =
  implementedEdge ellipticCurveToHodgeRealization
    proofBearingGenericTheorem

machineEmbeddingEdge : ImplementedEdge
machineEmbeddingEdge =
  implementedEdge deterministicMachineToNondeterministicMachine
    proofBearingGenericTheorem

complexityKleinEdge : ImplementedEdge
complexityKleinEdge =
  implementedEdge kleinInvariantToGCTOrbitSeparation
    proofBearingGenericTheorem

poincareQuaternionEdge : ImplementedEdge
poincareQuaternionEdge =
  implementedEdge unitQuaternionsToRoundThreeSphere
    proofBearingGenericTheorem

eisensteinObserverEdge : ImplementedEdge
eisensteinObserverEdge =
  implementedEdge eisensteinPhaseToConsumerDescent
    proofBearingGenericTheorem

------------------------------------------------------------------------
-- Exact witness behind the Eisenstein observer edge:
--   * phase is sufficient for the chi_-3 consumer;
--   * phase is not sufficient for the identity consumer;
--   * phase + residual reopens the full integer exactly.
-- These are theorem-level distinctions, not a status-table analogy.
------------------------------------------------------------------------

eisensteinPhasePaysChiConsumer =
  EisensteinObserver.phaseIsSufficientForChiMinus3

eisensteinPhaseDoesNotPayIdentityConsumer =
  EisensteinObserver.phaseCannotPayIdentityConsumer

eisensteinPhaseResidualReopens =
  EisensteinObserver.reopenPhaseQuotient

completedStatusIsDistinctFromBoundary :
  completedMillenniumProof ≡ analyticOrGeometricBoundary → ⊥
completedStatusIsDistinctFromBoundary ()
