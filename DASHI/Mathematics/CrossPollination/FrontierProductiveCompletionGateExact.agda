module DASHI.Mathematics.CrossPollination.FrontierProductiveCompletionGateExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Finite status gate for the productive-completion tranche.  Every lane now
-- has an inhabited local theorem or exact finite model.  The gate preserves
-- the distinction between those results and the missing global analytic,
-- arithmetic, complexity or continuum closure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Topology.FiniteCochainComplexExact
import DASHI.Mathematics.LinearAlgebra.FiniteHodgeEnergyExact
import DASHI.Mathematics.LinearAlgebra.RationalThreeWayHodgeDecompositionExact
import DASHI.Mathematics.NumberTheory.FiniteEulerProductExact
import DASHI.Mathematics.NumberTheory.FiniteMultiplicativeDirichletExact
import DASHI.Mathematics.Automorphic.TruncatedLFunctionExact
import DASHI.Mathematics.Automorphic.MellinSplitFunctionalEquationExact
import DASHI.Mathematics.Arithmetic.EllipticCurveSmallPrimeFrobeniusExact
import DASHI.Mathematics.Arithmetic.SmallPrimeTruncatedEulerProductExact
import DASHI.Mathematics.Arithmetic.EllipticCurveTwoTorsionAndBadPrimeExact
import DASHI.Mathematics.Complexity.PSubsetNPTrivialCertificateExact
import DASHI.Mathematics.Complexity.MachineRunCertificateExact
import DASHI.Mathematics.Complexity.FiniteCookLevinTableauExact
import DASHI.Moonshine.SquareZeroDifferentialVertexAlgebraExact
import DASHI.Moonshine.RankOneFockPartitionGradingExact
import DASHI.Moonshine.RankOneFockEulerProductPrefixExact
import DASHI.Analysis.SharedFiniteSpectralCertificationExact
import DASHI.Physics.YangMills.FiniteAbelianGaugeHodgeExact
import DASHI.Physics.YangMills.YangMillsHodgeCoercivityFrontierExact
import DASHI.Physics.Closure.NavierStokesFiniteVorticityDepletionExact

data FrontierLane : Set where
  cochainHodgeLane
  automorphicLFunctionLane
  bsdArithmeticLane
  complexityLane
  gradedVertexLane
  spectralCertificationLane
  yangMillsLane
  navierStokesLane

data CompletionStage : Set where
  exactFiniteTheorem
  proofBearingGenericTheorem
  finiteCrossPollinationBridge
  analyticBoundary
  arithmeticBoundary
  continuumBoundary
  openProblemClosure

record FrontierLaneStatus : Set where
  constructor frontierLaneStatus
  field
    lane : FrontierLane
    localCore : CompletionStage
    sharedBridge : CompletionStage
    globalClosure : CompletionStage

open FrontierLaneStatus public

cochainHodgeStatus : FrontierLaneStatus
cochainHodgeStatus = frontierLaneStatus
  cochainHodgeLane proofBearingGenericTheorem
  finiteCrossPollinationBridge analyticBoundary

automorphicStatus : FrontierLaneStatus
automorphicStatus = frontierLaneStatus
  automorphicLFunctionLane proofBearingGenericTheorem
  finiteCrossPollinationBridge analyticBoundary

bsdStatus : FrontierLaneStatus
bsdStatus = frontierLaneStatus
  bsdArithmeticLane exactFiniteTheorem
  finiteCrossPollinationBridge arithmeticBoundary

complexityStatus : FrontierLaneStatus
complexityStatus = frontierLaneStatus
  complexityLane proofBearingGenericTheorem
  finiteCrossPollinationBridge openProblemClosure

gradedVertexStatus : FrontierLaneStatus
gradedVertexStatus = frontierLaneStatus
  gradedVertexLane exactFiniteTheorem
  finiteCrossPollinationBridge analyticBoundary

spectralStatus : FrontierLaneStatus
spectralStatus = frontierLaneStatus
  spectralCertificationLane proofBearingGenericTheorem
  finiteCrossPollinationBridge analyticBoundary

yangMillsStatus : FrontierLaneStatus
yangMillsStatus = frontierLaneStatus
  yangMillsLane exactFiniteTheorem
  finiteCrossPollinationBridge continuumBoundary

navierStokesStatus : FrontierLaneStatus
navierStokesStatus = frontierLaneStatus
  navierStokesLane proofBearingGenericTheorem
  finiteCrossPollinationBridge openProblemClosure

allLocalCoresAreNowSubstantive :
  localCore cochainHodgeStatus ≡ proofBearingGenericTheorem
  × localCore automorphicStatus ≡ proofBearingGenericTheorem
  × localCore bsdStatus ≡ exactFiniteTheorem
  × localCore complexityStatus ≡ proofBearingGenericTheorem
  × localCore gradedVertexStatus ≡ exactFiniteTheorem
  × localCore spectralStatus ≡ proofBearingGenericTheorem
  × localCore yangMillsStatus ≡ exactFiniteTheorem
  × localCore navierStokesStatus ≡ proofBearingGenericTheorem
allLocalCoresAreNowSubstantive =
  refl , refl , refl , refl , refl , refl , refl , refl

openProblemLanesRemainOpen :
  globalClosure complexityStatus ≡ openProblemClosure
  × globalClosure navierStokesStatus ≡ openProblemClosure
openProblemLanesRemainOpen = refl , refl

yangMillsContinuumClosureRemainsBoundary :
  globalClosure yangMillsStatus ≡ continuumBoundary
yangMillsContinuumClosureRemainsBoundary = refl

data ImplementedFrontierEdge : Set where
  cochainToHodgeEnergy
  hodgeToGaugeInvariantCurvature
  hodgeToFiniteCoercivity
  localFrobeniusToEulerProduct
  modularCoefficientToEulerAgreement
  modularSubstitutionToFunctionalEquation
  deterministicPToUnitCertificateNP
  nondeterministicRunToPathCertificate
  finiteRunToCookLevinTableau
  differentialAlgebraToVertexFields
  fockBasisToEulerCharacterPrefix
  selfAdjointMatrixToCriticalLineCandidate
  vorticityCoherenceToFiniteDepletion

data MissingFrontierEdge : Set where
  analyticHodgeDecomposition
  infiniteEulerProductConvergence
  ellipticModularityTheorem
  mellinIntegralRealization
  generalCookLevinPolynomialBound
  heisenbergVOACompletion
  hilbertPolyaCompleteness
  nonabelianWeightedCoercivity
  os2os4kpUniformity
  continuumYangMillsGap
  continuumBiotSavartDepletion
  navierStokesGlobalRegularity

finiteStageIsNotContinuumStage :
  exactFiniteTheorem ≡ continuumBoundary → ⊥
finiteStageIsNotContinuumStage ()
