module DASHI.ComputerScience.RSA260ShorColouring369MonsterSymmetrySearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Crypto.ShorFactoring as Shor
import DASHI.Algebra.Quantum.GeneralShor as GeneralShor
import DASHI.ComputerScience.RSA260ProductionSubstitutionRoadmapExact as Production
import DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact as Pants369
import DASHI.Moonshine.Monster369NDimParetoTetrationBridgeExact as MonsterNDim
import DASHI.Moonshine.Monster369DiscriminatorSymmetryBoundaryExact as MonsterSymmetry
import DASHI.Moonshine.Base369Ternary27PathCubeSpectralBandsExact as PathCube
import DASHI.Foundations.Moonshine196883Boundary as M196883

------------------------------------------------------------------------
-- SHOR / COLOURING / 369 / MONSTER SYMMETRY SEARCH BOUNDARY
--
-- Reusable principle:
--
--   find an exact action/symmetry
--   -> prove the target consumer is invariant/covariant
--   -> quotient / Fourier-transform / orbit-compress
--   -> solve on the reduced carrier
--   -> reconstruct and verify on the original carrier.
--
-- Dimension by itself is never the reduction theorem.  The reduction is paid
-- only by an action and an invariant consumer.
------------------------------------------------------------------------

record SymmetrySearchPrinciple : Set where
  constructor symmetry-search-principle
  field
    actionSpecified : Bool
    targetConsumerInvariant : Bool
    quotientOrTransformSpecified : Bool
    reducedCarrierSpecified : Bool
    liftOrReconstructionSpecified : Bool
    dimensionIncreaseAloneCountsAsReduction : Bool
open SymmetrySearchPrinciple public

canonicalSymmetrySearchPrinciple : SymmetrySearchPrinciple
canonicalSymmetrySearchPrinciple =
  symmetry-search-principle false false false false false false

------------------------------------------------------------------------
-- Six cube faces = three opposite-face axes x two polarities.
-- This is a chosen six-state coordinate carrier.  It is not yet a proof that
-- the cube-face adjacency graph and the 369 wheel adjacency are isomorphic.
------------------------------------------------------------------------

data Axis3 : Set where axisX axisY axisZ : Axis3
data Polarity2 : Set where minusFace plusFace : Polarity2

record CubeFace6 : Set where
  constructor cubeFace
  field
    axis : Axis3
    polarity : Polarity2
open CubeFace6 public

oppositeFace : CubeFace6 → CubeFace6
oppositeFace (cubeFace a minusFace) = cubeFace a plusFace
oppositeFace (cubeFace a plusFace) = cubeFace a minusFace

oppositeFaceInvolutive : (f : CubeFace6) → oppositeFace (oppositeFace f) ≡ f
oppositeFaceInvolutive (cubeFace axisX minusFace) = refl
oppositeFaceInvolutive (cubeFace axisX plusFace) = refl
oppositeFaceInvolutive (cubeFace axisY minusFace) = refl
oppositeFaceInvolutive (cubeFace axisY plusFace) = refl
oppositeFaceInvolutive (cubeFace axisZ minusFace) = refl
oppositeFaceInvolutive (cubeFace axisZ plusFace) = refl

record CubeFace369Boundary : Set where
  constructor cube-face-369-boundary
  field
    cubeHasThreeOppositeFaceAxes : Bool
    eachAxisHasTwoPolarities : Bool
    sixStateCarrierShapeIsThreeTimesTwo : Bool
    existing369StrictWheelHasSixStates : Bool
    existing369SixEmbedsInNine : Bool
    cubeFaceAdjacencyProvedSameAs369Adjacency : Bool
    cubeSymmetryActionProvedToPreserveRSAConsumer : Bool
open CubeFace369Boundary public

canonicalCubeFace369Boundary : CubeFace369Boundary
canonicalCubeFace369Boundary = cube-face-369-boundary
  true true true
  true
  (Pants369.ColourWheelNinePantsBoundary.colourWheelSixEmbedsInNineSheet
    Pants369.canonicalColourWheelNinePantsBoundary)
  false false

------------------------------------------------------------------------
-- The 2026 near-linear Four-Color result is retained as an external theorem
-- coordinate rather than imported from the sibling PR.  The relevant "six"
-- is a larger D-reducible 6-regular configuration, not a universal six-vertex
-- graph.  The complexity gain comes from Omega(n) compatible local reductions
-- giving constant-factor shrinkage per recursive round.
------------------------------------------------------------------------

record NearLinearColouringReductionReceipt : Set where
  constructor near-linear-colouring-reduction-receipt
  field
    sourceReference : String
    largerDReducibleSixRegularConfigurationReported : Bool
    sixMeansSixRegularNotSixVertexUniversalReducer : Bool
    linearlyManyPairwiseCompatibleReductionsReported : Bool
    constantFactorProblemShrinkReported : Bool
    nearLinearRuntimeReported : Bool
    cubeSixFaceCarrierIdentifiedWithSixRegularConfiguration : Bool
open NearLinearColouringReductionReceipt public

nearLinearColouringReduction : NearLinearColouringReductionReceipt
nearLinearColouringReduction = near-linear-colouring-reduction-receipt
  "Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, The Four Color Theorem with Linearly Many Reducible Configurations and Near-Linear Time Coloring, arXiv:2603.24880v2, 2026"
  true true true true true false

------------------------------------------------------------------------
-- Existing Shor content already pays the *shape* of a genuine symmetry-based
-- reduction: modular exponentiation is presented as an exact hidden-period
-- problem and the machine surface carries a finite Fourier transform.  This is
-- not an RSA-260 quantum execution receipt.
------------------------------------------------------------------------

record ShorSymmetryBoundary : Set where
  constructor shor-symmetry-boundary
  field
    finiteAbelianHSPGeneralSurfaceExists : Bool
    modularOrderPresentedAsHiddenPeriod : Bool
    FourierTransformPresentInPeriodMachine : Bool
    exactRecoveredPeriodCanFeedCertifiedClassicalSplit : Bool
    rsa260QuantumOrderFindingRunConstructed : Bool
    rsa260QuantumResourceEstimateCertified : Bool
open ShorSymmetryBoundary public

canonicalShorSymmetryBoundary : ShorSymmetryBoundary
canonicalShorSymmetryBoundary = shor-symmetry-boundary
  true true true true false false

------------------------------------------------------------------------
-- 19683 / 196883 / 196884 ledgers.
--
-- 19683 is the current 3^9 Base369 profile carrier.
-- 196883 = 10*19683 + 53 and 196884 = 196883 + 1 are exact arithmetic only.
-- No Monster action on RSA or graph-colouring states is manufactured from it.
------------------------------------------------------------------------

base369Profiles : Nat
base369Profiles = 19683

monsterNeighbour : Nat
monsterNeighbour = M196883.moonshineLargeFactor

base369TenPlusResidual : 10 * base369Profiles + 53 ≡ monsterNeighbour
base369TenPlusResidual = refl

record MonsterScaleSymmetryBoundary : Set where
  constructor monster-scale-symmetry-boundary
  field
    base369ProfileCountIs19683 : Bool
    arithmetic196883AsTenBlocksPlus53Checked : Bool
    arithmetic196884As196883PlusOneChecked : Bool
    signed369CarrierSymmetryExists : Bool
    validSemanticSymmetryMaySupportOrbitCompression : Bool
    monsterRepresentationActionOnRSAStatesPaid : Bool
    monsterRepresentationActionOnColouringStatesPaid : Bool
    arithmeticDecompositionImpliesRepresentationDecomposition : Bool
open MonsterScaleSymmetryBoundary public

canonicalMonsterScaleSymmetryBoundary : MonsterScaleSymmetryBoundary
canonicalMonsterScaleSymmetryBoundary = monster-scale-symmetry-boundary
  true true true
  (MonsterSymmetry.Monster369DiscriminatorSymmetryBoundary.signedVoxelReflectionIsExactCarrierSymmetry
    MonsterSymmetry.canonicalMonster369DiscriminatorSymmetryBoundary)
  (MonsterNDim.Monster369NDimParetoTetrationBoundary.validSemanticParetoAutomorphismMaySupportOrbitCompression
    MonsterNDim.canonicalMonster369NDimParetoTetrationBoundary)
  false false false

------------------------------------------------------------------------
-- Higher-dimensional research route.
------------------------------------------------------------------------

data HigherDimensionalCandidateRoute : Set where
  colouringSurfaceLift : HigherDimensionalCandidateRoute
  rsaBlockTensorLift : HigherDimensionalCandidateRoute
  shorFourierCharacterLift : HigherDimensionalCandidateRoute
  monsterOrbitQuotientLift : HigherDimensionalCandidateRoute
  recursive369NDimLift : HigherDimensionalCandidateRoute

record HigherDimensionalSearchBoundary : Set where
  constructor higher-dimensional-search-boundary
  field
    higherDimensionMayExposeProductStructure : Bool
    higherDimensionMayExposeGroupAction : Bool
    symmetryQualifiedOrbitCompressionMayReduceSearch : Bool
    higherDimensionAutomaticallyImprovesGraphColouring : Bool
    higherDimensionAutomaticallyImprovesClassicalRSAFactoring : Bool
    monsterScaleAutomaticallyImprovesRSA : Bool
    shorShowsARealSymmetryBasedFactoringReductionFamily : Bool
    fourColourResultSuggestsFixedSurfaceExtensions : Bool
open HigherDimensionalSearchBoundary public

canonicalHigherDimensionalSearchBoundary : HigherDimensionalSearchBoundary
canonicalHigherDimensionalSearchBoundary = higher-dimensional-search-boundary
  true true true
  false false false
  true true

------------------------------------------------------------------------
-- RSA roadmap insertion point.
--
-- Production bytes remain first conclusion-paying acquisition residual.
-- Symmetry analysis may run in parallel as a candidate compressor, but it may
-- not discharge same-object acquisition or production replay.
------------------------------------------------------------------------

productionBoundary : Production.RSA260ProductionSubstitutionBoundary
productionBoundary = Production.currentRSA260ProductionSubstitutionBoundary

record RSA260SymmetryResearchRoadmapBoundary : Set where
  constructor rsa260-symmetry-research-roadmap-boundary
  field
    syntheticLinearAlgebraPathComplete : Bool
    productionBytesStillFirstConclusionPayingResidual : Bool
    shorHSPProvidesExactSymmetryReductionTemplate : Bool
    colouringManyLocalReductionsProvideCompatibilityTemplate : Bool
    cubeSixFaceThreeByTwoCarrierAvailable : Bool
    base369SignedSymmetryCandidateGenerationAvailable : Bool
    monsterNDimOrbitCompressionRequiresConsumerInvariant : Bool
    higherDimensionalSymmetrySearchWorthRunningInParallel : Bool
    higherDimensionalSearchAlreadyImprovesGNFSAsymptotics : Bool
open RSA260SymmetryResearchRoadmapBoundary public

currentRSA260SymmetryResearchRoadmapBoundary : RSA260SymmetryResearchRoadmapBoundary
currentRSA260SymmetryResearchRoadmapBoundary = rsa260-symmetry-research-roadmap-boundary
  true true true true true true true true false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SixFacesImpliesSixRegularReducer : Set where
data HigherDimensionImpliesLowerComplexity : Set where
data MonsterArithmeticImpliesRSAAction : Set where
data CarrierSymmetryImpliesConsumerSymmetry : Set where
data ShorHSPImpliesClassicalGNFSAcceleration : Set where
data ColouringReducerImpliesRSAReducer : Set where

sixFacesDoNotCreateColouringReducer : SixFacesImpliesSixRegularReducer → ⊥
sixFacesDoNotCreateColouringReducer ()

higherDimensionDoesNotCreateLowerComplexity : HigherDimensionImpliesLowerComplexity → ⊥
higherDimensionDoesNotCreateLowerComplexity ()

monsterArithmeticDoesNotCreateRSAAction : MonsterArithmeticImpliesRSAAction → ⊥
monsterArithmeticDoesNotCreateRSAAction ()

carrierSymmetryDoesNotCreateConsumerSymmetry : CarrierSymmetryImpliesConsumerSymmetry → ⊥
carrierSymmetryDoesNotCreateConsumerSymmetry ()

shorHSPDoesNotCreateGNFSAcceleration : ShorHSPImpliesClassicalGNFSAcceleration → ⊥
shorHSPDoesNotCreateGNFSAcceleration ()

colouringReducerDoesNotCreateRSAReducer : ColouringReducerImpliesRSAReducer → ⊥
colouringReducerDoesNotCreateRSAReducer ()

------------------------------------------------------------------------
-- Existing 27 path-cube warning retained: C3^3 character labels are not by
-- themselves adjacency eigenvectors for the non-periodic P3 x P3 x P3 grid.
------------------------------------------------------------------------

pathCubeCharactersDoNotAutomaticallyDiagonaliseAdjacency : Bool
pathCubeCharactersDoNotAutomaticallyDiagonaliseAdjacency =
  not (PathCube.PeriodicVsPathCubeSpectralBoundary.c3CubedCharactersAutomaticallyDiagonalisePathCubeAdjacency
    PathCube.canonicalPeriodicVsPathCubeSpectralBoundary)
