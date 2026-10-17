module DASHI.Biology.IITParityGluingTerminalMaxCut20261017Exact where

------------------------------------------------------------------------
-- TERMINAL LOCAL MAX-CUT, 2026-10-17
--
-- This owner supersedes stale frontier flags in earlier rolling capstones.  It
-- records only payments actually available on the current branch and keeps the
-- three remaining blockers explicitly external:
--
--   * direct package-level PyPhi replay of the calibrated +ABC result;
--   * actual LILA hidden trajectories/checkpoints;
--   * a fresh Agda kernel run in an environment with Agda installed.
--
-- It does not turn numerical receipts into Agda theorems.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IITParityGluingConjectureMaxCutExact as Prior
import DASHI.Biology.IITFaceAwarePyPhiGoldenCalibrationExact as Golden
import DASHI.Biology.IITCubeJordanChainCentralizerTargetExact as Jordan
import DASHI.Biology.IITCubeJordanBasisMatrixExact as JordanBasis
import DASHI.Biology.IITCubeConcreteJordanConjugacyExact as Conjugacy
import DASHI.Biology.IITCubeConcreteNMatrixRecognitionExact as Recognition
import DASHI.Biology.IITCubeJordanCentralizerAlgebraExact as Centralizer
import DASHI.Biology.IITCubeFirstTitsSL3TranslationIntersectionExact as SL3
import DASHI.Biology.IITCubePermutationStabilizer18Exact as Perm18
import DASHI.Biology.IITCubeDiagonalStabilizerExact as Stabilizer

------------------------------------------------------------------------
-- 1. Concrete proof-relevant centralizer witnesses.
------------------------------------------------------------------------

concreteJordanChainA : Jordan.ConcreteJordanChain3
concreteJordanChainA = Jordan.chainA

concreteJordanChainB : Jordan.ConcreteJordanChain3
concreteJordanChainB = Jordan.chainB

concreteJordanChainC : Jordan.ConcreteJordanChain3
concreteJordanChainC = Jordan.chainC

concreteJordanBasisMatrix : JordanBasis.ConcreteJordanBasisMatrixWitness
concreteJordanBasisMatrix = JordanBasis.canonicalConcreteJordanBasisMatrixWitness

concreteNMatrixRecognition : Recognition.ConcreteNMatrixRecognition
concreteNMatrixRecognition = Recognition.canonicalConcreteNMatrixRecognition

concreteJordanConjugacy : Conjugacy.ConcreteJordanConjugacyWitness
concreteJordanConjugacy = Conjugacy.canonicalConcreteJordanConjugacyWitness

jordanCentralizerPolynomialEquivalence :
  Centralizer.JordanCentralizerPolynomialEquivalence
jordanCentralizerPolynomialEquivalence =
  Centralizer.canonicalJordanCentralizerPolynomialEquivalence

------------------------------------------------------------------------
-- 2. Residual finite SL3 same-action intersection.
------------------------------------------------------------------------

cubeFirstTitsSL3TranslationIntersection :
  SL3.CubeFirstTitsSL3TranslationIntersection
cubeFirstTitsSL3TranslationIntersection =
  SL3.canonicalCubeFirstTitsSL3TranslationIntersection

permutationSpinePreservesGraph :
  (g : Perm18.Permutation18) →
  Stabilizer.PreservesGraph (Perm18.permutationEndo g)
permutationSpinePreservesGraph = Perm18.permutationPreservesGraph

------------------------------------------------------------------------
-- 3. PyPhi golden same-TPM authority boundary.
------------------------------------------------------------------------

golden2023 : Golden.PyPhiXORGoldenSourceReceipt
golden2023 = Golden.canonicalPyPhiXOR2023GoldenSourceReceipt

golden2026 : Golden.PyPhiXORGoldenSourceReceipt
golden2026 = Golden.canonicalPyPhiXOR2026GoldenSourceReceipt

------------------------------------------------------------------------
-- 4. Final local/external ledger.
------------------------------------------------------------------------

record TerminalLocalMaxCutStatus : Set where
  constructor terminal-local-max-cut-status
  field
    xorGridAsTwoInputOneOutputFabricSourceWritten : Bool
    finiteGridTorqueC3WholePathIntertwinerSourceWritten : Bool
    matchedBinaryFabricPlusABCSourceWritten : Bool
    pairwiseControlSameTPMAsPyPhiGoldenKernelWitnessWritten : Bool
    pyPhi2023GoldenCalibrationReceiptPresent : Bool
    pyPhi2026SystemPhiVsCESSeparationReceiptPresent : Bool
    goldenCalibratedMatchedFullCESReceiptPresent : Bool
    fullCESResolvesScalarCollisionAt110Numerically : Bool

    concreteJordanChainsSourceWritten : Bool
    concreteJordanBasisHasExplicitTwoSidedInverseSourceWritten : Bool
    concreteNMatrixRecognizedAsActualBPlusIOnBasisSourceWritten : Bool
    concreteNConjugatesToThreeJordanBlocksSourceWritten : Bool
    jordanCentralizerIffToeplitzShapeSourceWritten : Bool
    jordanCentralizerPolynomialExtractionExpansionSourceWritten : Bool
    truncatedPolynomialT3ZeroSourceWritten : Bool

    permutation18GraphStabilizerSourceWritten : Bool
    permutation18FaithfulnessAndSemidirectLawNumericallyPaid : Bool
    residualCubeTranslationsSameCoordinateCyclesAsFirstTitsSourceWritten : Bool
    residualCubeTranslationsDeterminantOneSL3ActionNumericallyPaid : Bool

    directPyPhiPackageReplayPresent : Bool
    actualLilaHiddenTrajectoryPresent : Bool
    freshAgdaKernelReceiptForNewestOwnersPresent : Bool
open TerminalLocalMaxCutStatus public

canonicalTerminalLocalMaxCutStatus : TerminalLocalMaxCutStatus
canonicalTerminalLocalMaxCutStatus =
  terminal-local-max-cut-status
    true true true true true true true true
    true true true true true true true
    true true true true
    false false false

record TerminalExternalFrontier : Set where
  constructor terminal-external-frontier
  field
    needsMoreBooleanTruthTableEnumeration : Bool
    needsAnotherBinaryVsTriadicFixture : Bool
    needsMoreCubeRankOrCardinalityCounting : Bool
    needsMoreFiniteC3PhaseRecharting : Bool
    needsAnotherLocalCentralizerDimensionScan : Bool
    needsAnotherResidualFiniteSL3TranslationTest : Bool

    directPyPhiReplayWouldProvideIndependentVerification : Bool
    lilaRequiresActualExternalModelData : Bool
    agdaKernelVerificationRequiresAgdaEnvironment : Bool
open TerminalExternalFrontier public

canonicalTerminalExternalFrontier : TerminalExternalFrontier
canonicalTerminalExternalFrontier =
  terminal-external-frontier
    false false false false false false
    true true true

------------------------------------------------------------------------
-- Interpretation firewall.
------------------------------------------------------------------------

record TerminalInterpretationBoundary : Set where
  constructor terminal-interpretation-boundary
  field
    sameFiniteC3PhaseMeansSameTorqueAmplitude : Bool
    residualSL3CoordinateActionMeansFullE6InvariantDynamics : Bool
    calibratedFiniteCESResultIsDirectPyPhiPackageOutput : Bool
    absentLilaDataCanBeReplacedBySyntheticTrajectory : Bool
open TerminalInterpretationBoundary public

canonicalTerminalInterpretationBoundary : TerminalInterpretationBoundary
canonicalTerminalInterpretationBoundary =
  terminal-interpretation-boundary false false false false
