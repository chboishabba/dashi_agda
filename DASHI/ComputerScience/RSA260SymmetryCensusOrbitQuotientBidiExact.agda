module DASHI.ComputerScience.RSA260SymmetryCensusOrbitQuotientBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260ShorColouring369MonsterSymmetrySearchExact as Search
import DASHI.ComputerScience.RSA260Monster3BPhaseSymmetryQuotientResearchExact as MonsterModel

------------------------------------------------------------------------
-- EXECUTED SYMMETRY CENSUS + BIDIRECTIONAL ORBIT-QUOTIENT BENCHMARK
--
-- Two deliberately different synthetic carriers are retained:
--
--  (A) the SAME generic 256x256 GF(2) matrix used by the Krylov/kernel lane;
--      a census over S4 block permutations x C64 common shifts finds only the
--      identity commuting action in that candidate family;
--
--  (B) a declared C2 pair-swap-equivariant 256-coordinate benchmark, with 128
--      two-element coordinate orbits.  Its invariant carrier quotients exactly
--      to 128 coordinates and lifts back losslessly.
--
-- Together these pay both directions of the research rule:
--
--   generic carrier -> test symmetry -> fail closed when absent
--   qualified symmetry -> quotient -> solve/check -> lift -> verify upstairs.
------------------------------------------------------------------------

record SymmetryCensusExecutionReceipt : Set where
  constructor symmetry-census-execution-receipt
  field
    sourceRepository : String
    sourcePath : String
    sourceBlob : String
    sourceEquivalentExecutionPassed : Bool
    exactGitBlobExecuted : Bool
    compiler : String
    candidateBlockPermutations : Nat
    candidateCommonShifts : Nat
    candidateActions : Nat
    commutingActions : Nat
    nontrivialCommutingActions : Nat
    identityObserved : Bool
    censusFamilyExhausted : Bool
    absenceBeyondCensusFamilyProved : Bool
open SymmetryCensusExecutionReceipt public

rsa260SyntheticSymmetryCensusReceipt : SymmetryCensusExecutionReceipt
rsa260SyntheticSymmetryCensusReceipt = symmetry-census-execution-receipt
  "chboishabba/dashiRTX"
  "rsa260_symmetry_census_256_oracle.c"
  "6ebf7fc28b011ab9bbeae5418ed45fdb9a3a4126"
  true false
  "GCC 14.2.0; -std=c11 -O3 -Wall -Wextra -pedantic"
  24 64 1536 1 0 true true false

record PairOrbitQuotientExecutionReceipt : Set where
  constructor pair-orbit-quotient-execution-receipt
  field
    sourceRepository : String
    sourcePath : String
    sourceBlob : String
    sourceEquivalentExecutionPassed : Bool
    exactGitBlobExecuted : Bool
    compiler : String
    fullWidth : Nat
    quotientWidth : Nat
    orbitCount : Nat
    orbitSize : Nat
    commuteBasisChecks : Nat
    bidiIntertwiningChecks : Nat
    quotientRank : Nat
    quotientNullity : Nat
    liftedKernelWeight : Nat
    reductionFactor : Nat
    actionCommutesWithOperator : Bool
    projectAfterLiftIsIdentity : Bool
    liftAfterProjectOnInvariantCarrierIsIdentity : Bool
    quotientOperatorIntertwinesWithLift : Bool
    nonzeroQuotientKernelRecovered : Bool
    liftedKernelVerifiedUpstairs : Bool
    productionRSA260MatrixUsed : Bool
open PairOrbitQuotientExecutionReceipt public

rsa260PairOrbitBidiReceipt : PairOrbitQuotientExecutionReceipt
rsa260PairOrbitBidiReceipt = pair-orbit-quotient-execution-receipt
  "chboishabba/dashiRTX"
  "rsa260_pair_orbit_quotient_bidi_256_oracle.c"
  "dbc52b8c4813e3dbe61a08711f0001222d81c024"
  true false
  "GCC 14.2.0; -std=c11 -O3 -Wall -Wextra -pedantic"
  256 128 128 2
  256 262272
  127 1 256 2
  true true true true true true false

------------------------------------------------------------------------
-- Characteristic-sensitive symmetry boundary.
--
-- The cube/opposite-face C2 carrier is useful here only as an orbit action.
-- Over GF(2), +1 = -1, so importing a +/- eigenspace split from characteristic
-- not-two would be the wrong algebra.  The safe transport is orbit/equitable
-- partition quotienting plus an explicit lift/intertwiner.
------------------------------------------------------------------------

record CharacteristicTwoSymmetryBoundary : Set where
  constructor characteristic-two-symmetry-boundary
  field
    pairSwapActionHasOrderTwo : Bool
    plusAndMinusScalarsDistinctInGF2 : Bool
    spectralPlusMinusSplitImported : Bool
    orbitPartitionQuotientUsed : Bool
    explicitLiftUsed : Bool
open CharacteristicTwoSymmetryBoundary public

canonicalCharacteristicTwoSymmetryBoundary : CharacteristicTwoSymmetryBoundary
canonicalCharacteristicTwoSymmetryBoundary =
  characteristic-two-symmetry-boundary true false false true true

------------------------------------------------------------------------
-- Bidirectional x-pollination ledger.
------------------------------------------------------------------------

record BidiCrossPollinationBoundary : Set where
  constructor bidi-cross-pollination-boundary
  field
    shorContributesSymmetryQuotientTemplate : Bool
    colouringContributesCompatibleLocalReductionTemplate : Bool
    pantsContributesSeamAndLiftDiscipline : Bool
    cubeSixContributesOppositePairOrbitCarrier : Bool
    monster3BContributesActualPhaseDecompositionModel : Bool
    rsaContributesExecutableCommutationAndLiftTest : Bool
    rsaResultAutomaticallyProvesColouringSpeedup : Bool
    rsaResultAutomaticallyProvesMonsterAction : Bool
    symmetryAbsentInOneFamilyMeansNoSymmetryExists : Bool
open BidiCrossPollinationBoundary public

canonicalBidiCrossPollinationBoundary : BidiCrossPollinationBoundary
canonicalBidiCrossPollinationBoundary = bidi-cross-pollination-boundary
  true true true true true true false false false

searchBoundary : Search.RSA260SymmetryResearchRoadmapBoundary
searchBoundary = Search.currentRSA260SymmetryResearchRoadmapBoundary

monsterCandidateBoundary : MonsterModel.Monster3BRSAQuotientCandidateBoundary
monsterCandidateBoundary = MonsterModel.canonicalMonster3BRSAQuotientCandidateBoundary

------------------------------------------------------------------------
-- Roadmap consequence.
------------------------------------------------------------------------

record RSA260SymmetryExecutionRoadmapBoundary : Set where
  constructor rsa260-symmetry-execution-roadmap-boundary
  field
    genericMatrixCandidateCensusExecuted : Bool
    genericMatrixNontrivialActionFoundInTestedFamily : Bool
    declaredEquivariantBenchmarkExecuted : Bool
    orbitQuotientHalvesCarrier : Bool
    quotientKernelLiftsToFullKernel : Bool
    measuredStructuralReductionPaid : Bool
    productionMatrixSymmetryCensusPaid : Bool
    productionOperatorQuotientPaid : Bool
    productionBytesStillRequired : Bool
open RSA260SymmetryExecutionRoadmapBoundary public

currentRSA260SymmetryExecutionRoadmapBoundary : RSA260SymmetryExecutionRoadmapBoundary
currentRSA260SymmetryExecutionRoadmapBoundary =
  rsa260-symmetry-execution-roadmap-boundary
    true false true true true true false false true

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data CensusMissImpliesNoAutomorphism : Set where
data ToySpeedupImpliesProductionSpeedup : Set where
data C2OrbitImpliesC3Eigenspace : Set where
data QuotientKernelImpliesWholeKernelCaptured : Set where
data ReductionFactorImpliesAsymptoticImprovement : Set where

censusMissDoesNotProveNoAutomorphism : CensusMissImpliesNoAutomorphism → ⊥
censusMissDoesNotProveNoAutomorphism ()

toySpeedupDoesNotProveProductionSpeedup : ToySpeedupImpliesProductionSpeedup → ⊥
toySpeedupDoesNotProveProductionSpeedup ()

c2OrbitDoesNotCreateC3Eigenspace : C2OrbitImpliesC3Eigenspace → ⊥
c2OrbitDoesNotCreateC3Eigenspace ()

oneQuotientKernelDoesNotCaptureWholeKernel : QuotientKernelImpliesWholeKernelCaptured → ⊥
oneQuotientKernelDoesNotCaptureWholeKernel ()

constantReductionDoesNotCreateAsymptoticImprovement : ReductionFactorImpliesAsymptoticImprovement → ⊥
constantReductionDoesNotCreateAsymptoticImprovement ()
