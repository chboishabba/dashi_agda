module DASHI.ComputerScience.RSA260BidiSparseRawRankStressFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.ComputerScience.RSA260BidiSparseRawRankObserverFrontierExact as Previous

------------------------------------------------------------------------
-- STRESSED SPARSE RAW-RANK FRONTIER
--
-- Add eight fresh projection-seed worlds to the prior 18-world carrier.
-- The previous sparse receipt observer (degree,r2,r4,r10) now collides:
-- seed7, seed8, seed11 and seed14 share (16,7,6,7) while their generator
-- digests differ. Re-run coordinate-subset search over the resulting 26 worlds.
-- No degree + <=3 rank-coordinate subset separates all receipts in the runtime
-- search. Four coordinates are the first found sparse size; choose the
-- all-high-rank/raw-mode set (r4,r5,r7,r9).
--
-- The selected 26-world factorisation is formal below. Exhaustive subset
-- minimality remains runtime evidence rather than an Agda theorem.
------------------------------------------------------------------------

record SparseStressRuntimeReceipt : Set where
  constructor sparse-stress-runtime-receipt
  field
    stressScriptPath : String
    stressScriptSHA256 : String
    stressOutputPath : String
    stressOutputSHA256 : String
    frontierScriptPath : String
    frontierScriptSHA256 : String
    frontierOutputPath : String
    frontierOutputSHA256 : String
    combinedWorlds : Nat
    seedWorlds : Nat
    discoveryWorlds : Nat
    selectedRank0 selectedRank1 selectedRank2 selectedRank3 : Nat
    minimumRankCoordinateCountFoundWithDegree : Nat
    runtimeSubsetSearchExact : Bool
    runtimeCommittedToProducerRepository : Bool
open SparseStressRuntimeReceipt public

currentSparseStressRuntimeReceipt : SparseStressRuntimeReceipt
currentSparseStressRuntimeReceipt =
  sparse-stress-runtime-receipt
    "/mnt/data/rsa260_bidi_sparse_raw_rank_stress.py"
    "a0539bf031fd142947eaace4116d5509b65406244951f805211d3b3d07ad37d3"
    "/mnt/data/rsa260_bidi_sparse_raw_rank_stress.json"
    "b45c33065f6889a2dc6c79bab7df0f8900e805bf2bf9b52c3e888ad60e077f5b"
    "/mnt/data/rsa260_bidi_sparse_raw_rank_stress_frontier.py"
    "42b0f8009d20d6bcdeedf495b2aa53bc2b6b499d93bbb62ca6893241c1afb483"
    "/mnt/data/rsa260_bidi_sparse_raw_rank_stress_frontier.json"
    "7d09b2e2defa2358527715bb0a487169777b770b2032828949e9a79c404a8d77"
    26 16 10 4 5 7 9 4 true false

data StressWorld : Set where
  seed0 seed1 seed2 seed3 seed4 seed5 seed6 seed7 : StressWorld
  seed8 seed9 seed10 seed11 seed12 seed13 seed14 seed15 : StressWorld
  identity rotate1 rotate2 rotate3 affine3 affine5 affine7 affine9 xor1 bitrev9 : StressWorld

data ReceiptQuery : Set where receiptIdentity : ReceiptQuery

data ReceiptAnswer : Set where
  seed0Receipt seed1Receipt seed2Receipt seed3Receipt : ReceiptAnswer
  seed4Receipt seed5Receipt seed6Receipt seed7Receipt : ReceiptAnswer
  seed8Receipt seed9Receipt seed10Receipt seed11Receipt : ReceiptAnswer
  seed12Receipt seed13Receipt seed14Receipt seed15Receipt : ReceiptAnswer
  identityReceipt rotate1Receipt rotate2Receipt rotate3Receipt : ReceiptAnswer
  affine3Receipt affine5Receipt affine7Receipt affine9Receipt : ReceiptAnswer
  xor1Receipt bitrev9Receipt : ReceiptAnswer

receiptAnswer : ReceiptQuery → StressWorld → ReceiptAnswer
receiptAnswer receiptIdentity seed0 = seed0Receipt
receiptAnswer receiptIdentity seed1 = seed1Receipt
receiptAnswer receiptIdentity seed2 = seed2Receipt
receiptAnswer receiptIdentity seed3 = seed3Receipt
receiptAnswer receiptIdentity seed4 = seed4Receipt
receiptAnswer receiptIdentity seed5 = seed5Receipt
receiptAnswer receiptIdentity seed6 = seed6Receipt
receiptAnswer receiptIdentity seed7 = seed7Receipt
receiptAnswer receiptIdentity seed8 = seed8Receipt
receiptAnswer receiptIdentity seed9 = seed9Receipt
receiptAnswer receiptIdentity seed10 = seed10Receipt
receiptAnswer receiptIdentity seed11 = seed11Receipt
receiptAnswer receiptIdentity seed12 = seed12Receipt
receiptAnswer receiptIdentity seed13 = seed13Receipt
receiptAnswer receiptIdentity seed14 = seed14Receipt
receiptAnswer receiptIdentity seed15 = seed15Receipt
receiptAnswer receiptIdentity identity = identityReceipt
receiptAnswer receiptIdentity rotate1 = rotate1Receipt
receiptAnswer receiptIdentity rotate2 = rotate2Receipt
receiptAnswer receiptIdentity rotate3 = rotate3Receipt
receiptAnswer receiptIdentity affine3 = affine3Receipt
receiptAnswer receiptIdentity affine5 = affine5Receipt
receiptAnswer receiptIdentity affine7 = affine7Receipt
receiptAnswer receiptIdentity affine9 = affine9Receipt
receiptAnswer receiptIdentity xor1 = xor1Receipt
receiptAnswer receiptIdentity bitrev9 = bitrev9Receipt

receiptSemantics : Query.QuerySemantics StressWorld ReceiptQuery ReceiptAnswer
receiptSemantics = Query.querySemantics receiptAnswer

------------------------------------------------------------------------
-- Previous sparse observer fails under stress.
------------------------------------------------------------------------

data PreviousSparseKey : Set where
  p16-8-7-7 p17-6-7-7 p17-7-7-6 p16-8-7-8 : PreviousSparseKey
  p16-6-8-8 p17-6-7-6 p17-7-8-7 p16-7-6-7 : PreviousSparseKey
  p17-6-8-7 p16-7-8-7 p17-6-6-8 p16-7-8-6 : PreviousSparseKey
  p17-7-5-7 p17-8-7-7 p17-3-7-7 p16-6-7-6 : PreviousSparseKey
  p17-7-6-8 p16-7-8-8 p17-7-7-8 p17-5-8-7 : PreviousSparseKey
  p16-7-7-7 p17-6-8-8 p16-7-7-6 : PreviousSparseKey

previousSparseObserve : StressWorld → PreviousSparseKey
previousSparseObserve seed0 = p16-8-7-7
previousSparseObserve seed1 = p17-6-7-7
previousSparseObserve seed2 = p17-7-7-6
previousSparseObserve seed3 = p16-8-7-8
previousSparseObserve seed4 = p16-6-8-8
previousSparseObserve seed5 = p17-6-7-6
previousSparseObserve seed6 = p17-7-8-7
previousSparseObserve seed7 = p16-7-6-7
previousSparseObserve seed8 = p16-7-6-7
previousSparseObserve seed9 = p17-6-8-7
previousSparseObserve seed10 = p16-7-8-7
previousSparseObserve seed11 = p16-7-6-7
previousSparseObserve seed12 = p17-6-6-8
previousSparseObserve seed13 = p16-7-8-6
previousSparseObserve seed14 = p16-7-6-7
previousSparseObserve seed15 = p17-7-5-7
previousSparseObserve identity = p17-8-7-7
previousSparseObserve rotate1 = p17-3-7-7
previousSparseObserve rotate2 = p16-6-7-6
previousSparseObserve rotate3 = p17-7-6-8
previousSparseObserve affine3 = p16-7-8-8
previousSparseObserve affine5 = p17-7-7-8
previousSparseObserve affine7 = p17-5-8-7
previousSparseObserve affine9 = p16-7-7-7
previousSparseObserve xor1 = p17-6-8-8
previousSparseObserve bitrev9 = p16-7-7-6

PreviousSparseDefect : Set₁
PreviousSparseDefect =
  Query.QueryAdequacyDefect previousSparseObserve receiptSemantics receiptIdentity

seed7Seed8PreviousSparseCollision : PreviousSparseDefect
seed7Seed8PreviousSparseCollision =
  Query.queryAdequacyDefect seed7 seed8 refl (λ ())

previousSparseObserverNotAdequate :
  Query.AdequateFor previousSparseObserve receiptSemantics receiptIdentity → ⊥
previousSparseObserverNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation seed7Seed8PreviousSparseCollision

------------------------------------------------------------------------
-- Selected four-rank raw-mode observer: (degree,r4,r5,r7,r9).
------------------------------------------------------------------------

data StressSparseKey : Set where
  k16-7-7-8-8 k17-7-8-8-8 k17-7-6-7-7 : StressSparseKey
  k16-7-8-7-7 k16-8-7-7-7 k17-7-8-7-6 : StressSparseKey
  k17-8-8-7-7 k16-6-7-7-7 k16-6-7-7-6 : StressSparseKey
  k17-8-8-7-8 k16-8-8-8-8 k16-6-5-7-7 : StressSparseKey
  k17-6-7-8-8 k16-8-8-7-7 k16-6-7-7-8 : StressSparseKey
  k17-5-7-7-7 k17-7-7-6-6 k17-7-8-8-7 : StressSparseKey
  k16-7-8-8-7 k17-6-8-7-7 k16-8-7-8-7 : StressSparseKey
  k17-7-8-7-7 k17-8-6-7-6 k16-7-7-7-7 : StressSparseKey
  k17-8-7-7-7 k16-7-7-6-7 : StressSparseKey

selectedStressSparseObserve : StressWorld → StressSparseKey
selectedStressSparseObserve seed0 = k16-7-7-8-8
selectedStressSparseObserve seed1 = k17-7-8-8-8
selectedStressSparseObserve seed2 = k17-7-6-7-7
selectedStressSparseObserve seed3 = k16-7-8-7-7
selectedStressSparseObserve seed4 = k16-8-7-7-7
selectedStressSparseObserve seed5 = k17-7-8-7-6
selectedStressSparseObserve seed6 = k17-8-8-7-7
selectedStressSparseObserve seed7 = k16-6-7-7-7
selectedStressSparseObserve seed8 = k16-6-7-7-6
selectedStressSparseObserve seed9 = k17-8-8-7-8
selectedStressSparseObserve seed10 = k16-8-8-8-8
selectedStressSparseObserve seed11 = k16-6-5-7-7
selectedStressSparseObserve seed12 = k17-6-7-8-8
selectedStressSparseObserve seed13 = k16-8-8-7-7
selectedStressSparseObserve seed14 = k16-6-7-7-8
selectedStressSparseObserve seed15 = k17-5-7-7-7
selectedStressSparseObserve identity = k17-7-7-6-6
selectedStressSparseObserve rotate1 = k17-7-8-8-7
selectedStressSparseObserve rotate2 = k16-7-8-8-7
selectedStressSparseObserve rotate3 = k17-6-8-7-7
selectedStressSparseObserve affine3 = k16-8-7-8-7
selectedStressSparseObserve affine5 = k17-7-8-7-7
selectedStressSparseObserve affine7 = k17-8-6-7-6
selectedStressSparseObserve affine9 = k16-7-7-7-7
selectedStressSparseObserve xor1 = k17-8-7-7-7
selectedStressSparseObserve bitrev9 = k16-7-7-6-7

answerFromStressSparseKey : StressSparseKey → ReceiptAnswer
answerFromStressSparseKey k16-7-7-8-8 = seed0Receipt
answerFromStressSparseKey k17-7-8-8-8 = seed1Receipt
answerFromStressSparseKey k17-7-6-7-7 = seed2Receipt
answerFromStressSparseKey k16-7-8-7-7 = seed3Receipt
answerFromStressSparseKey k16-8-7-7-7 = seed4Receipt
answerFromStressSparseKey k17-7-8-7-6 = seed5Receipt
answerFromStressSparseKey k17-8-8-7-7 = seed6Receipt
answerFromStressSparseKey k16-6-7-7-7 = seed7Receipt
answerFromStressSparseKey k16-6-7-7-6 = seed8Receipt
answerFromStressSparseKey k17-8-8-7-8 = seed9Receipt
answerFromStressSparseKey k16-8-8-8-8 = seed10Receipt
answerFromStressSparseKey k16-6-5-7-7 = seed11Receipt
answerFromStressSparseKey k17-6-7-8-8 = seed12Receipt
answerFromStressSparseKey k16-8-8-7-7 = seed13Receipt
answerFromStressSparseKey k16-6-7-7-8 = seed14Receipt
answerFromStressSparseKey k17-5-7-7-7 = seed15Receipt
answerFromStressSparseKey k17-7-7-6-6 = identityReceipt
answerFromStressSparseKey k17-7-8-8-7 = rotate1Receipt
answerFromStressSparseKey k16-7-8-8-7 = rotate2Receipt
answerFromStressSparseKey k17-6-8-7-7 = rotate3Receipt
answerFromStressSparseKey k16-8-7-8-7 = affine3Receipt
answerFromStressSparseKey k17-7-8-7-7 = affine5Receipt
answerFromStressSparseKey k17-8-6-7-6 = affine7Receipt
answerFromStressSparseKey k16-7-7-7-7 = affine9Receipt
answerFromStressSparseKey k17-8-7-7-7 = xor1Receipt
answerFromStressSparseKey k16-7-7-6-7 = bitrev9Receipt

selectedStressSparseFactorisation :
  (world : StressWorld) →
  receiptAnswer receiptIdentity world
  ≡ answerFromStressSparseKey (selectedStressSparseObserve world)
selectedStressSparseFactorisation seed0 = refl
selectedStressSparseFactorisation seed1 = refl
selectedStressSparseFactorisation seed2 = refl
selectedStressSparseFactorisation seed3 = refl
selectedStressSparseFactorisation seed4 = refl
selectedStressSparseFactorisation seed5 = refl
selectedStressSparseFactorisation seed6 = refl
selectedStressSparseFactorisation seed7 = refl
selectedStressSparseFactorisation seed8 = refl
selectedStressSparseFactorisation seed9 = refl
selectedStressSparseFactorisation seed10 = refl
selectedStressSparseFactorisation seed11 = refl
selectedStressSparseFactorisation seed12 = refl
selectedStressSparseFactorisation seed13 = refl
selectedStressSparseFactorisation seed14 = refl
selectedStressSparseFactorisation seed15 = refl
selectedStressSparseFactorisation identity = refl
selectedStressSparseFactorisation rotate1 = refl
selectedStressSparseFactorisation rotate2 = refl
selectedStressSparseFactorisation rotate3 = refl
selectedStressSparseFactorisation affine3 = refl
selectedStressSparseFactorisation affine5 = refl
selectedStressSparseFactorisation affine7 = refl
selectedStressSparseFactorisation affine9 = refl
selectedStressSparseFactorisation xor1 = refl
selectedStressSparseFactorisation bitrev9 = refl

SelectedStressSparseObserverAdequacy : Set₁
SelectedStressSparseObserverAdequacy =
  Query.AdequateFor selectedStressSparseObserve receiptSemantics receiptIdentity

selectedStressSparseObserverAdequate : SelectedStressSparseObserverAdequacy
selectedStressSparseObserverAdequate =
  Query.factorsForQuery answerFromStressSparseKey selectedStressSparseFactorisation

record SparseRawRankStressFrontierBoundary : Set where
  constructor sparse-raw-rank-stress-frontier-boundary
  field
    previousEighteenWorldSparseObserverInherited : Bool
    eightFreshSeedWorldsAdded : Bool
    previousDegreeR2R4R10ObserverCollides : Bool
    explicitSeed7Seed8CollisionPaid : Bool
    runtimeSearchFindsNoDegreePlusThreeRankObserver : Bool
    runtimeFirstSparseCoordinateCountIsFour : Bool
    selectedDegreeR4R5R7R9SeparatesTwentySix : Bool
    selectedStressFactorisationPaid : Bool
    firstContiguousRepairNeedsFiveRanksF2ThroughF6 : Bool
    runtimeMinimalityIsKernelTheorem : Bool
    selectedObserverReplaysCoefficients : Bool
    selectedObserverProductionSufficient : Bool
    selectedObserverGloballyMinimal : Bool
open SparseRawRankStressFrontierBoundary public

canonicalSparseRawRankStressFrontierBoundary : SparseRawRankStressFrontierBoundary
canonicalSparseRawRankStressFrontierBoundary =
  sparse-raw-rank-stress-frontier-boundary
    true true true true true true true true true false false false false

data SparseRawRankStressResidual : Set where
  attackSelectedFourRankObserverWithFreshAdapters : SparseRawRankStressResidual
  compareSixRuntimeMinimalFourRankSetsOnAcquisitionCost : SparseRawRankStressResidual
  formallyAttackAllDegreePlusThreeRankSubsets : SparseRawRankStressResidual
  testSelectedObserverAgainstNonReceiptConsumers : SparseRawRankStressResidual
  retainExactReplayTailSeparately : SparseRawRankStressResidual

firstSparseRawRankStressResidual : SparseRawRankStressResidual
firstSparseRawRankStressResidual = attackSelectedFourRankObserverWithFreshAdapters

previousBoundary : Previous.SparseRawRankObserverFrontierBoundary
previousBoundary = Previous.canonicalSparseRawRankObserverFrontierBoundary
