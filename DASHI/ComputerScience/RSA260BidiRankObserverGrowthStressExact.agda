module DASHI.ComputerScience.RSA260BidiRankObserverGrowthStressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.ComputerScience.RSA260BidiSparseRawRankStressFrontierExact as Previous

------------------------------------------------------------------------
-- RANK-OBSERVER GROWTH UNDER PORTFOLIO STRESS
--
-- The 26-world selected rank observer (degree,r4,r5,r7,r9) is attacked with
-- eight fresh operator preparations.  It fails on multiple pairs; one exact
-- witness is rotate7 versus bitrev9, both exposing
--
--   (degree,r4,r5,r7,r9) = (16,7,7,6,7)
--
-- while their recovered generator digests differ.
--
-- Runtime subset search on the resulting 34-world portfolio finds the minimum
-- rank-coordinate count (with degree retained) has risen again:
--
--   18 worlds -> 3 rank coordinates
--   26 worlds -> 4 rank coordinates
--   34 worlds -> 5 rank coordinates
--
-- and the first separating contiguous prefix from F2 now needs six ranks.
-- This is evidence that a fixed tiny rank fingerprint is unstable for RECEIPT
-- identity as the adversarial family grows.  It is not a theorem of unbounded
-- rank dimension and does not weaken the exact replay tail.
------------------------------------------------------------------------

record RankObserverGrowthRuntimeReceipt : Set where
  constructor rank-observer-growth-runtime-receipt
  field
    adapterStressScriptPath : String
    adapterStressScriptSHA256 : String
    adapterStressOutputPath : String
    adapterStressOutputSHA256 : String
    growthSearchScriptPath : String
    growthSearchScriptSHA256 : String
    growthSearchOutputPath : String
    growthSearchOutputSHA256 : String
    stressedWorldCount : Nat
    freshAdapterWorldCount : Nat
    minimumRanksAtEighteenWorlds : Nat
    minimumRanksAtTwentySixWorlds : Nat
    minimumRanksAtThirtyFourWorlds : Nat
    firstContiguousRanksAtThirtyFourWorlds : Nat
    exactLocalRuntimeExecuted : Bool
    runtimeCommittedToProducerRepository : Bool
open RankObserverGrowthRuntimeReceipt public

currentRankObserverGrowthRuntimeReceipt : RankObserverGrowthRuntimeReceipt
currentRankObserverGrowthRuntimeReceipt =
  rank-observer-growth-runtime-receipt
    "/mnt/data/rsa260_bidi_sparse_raw_rank_adapter_stress.py"
    "6096d06c684c83fa2e07c836213f2889354f36c308fee0e3e51b0ed8cc79268b"
    "/mnt/data/rsa260_bidi_sparse_raw_rank_adapter_stress.json"
    "8136a400692f9b2ec055137c25ff125d273d364c9aa8f2c01547fea4a309f40b"
    "/mnt/data/rsa260_bidi_rank_observer_growth.py"
    "51bac180b3a23250e57c997ae7865ca687dc9b8c02c486cb4373c74da67d1f03"
    "/mnt/data/rsa260_bidi_rank_observer_growth.json"
    "fe4fbda0885f4e918d7e0016f9848d752b97cd2b393d2d53b410077676683a8e"
    34 8 3 4 5 6 true false

------------------------------------------------------------------------
-- Exact current-code failure witness.
------------------------------------------------------------------------

data AdapterStressWorld : Set where
  bitrev9World rotate7World : AdapterStressWorld

data StressedFourRankCode : Set where
  d16-r7-r7-r6-r7 : StressedFourRankCode

data ReceiptQuery : Set where receiptIdentity : ReceiptQuery

data ReceiptAnswer : Set where bitrev9Receipt rotate7Receipt : ReceiptAnswer

stressedFourRankObserve : AdapterStressWorld → StressedFourRankCode
stressedFourRankObserve bitrev9World = d16-r7-r7-r6-r7
stressedFourRankObserve rotate7World = d16-r7-r7-r6-r7

receiptAnswer : ReceiptQuery → AdapterStressWorld → ReceiptAnswer
receiptAnswer receiptIdentity bitrev9World = bitrev9Receipt
receiptAnswer receiptIdentity rotate7World = rotate7Receipt

receiptSemantics : Query.QuerySemantics AdapterStressWorld ReceiptQuery ReceiptAnswer
receiptSemantics = Query.querySemantics receiptAnswer

StressedFourRankDefect : Set₁
StressedFourRankDefect =
  Query.QueryAdequacyDefect stressedFourRankObserve receiptSemantics receiptIdentity

rotate7Bitrev9Collision : StressedFourRankDefect
rotate7Bitrev9Collision =
  Query.queryAdequacyDefect bitrev9World rotate7World refl (λ ())

stressedFourRankObserverNotAdequate :
  Query.AdequateFor stressedFourRankObserve receiptSemantics receiptIdentity → ⊥
stressedFourRankObserverNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation rotate7Bitrev9Collision

------------------------------------------------------------------------
-- Interpretation / Pareto recut.
------------------------------------------------------------------------

record RankObserverGrowthStressBoundary : Set where
  constructor rank-observer-growth-stress-boundary
  field
    priorTwentySixWorldFrontierInherited : Bool
    eightFreshOperatorPreparationsAdded : Bool
    priorFourRankObserverFails : Bool
    rotate7Bitrev9CollisionPaid : Bool
    runtimeMinimumRankCountGrowsThreeFourFive : Bool
    runtimeFirstContiguousCountAtThirtyFourIsSix : Bool
    fiveRankThirtyFourWorldCandidateFoundByRuntime : Bool
    fiveRankThirtyFourWorldCandidateKernelFactorisationPaid : Bool
    rankCoordinateGrowthProvesUnboundedRankRequirement : Bool
    fixedTinyRankFingerprintStableReceiptTerminal : Bool
    ranksRemainUsefulCheapDiagnostics : Bool
    exactReplayTailStillRequiredForReplayConsumer : Bool
    productionRSA260Claimed : Bool
open RankObserverGrowthStressBoundary public

canonicalRankObserverGrowthStressBoundary : RankObserverGrowthStressBoundary
canonicalRankObserverGrowthStressBoundary =
  rank-observer-growth-stress-boundary
    true true true true true true true false false false true true false

data RankObserverGrowthResidual : Set where
  stopTreatingTinyRankSketchAsStableReceiptTerminal : RankObserverGrowthResidual
  chooseConsumerWeActuallyNeedBeforeFurtherRankSearch : RankObserverGrowthResidual
  retainRanksAsCheapDiagnostics : RankObserverGrowthResidual
  retainExactReplayTailForReplayConsumer : RankObserverGrowthResidual
  onlyFormalizeFiveRankThirtyFourWorldCodeIfConsumerJustifiesIt : RankObserverGrowthResidual

firstRankObserverGrowthResidual : RankObserverGrowthResidual
firstRankObserverGrowthResidual = stopTreatingTinyRankSketchAsStableReceiptTerminal

previousBoundary : Previous.SparseRawRankStressFrontierBoundary
previousBoundary = Previous.canonicalSparseRawRankStressFrontierBoundary
