module DASHI.ComputerScience.RSA260BidiSparseRawRankObserverFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.ComputerScience.RSA260BidiRawRankCrossValidationAcquisitionExact as Acquisition

------------------------------------------------------------------------
-- SPARSE RAW-RANK OBSERVER FRONTIER
--
-- Reacquire the per-run generator coefficients from the same 8 independent
-- projection-seed runs + the discovery adapter family.  The old contiguous
-- receipt observer (degree,r2,r3,r4) does NOT survive the independent family:
-- seed0/seed3 collide at (16,8,7,7), and seed2/affine5 collide at
-- (17,7,7,7), while their recovered generator digests differ.
--
-- Instead of simply growing a contiguous prefix, search sparse coefficient-rank
-- coordinates.  Across the combined 18 unique worlds, the checked observer
--
--   (degree, rank F2, rank F4, rank F10)
--
-- separates every current receipt identity.  Runtime exhaustive subset search
-- over rank indices 0..15 found no one- or two-rank observer (with degree) and
-- found two three-rank sets: (2,4,10) and (2,10,11).
--
-- Only the selected 18-world factorisation is formal below.  The exhaustive
-- subset-search minimality claim remains a local runtime receipt.
------------------------------------------------------------------------

record SparseRawRankRuntimeReceipt : Set where
  constructor sparse-raw-rank-runtime-receipt
  field
    reacquisitionScriptPath : String
    reacquisitionScriptSHA256 : String
    reacquisitionOutputPath : String
    reacquisitionOutputSHA256 : String
    sparseSearchScriptPath : String
    sparseSearchScriptSHA256 : String
    sparseSearchOutputPath : String
    sparseSearchOutputSHA256 : String
    combinedUniqueWorlds : Nat
    independentSeedWorlds : Nat
    discoveryWorlds : Nat
    selectedRankIndex0 selectedRankIndex1 selectedRankIndex2 : Nat
    selectedObserverCollisionCount : Nat
    minimumRankCoordinateCountFoundWithDegree : Nat
    exhaustiveSubsetSearchIndicesZeroThroughFifteen : Bool
    exactLocalRuntimeExecuted : Bool
    runtimeCommittedToProducerRepository : Bool
open SparseRawRankRuntimeReceipt public

currentSparseRawRankRuntimeReceipt : SparseRawRankRuntimeReceipt
currentSparseRawRankRuntimeReceipt =
  sparse-raw-rank-runtime-receipt
    "/mnt/data/rsa260_bidi_raw_rank_crossvalidate.py"
    "aaf9b4f81c06a3c87cb96b922b4d373bd07b0aec087d5d715c6923ae2cb49d45"
    "/mnt/data/rsa260_bidi_raw_rank_crossvalidate.json"
    "9801d71ef96bbbd992526af68669d91103d22c41298000a5919800bad61fe5ef"
    "/mnt/data/rsa260_bidi_sparse_raw_rank_frontier.py"
    "4fd87c3966db8d6d45271bf504591b008ccabb3fef743ed9b3364e1e144bb57d"
    "/mnt/data/rsa260_bidi_sparse_raw_rank_frontier.json"
    "95c1a0d424aa0c9d50bb9ccef2052ecf71457339c7b2b35c915011aca3bc3ef1"
    18 8 10 2 4 10 0 3 true true false

------------------------------------------------------------------------
-- Combined finite carrier: eight independent seed worlds plus the ten-world
-- discovery family.  Baseline adapter repeats are unified with discovery.
------------------------------------------------------------------------

data CombinedWorld : Set where
  seed0 seed1 seed2 seed3 seed4 seed5 seed6 seed7 : CombinedWorld
  identity rotate1 rotate2 rotate3 affine3 affine5 affine7 affine9 xor1 bitrev9 : CombinedWorld

data ReceiptQuery : Set where
  receiptIdentity : ReceiptQuery

data ReceiptAnswer : Set where
  seed0Receipt seed1Receipt seed2Receipt seed3Receipt : ReceiptAnswer
  seed4Receipt seed5Receipt seed6Receipt seed7Receipt : ReceiptAnswer
  identityReceipt rotate1Receipt rotate2Receipt rotate3Receipt : ReceiptAnswer
  affine3Receipt affine5Receipt affine7Receipt affine9Receipt : ReceiptAnswer
  xor1Receipt bitrev9Receipt : ReceiptAnswer

receiptAnswer : ReceiptQuery → CombinedWorld → ReceiptAnswer
receiptAnswer receiptIdentity seed0 = seed0Receipt
receiptAnswer receiptIdentity seed1 = seed1Receipt
receiptAnswer receiptIdentity seed2 = seed2Receipt
receiptAnswer receiptIdentity seed3 = seed3Receipt
receiptAnswer receiptIdentity seed4 = seed4Receipt
receiptAnswer receiptIdentity seed5 = seed5Receipt
receiptAnswer receiptIdentity seed6 = seed6Receipt
receiptAnswer receiptIdentity seed7 = seed7Receipt
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

receiptSemantics : Query.QuerySemantics CombinedWorld ReceiptQuery ReceiptAnswer
receiptSemantics = Query.querySemantics receiptAnswer

------------------------------------------------------------------------
-- Old contiguous three-raw-rank observer fails after independent-seed attack.
------------------------------------------------------------------------

data DegreeRaw234 : Set where
  d16-8-7-7 : DegreeRaw234
  d17-6-6-7 : DegreeRaw234
  d17-7-7-7 : DegreeRaw234
  d16-6-8-8 : DegreeRaw234
  d17-6-7-7 : DegreeRaw234
  d17-7-7-8 : DegreeRaw234
  d16-7-7-6 : DegreeRaw234
  d17-8-8-7 : DegreeRaw234
  d17-3-7-7 : DegreeRaw234
  d16-6-7-7 : DegreeRaw234
  d17-7-7-6 : DegreeRaw234
  d16-7-7-8 : DegreeRaw234
  d17-5-7-8 : DegreeRaw234
  d16-7-6-7 : DegreeRaw234
  d17-6-7-8 : DegreeRaw234
  d16-7-7-7 : DegreeRaw234

contiguous234Observe : CombinedWorld → DegreeRaw234
contiguous234Observe seed0 = d16-8-7-7
contiguous234Observe seed1 = d17-6-6-7
contiguous234Observe seed2 = d17-7-7-7
contiguous234Observe seed3 = d16-8-7-7
contiguous234Observe seed4 = d16-6-8-8
contiguous234Observe seed5 = d17-6-7-7
contiguous234Observe seed6 = d17-7-7-8
contiguous234Observe seed7 = d16-7-7-6
contiguous234Observe identity = d17-8-8-7
contiguous234Observe rotate1 = d17-3-7-7
contiguous234Observe rotate2 = d16-6-7-7
contiguous234Observe rotate3 = d17-7-7-6
contiguous234Observe affine3 = d16-7-7-8
contiguous234Observe affine5 = d17-7-7-7
contiguous234Observe affine7 = d17-5-7-8
contiguous234Observe affine9 = d16-7-6-7
contiguous234Observe xor1 = d17-6-7-8
contiguous234Observe bitrev9 = d16-7-7-7

Contiguous234Defect : Set₁
Contiguous234Defect =
  Query.QueryAdequacyDefect contiguous234Observe receiptSemantics receiptIdentity

seed0Seed3Collision : Contiguous234Defect
seed0Seed3Collision = Query.queryAdequacyDefect seed0 seed3 refl (λ ())

contiguous234NotAdequate :
  Query.AdequateFor contiguous234Observe receiptSemantics receiptIdentity → ⊥
contiguous234NotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation seed0Seed3Collision

------------------------------------------------------------------------
-- Sparse selected observer: (degree, rank F2, rank F4, rank F10).
------------------------------------------------------------------------

data SparseRankKey : Set where
  k16-8-7-7 k17-6-7-7 k17-7-7-6 k16-8-7-8 : SparseRankKey
  k16-6-8-8 k17-6-7-6 k17-7-8-7 k16-7-6-7 : SparseRankKey
  k17-8-7-7 k17-3-7-7 k16-6-7-6 k17-7-6-8 : SparseRankKey
  k16-7-8-8 k17-7-7-8 k17-5-8-7 k16-7-7-7 : SparseRankKey
  k17-6-8-8 k16-7-7-6 : SparseRankKey

selectedSparseObserve : CombinedWorld → SparseRankKey
selectedSparseObserve seed0 = k16-8-7-7
selectedSparseObserve seed1 = k17-6-7-7
selectedSparseObserve seed2 = k17-7-7-6
selectedSparseObserve seed3 = k16-8-7-8
selectedSparseObserve seed4 = k16-6-8-8
selectedSparseObserve seed5 = k17-6-7-6
selectedSparseObserve seed6 = k17-7-8-7
selectedSparseObserve seed7 = k16-7-6-7
selectedSparseObserve identity = k17-8-7-7
selectedSparseObserve rotate1 = k17-3-7-7
selectedSparseObserve rotate2 = k16-6-7-6
selectedSparseObserve rotate3 = k17-7-6-8
selectedSparseObserve affine3 = k16-7-8-8
selectedSparseObserve affine5 = k17-7-7-8
selectedSparseObserve affine7 = k17-5-8-7
selectedSparseObserve affine9 = k16-7-7-7
selectedSparseObserve xor1 = k17-6-8-8
selectedSparseObserve bitrev9 = k16-7-7-6

answerFromSparseKey : SparseRankKey → ReceiptAnswer
answerFromSparseKey k16-8-7-7 = seed0Receipt
answerFromSparseKey k17-6-7-7 = seed1Receipt
answerFromSparseKey k17-7-7-6 = seed2Receipt
answerFromSparseKey k16-8-7-8 = seed3Receipt
answerFromSparseKey k16-6-8-8 = seed4Receipt
answerFromSparseKey k17-6-7-6 = seed5Receipt
answerFromSparseKey k17-7-8-7 = seed6Receipt
answerFromSparseKey k16-7-6-7 = seed7Receipt
answerFromSparseKey k17-8-7-7 = identityReceipt
answerFromSparseKey k17-3-7-7 = rotate1Receipt
answerFromSparseKey k16-6-7-6 = rotate2Receipt
answerFromSparseKey k17-7-6-8 = rotate3Receipt
answerFromSparseKey k16-7-8-8 = affine3Receipt
answerFromSparseKey k17-7-7-8 = affine5Receipt
answerFromSparseKey k17-5-8-7 = affine7Receipt
answerFromSparseKey k16-7-7-7 = affine9Receipt
answerFromSparseKey k17-6-8-8 = xor1Receipt
answerFromSparseKey k16-7-7-6 = bitrev9Receipt

selectedSparseFactorisation :
  (world : CombinedWorld) →
  receiptAnswer receiptIdentity world
  ≡ answerFromSparseKey (selectedSparseObserve world)
selectedSparseFactorisation seed0 = refl
selectedSparseFactorisation seed1 = refl
selectedSparseFactorisation seed2 = refl
selectedSparseFactorisation seed3 = refl
selectedSparseFactorisation seed4 = refl
selectedSparseFactorisation seed5 = refl
selectedSparseFactorisation seed6 = refl
selectedSparseFactorisation seed7 = refl
selectedSparseFactorisation identity = refl
selectedSparseFactorisation rotate1 = refl
selectedSparseFactorisation rotate2 = refl
selectedSparseFactorisation rotate3 = refl
selectedSparseFactorisation affine3 = refl
selectedSparseFactorisation affine5 = refl
selectedSparseFactorisation affine7 = refl
selectedSparseFactorisation affine9 = refl
selectedSparseFactorisation xor1 = refl
selectedSparseFactorisation bitrev9 = refl

SelectedSparseObserverAdequacy : Set₁
SelectedSparseObserverAdequacy =
  Query.AdequateFor selectedSparseObserve receiptSemantics receiptIdentity

selectedSparseObserverAdequate : SelectedSparseObserverAdequacy
selectedSparseObserverAdequate =
  Query.factorsForQuery answerFromSparseKey selectedSparseFactorisation

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record SparseRawRankObserverFrontierBoundary : Set where
  constructor sparse-raw-rank-observer-frontier-boundary
  field
    sameIndependentSyntheticRunsReacquired : Bool
    contiguousDegreeR2R3R4FailsIndependentFamily : Bool
    explicitSeed0Seed3CollisionPaid : Bool
    selectedSparseDegreeR2R4R10SeparatesCombinedEighteen : Bool
    selectedSparseObserverFormalFactorisationPaid : Bool
    runtimeSearchFoundNoDegreePlusOneRankObserver : Bool
    runtimeSearchFoundNoDegreePlusTwoRankObserver : Bool
    runtimeSearchFoundTwoThreeRankObserverSets : Bool
    allTwoRankImpossibilityKernelProvedInAgda : Bool
    selectedSparseObserverReplaysCoefficients : Bool
    selectedSparseObserverAlgebraicallyIdentifiesGenerator : Bool
    selectedSparseObserverProductionSufficient : Bool
    selectedSparseObserverGloballyMinimal : Bool
open SparseRawRankObserverFrontierBoundary public

canonicalSparseRawRankObserverFrontierBoundary :
  SparseRawRankObserverFrontierBoundary
canonicalSparseRawRankObserverFrontierBoundary =
  sparse-raw-rank-observer-frontier-boundary
    true true true true true true true true
    false false false false false

data SparseRawRankObserverResidual : Set where
  formallyAttackAllDegreePlusTwoRankSubsets : SparseRawRankObserverResidual
  compareSparseTriplesOnDescriptionAndAcquisitionCost : SparseRawRankObserverResidual
  attackSparseObserverWithNewSeedAndAdapterFamilies : SparseRawRankObserverResidual
  testSparseObserverAgainstNonReceiptConsumers : SparseRawRankObserverResidual
  retainExactReplayTailSeparately : SparseRawRankObserverResidual

firstSparseRawRankObserverResidual : SparseRawRankObserverResidual
firstSparseRawRankObserverResidual = formallyAttackAllDegreePlusTwoRankSubsets

acquisitionBoundary : Acquisition.RawRankCrossValidationAcquisitionBoundary
acquisitionBoundary = Acquisition.canonicalRawRankCrossValidationAcquisitionBoundary
