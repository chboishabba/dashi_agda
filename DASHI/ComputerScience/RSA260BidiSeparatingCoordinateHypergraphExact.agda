module DASHI.ComputerScience.RSA260BidiSeparatingCoordinateHypergraphExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- CONSUMER-RELATIVE SPARSE COORDINATE SELECTION AS A HITTING PROBLEM
--
-- For worlds that the retained coarse degree coordinate does not already
-- distinguish, every pair separated by the declared consumer induces a
-- constraint edge.  A rank coordinate hits that edge when its values differ on
-- the pair.  A selected coordinate family is sufficient exactly when every
-- declared consumer-separating equal-degree pair is hit.
--
-- This is a DASHI synthesis of the already executed sparse-rank search.  It is
-- not attributed to OEIS.  OEIS A082874 happened to contain several integers
-- occurring in our stress history (18, 26, 34, 64, 72), but A082874 is the
-- independence number of a king graph on triangular boards.  No structural map
-- from that graph family to RSA-260 is established here; the numerical overlap
-- is retained only as a bounded snowball observation.
------------------------------------------------------------------------

record SeparatingCoordinateProblem : Set₁ where
  field
    World Coordinate DegreeValue CoordinateValue ConsumerValue : Set
    degree : World → DegreeValue
    coordinate : Coordinate → World → CoordinateValue
    consumer : World → ConsumerValue

open SeparatingCoordinateProblem public

SameDegree : (P : SeparatingCoordinateProblem) → World P → World P → Set
SameDegree P left right = degree P left ≡ degree P right

ConsumerSeparates : (P : SeparatingCoordinateProblem) → World P → World P → Set
ConsumerSeparates P left right = consumer P left ≡ consumer P right → ⊥

CoordinateSeparates :
  (P : SeparatingCoordinateProblem) → Coordinate P → World P → World P → Set
CoordinateSeparates P c left right =
  coordinate P c left ≡ coordinate P c right → ⊥

record SelectedCoordinateFamily (P : SeparatingCoordinateProblem) : Set₁ where
  field
    Selected : Coordinate P → Set
    hitsEveryEqualDegreeConsumerPair :
      (left right : World P) →
      SameDegree P left right →
      ConsumerSeparates P left right →
      Σ (Coordinate P) (λ c → Selected c × CoordinateSeparates P c left right)

open SelectedCoordinateFamily public

------------------------------------------------------------------------
-- Runtime receipt from the current 34-world synthetic generator portfolio.
--
-- Universe construction:
--   * degree is retained separately;
--   * only equal-degree, distinct-consumer pairs need a rank coordinate;
--   * coordinate i hits a pair iff rank(F_i) differs for that pair.
--
-- Exhaustive local search over the 14 rank coordinates available in every
-- world found 258 equal-degree distinct-identity pair constraints.  Minimum
-- hitting-set size in that finite runtime search was 5, with 26 distinct
-- size-five solutions.  This is not promoted to a generic theorem or to a
-- production RSA-260 statement.
------------------------------------------------------------------------

record SeparatingCoordinateRuntimeReceipt : Set where
  constructor separating-coordinate-runtime-receipt
  field
    worldCount : Nat
    commonRankCoordinateCount : Nat
    equalDegreeDistinctConsumerPairCount : Nat
    minimumHittingSetSizeFound : Nat
    minimumSizeSolutionCountFound : Nat
    selectedCoordinate0 : Nat
    selectedCoordinate1 : Nat
    selectedCoordinate2 : Nat
    selectedCoordinate3 : Nat
    selectedCoordinate4 : Nat
    greedyCoordinate0 : Nat
    greedyCoordinate1 : Nat
    greedyCoordinate2 : Nat
    greedyCoordinate3 : Nat
    greedyCoordinate4 : Nat
    exhaustiveFiniteSubsetSearchRun : Bool
    selectedFiveHitsAllCurrentPairConstraints : Bool
    minimumFiveKernelProved : Bool
    productionRSA260CarrierUsed : Bool
    runtimeReceiptReference : String

open SeparatingCoordinateRuntimeReceipt public

currentSeparatingCoordinateRuntimeReceipt : SeparatingCoordinateRuntimeReceipt
currentSeparatingCoordinateRuntimeReceipt =
  separating-coordinate-runtime-receipt
    34
    14
    258
    5
    26
    1 4 5 7 9
    10 2 4 9 11
    true
    true
    false
    false
    "rsa260_bidi_coordinate_hitting_set.json; finite synthetic 34-world portfolio"

------------------------------------------------------------------------
-- OEIS snowball boundary.
------------------------------------------------------------------------

record OEISGraphSnowballBoundary : Set where
  constructor oeis-graph-snowball-boundary
  field
    oeisSequence : String
    oeisTitle : String
    observedOverlap : String
    numericalOverlapObserved : Bool
    structuralMapToRSAWorldGraphPaid : Bool
    oeisIndependenceNumberExplainsRSAObserverGrowth : Bool
    graphHittingSetViewUsefulIndependentlyOfOEIS : Bool

open OEISGraphSnowballBoundary public

currentOEISGraphSnowballBoundary : OEISGraphSnowballBoundary
currentOEISGraphSnowballBoundary =
  oeis-graph-snowball-boundary
    "A082874"
    "Independence number of king KG_4 on triangle board B_n"
    "A082874 contains 18,26,34,64,72, all numbers that also appeared incidentally in this RSA tranche"
    true
    false
    false
    true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OEISNumericOverlapImpliesRSACombinatorialIdentity : Set where
data FiniteHittingSetMinimumImpliesProductionMinimum : Set where

oeisOverlapDoesNotCreateStructuralIdentity :
  OEISNumericOverlapImpliesRSACombinatorialIdentity → ⊥
oeisOverlapDoesNotCreateStructuralIdentity ()

finiteMinimumDoesNotCreateProductionMinimum :
  FiniteHittingSetMinimumImpliesProductionMinimum → ⊥
finiteMinimumDoesNotCreateProductionMinimum ()

record SeparatingCoordinateHypergraphBoundary : Set where
  constructor separating-coordinate-hypergraph-boundary
  field
    pairConstraintHypergraphInterpretationWritten : Bool
    currentFiniteRuntimeSearchPaid : Bool
    minimumFiveProvedInAgdaKernel : Bool
    oeisCheckedAsPatternDonor : Bool
    oeisStructuralIdentificationPaid : Bool
    nextUseShouldBeConsumerActionPairsNotReceiptIdentity : Bool
    exactReplayTailStillIndependent : Bool

open SeparatingCoordinateHypergraphBoundary public

canonicalSeparatingCoordinateHypergraphBoundary :
  SeparatingCoordinateHypergraphBoundary
canonicalSeparatingCoordinateHypergraphBoundary =
  separating-coordinate-hypergraph-boundary
    true
    true
    false
    true
    false
    true
    true
