module DASHI.Mathematics.Complexity.PNotEqualsNPBlockEqualityDirectDPObstructionExact where

------------------------------------------------------------------------
-- BLOCK EQUALITY -> DIRECT-DP RESOURCE OBSTRUCTION
--
-- The literal equality owner provides one Shannon layer with 2^n distinct
-- residual Boolean functions.  The preferred direct-DP carrier therefore needs
-- at least 2^n states on any live state whose canonical indexed root is exactly
-- that equality root.
--
-- This owner packages the dependent same-object attachment and derives the
-- direct contradiction:
--
--   recursiveMeasure(state) <= 3 * 2^n
--       ->
--   no DirectDPChargedConstructionRun state.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits
import DASHI.Mathematics.Complexity.PNotEqualsNPBlockEqualityResidualWidthWitnessExact as EqualityWidth
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact as DirectDP
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate

------------------------------------------------------------------------
-- Dependent root carrier.
------------------------------------------------------------------------

IndexedRoot : Set
IndexedRoot =
  Σ Nat (λ variables → SAT.BooleanFormula variables)

RootResidualWidth :
  Nat →
  Nat →
  IndexedRoot →
  Set₁
RootResidualWidth remaining width (variables , root) =
  Width.ResidualWidthWitness
    {root = root}
    remaining
    width

------------------------------------------------------------------------
-- One live state identified, at the full dependent indexed-root level, with
-- the compact block-equality family.
------------------------------------------------------------------------

record BlockEqualityLiveRoot
    (state : Q2.BoundedSelfReferenceState)
    (width : Nat) : Set₁ where
  constructor block-equality-live-root
  field
    indexedRootExact :
      Bridge.cookFormulaIndexedView
        (Q2.currentFormula state)
      ≡
      ( width + width
      , EqualityWidth.blockEqualityFormula width
      )

open BlockEqualityLiveRoot public

------------------------------------------------------------------------
-- Transport the literal 2^n residual witness onto the actual live root.
------------------------------------------------------------------------

liveBlockEqualityResidualWidth :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {width : Nat} →
  BlockEqualityLiveRoot state width →
  Width.ResidualWidthWitness
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula state)}
    width
    (Bits.bitCardinality width)
liveBlockEqualityResidualWidth
    {state}
    {width}
    realization =
  subst
    (RootResidualWidth
      width
      (Bits.bitCardinality width))
    (sym
      (indexedRootExact realization))
    (EqualityWidth.blockEqualityResidualWidthWitness width)

------------------------------------------------------------------------
-- Any successful direct-DP run on this state therefore needs at least 2^n
-- automaton states.
------------------------------------------------------------------------

liveBlockEqualityStateLowerBound :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {width : Nat}
    (realization : BlockEqualityLiveRoot state width)
    (run : DirectDP.DirectDPChargedConstructionRun state) →
  Bits.bitCardinality width
  ≤
  Candidate.stateCount
    (DirectDP.candidate run)
liveBlockEqualityStateLowerBound realization run =
  DirectDP.directDPResidualWidthBelowStateCount
    run
    (liveBlockEqualityResidualWidth realization)

------------------------------------------------------------------------
-- Graph cost alone is already at least 3 * 2^n.
------------------------------------------------------------------------

liveBlockEqualityTripleWidthStrictlyBelowMeasure :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {width : Nat}
    (realization : BlockEqualityLiveRoot state width)
    (run : DirectDP.DirectDPChargedConstructionRun state) →
  Width.triple
      (Bits.bitCardinality width)
  <
  Q2.recursiveMeasure state
liveBlockEqualityTripleWidthStrictlyBelowMeasure
    realization
    run =
  DirectDP.directDPTripleResidualWidthStrictlyBelowCurrentMeasure
    run
    (liveBlockEqualityResidualWidth realization)

------------------------------------------------------------------------
-- Main obstruction.
------------------------------------------------------------------------

blockEqualityMeasureBlocksDirectDPRun :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {width : Nat} →
  BlockEqualityLiveRoot state width →
  Q2.recursiveMeasure state
  ≤
  Width.triple
    (Bits.bitCardinality width) →
  DirectDP.DirectDPChargedConstructionRun state →
  ⊥
blockEqualityMeasureBlocksDirectDPRun
    realization
    measureBelowExponentialGraph
    run =
  DirectDP.directDPSingleLayerHighWidthBlocksRun
    (liveBlockEqualityResidualWidth realization)
    measureBelowExponentialGraph
    run

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The equality test is now wired to the live repaired resource carrier.
--
-- What remains is only the SAME-OBJECT question:
--
--   can an actual self-instantiation state satisfy BlockEqualityLiveRoot
--   (or a semantics-preserving embedding strong enough to transport this width)
--   while its recursive measure is below 3 * 2^n?
--
-- If yes, the direct-DP Q1 route is blocked at that state.
-- If no, the theorem preventing that attachment is genuine special structure
-- of the live self-instantiation family.
------------------------------------------------------------------------
