module DASHI.Mathematics.Complexity.PNotEqualsNPNaivePrefixTrieAutomatonNoGoExact where

------------------------------------------------------------------------
-- NAIVE PREFIX-TRIE AUTOMATON NO-GO
--
-- Concrete SAT-blind builder under audit:
--
--   one automaton state for every reachable restriction prefix.
--
-- This transition system is trivial to construct: root state is the empty
-- prefix and each state has false/true children obtained by appending one bit.
--
-- But it performs no semantic merging.  For n variables the complete prefix
-- trie has
--
--   T(0) = 1
--   T(n+1) = 1 + 2*T(n)
--
-- states, hence at least 2^n states.
--
-- The live operational Q1 theorem requires every successful quotient to satisfy
--
--   stateCount(Q) < recursiveMeasure(current).
--
-- Therefore the naive prefix-trie builder cannot close any state for which
--
--   recursiveMeasure(current) <= 2^n.
--
-- This kills the simplest fully executable root-state/transition-table
-- constructor without assuming SAT hardness.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1OperationalConstructionCostExact as Operational
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits

------------------------------------------------------------------------
-- Exact state-count recurrence for a full Boolean restriction-prefix trie.
------------------------------------------------------------------------

prefixTrieStateCount : Nat → Nat
prefixTrieStateCount zero =
  suc zero
prefixTrieStateCount (suc variables) =
  suc
    (prefixTrieStateCount variables
      + prefixTrieStateCount variables)

prefixTrieStateCountRecurrence :
  (variables : Nat) →
  prefixTrieStateCount (suc variables)
  ≡
  suc
    (prefixTrieStateCount variables
      + prefixTrieStateCount variables)
prefixTrieStateCountRecurrence variables =
  refl

------------------------------------------------------------------------
-- There are at least as many trie states as full assignments/leaves.
------------------------------------------------------------------------

pow2BelowPrefixTrie :
  (variables : Nat) →
  Bits.bitCardinality variables
  ≤
  prefixTrieStateCount variables
pow2BelowPrefixTrie zero =
  NatP.≤-refl
pow2BelowPrefixTrie (suc variables) =
  NatP.≤-trans
    (NatP.+-mono-≤
      (pow2BelowPrefixTrie variables)
      (pow2BelowPrefixTrie variables))
    (NatP.n≤1+n
      (prefixTrieStateCount variables
        + prefixTrieStateCount variables))

------------------------------------------------------------------------
-- Identify a live Q1 run with the naive prefix-trie state table.
------------------------------------------------------------------------

record NaivePrefixTrieOperationalRun
    (variables : Nat)
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor naive-prefix-trie-operational-run
  field
    run :
      Operational.OperationalQ1ConstructionRun state

    stateCountIsPrefixTrie :
      Operational.q1WitnessStateCount
        (Operational.q1Witness run)
      ≡
      prefixTrieStateCount variables

open NaivePrefixTrieOperationalRun public

------------------------------------------------------------------------
-- Main charged no-go.
------------------------------------------------------------------------

naivePrefixTrieCannotCloseWhenAssignmentsReachMeasure :
  (variables : Nat)
  (state : Q2.BoundedSelfReferenceState) →
  Q2.recursiveMeasure state
    ≤ Bits.bitCardinality variables →
  NaivePrefixTrieOperationalRun variables state →
  ⊥
naivePrefixTrieCannotCloseWhenAssignmentsReachMeasure
    variables
    state
    measureBelowAssignments
    trieRun =
  NatP.<-irrefl
    (Q2.recursiveMeasure state)
    (NatP.≤-<-trans
      measureBelowTrieStates
      (Operational.stateCountStrictlyBelowCurrentMeasure
        (run trieRun)))
  where
    assignmentsBelowTrieStates :
      Bits.bitCardinality variables
      ≤
      Operational.q1WitnessStateCount
        (Operational.q1Witness (run trieRun))
    assignmentsBelowTrieStates =
      NatP.≤-trans
        (pow2BelowPrefixTrie variables)
        (NatP.≤-reflexive
          (symmetry (stateCountIsPrefixTrie trieRun)))
      where
        symmetry :
          ∀ {a b : Nat} →
          a ≡ b →
          b ≡ a
        symmetry refl = refl

    measureBelowTrieStates :
      Q2.recursiveMeasure state
      ≤
      Operational.q1WitnessStateCount
        (Operational.q1Witness (run trieRun))
    measureBelowTrieStates =
      NatP.≤-trans
        measureBelowAssignments
        assignmentsBelowTrieStates

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Two maximally honest SAT-blind builders are now eliminated in the same
-- relevant budget regime:
--
--   * exact raw-residual memoization;
--   * exact one-state-per-prefix restriction trie.
--
-- Both fail because they preserve too much information.
--
-- A viable transition-table constructor must therefore merge many restriction
-- prefixes/residual configurations by a reusable semantic invariant specific
-- to the self-instantiation family, while constructing that invariant without
-- first computing SAT truth.
------------------------------------------------------------------------
