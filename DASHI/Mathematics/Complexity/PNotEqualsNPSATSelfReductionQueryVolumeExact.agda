module DASHI.Mathematics.Complexity.PNotEqualsNPSATSelfReductionQueryVolumeExact where

------------------------------------------------------------------------
-- EXACT QUERY-SIZE VOLUME OF STANDARD SAT SELF-REDUCTION
--
-- Existing SAT decision-to-search reduction:
--
--   one exact SAT query per remaining variable.
--
-- Existing size theorem:
--
--   restrictHead preserves syntax-node count exactly.
--
-- This owner combines them operationally.  It follows the same oracle-guided
-- branch recursion as recoverWitness and charges each SAT query by the syntax
-- node count of the queried restricted formula.
--
-- Main theorem:
--
--   queryVolume(phi) = variables(phi) * nodeCount(phi).
--
-- Thus ordinary SAT self-reduction does not create a shrinking sequence of
-- decider input sizes.  It performs n same-size SAT queries.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.SATDecisionToWitnessSelfReductionExact as Search
import DASHI.Mathematics.Complexity.PNotEqualsNPSATSelfReductionSizeNoGoExact as Size

------------------------------------------------------------------------
-- Operational syntax-volume of the exact self-reduction.
------------------------------------------------------------------------

satSearchQueryVolume :
  (oracle : SAT.SATDecisionOracle) →
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula variables) →
  SAT.Satisfying formula →
  Nat
satSearchQueryVolume oracle {zero} formula satisfiable =
  zero
satSearchQueryVolume oracle {suc variables} formula satisfiable
    with Search.decide oracle (SAT.restrictHead false formula)
... | true =
  Size.formulaNodeCount
    (SAT.restrictHead false formula)
  +
  satSearchQueryVolume
    oracle
    (SAT.restrictHead false formula)
    (Search.sound
      oracle
      (SAT.restrictHead false formula)
      refl)
... | false with SAT.satisfiableSplits formula satisfiable
...   | inj₁ falseSat =
  ⊥-elim
    (Search.falseDecisionExcludesSatisfiable
      oracle
      (SAT.restrictHead false formula)
      refl
      falseSat)
...   | inj₂ trueSat =
  Size.formulaNodeCount
    (SAT.restrictHead false formula)
  +
  satSearchQueryVolume
    oracle
    (SAT.restrictHead true formula)
    trueSat

------------------------------------------------------------------------
-- Exact n*N accounting.
------------------------------------------------------------------------

satSearchQueryVolumeExact :
  (oracle : SAT.SATDecisionOracle) →
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula variables)
    (satisfiable : SAT.Satisfying formula) →
  satSearchQueryVolume
    oracle
    formula
    satisfiable
  ≡
  variables * Size.formulaNodeCount formula
satSearchQueryVolumeExact
    oracle {zero} formula satisfiable =
  refl
satSearchQueryVolumeExact
    oracle {suc variables} formula satisfiable
    with Search.decide oracle (SAT.restrictHead false formula)
... | true
    rewrite
      Size.restrictHeadPreservesNodeCount false formula
      |
      satSearchQueryVolumeExact
        oracle
        (SAT.restrictHead false formula)
        (Search.sound
          oracle
          (SAT.restrictHead false formula)
          refl)
      |
      Size.restrictHeadPreservesNodeCount false formula =
  refl
... | false with SAT.satisfiableSplits formula satisfiable
...   | inj₁ falseSat =
  ⊥-elim
    (Search.falseDecisionExcludesSatisfiable
      oracle
      (SAT.restrictHead false formula)
      refl
      falseSat)
...   | inj₂ trueSat
    rewrite
      Size.restrictHeadPreservesNodeCount false formula
      |
      satSearchQueryVolumeExact
        oracle
        (SAT.restrictHead true formula)
        trueSat
      |
      Size.restrictHeadPreservesNodeCount true formula =
  refl

------------------------------------------------------------------------
-- Research consequence.
--
-- If a hypothetical SAT decider costs T(N) on N-node formulas, the standard
-- decision-to-search route invokes it n times on formulas still of size N.
-- This owner deliberately does not assume any particular runtime model, but
-- it records the exact structural fact needed for such a cost lift:
--
--   number of queries = n
--   size of each query = N
--
-- Hence ordinary SAT self-reducibility does not provide the strictly-smaller
-- recursive calls required by the current self-diagonal strategy.
------------------------------------------------------------------------
