module DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableTerminalAdmissionExact where

------------------------------------------------------------------------
-- TERMINAL OBSERVATIONS FOR THE ROOT-REACHABLE NUMERIC QUOTIENT
--
-- At zero remaining variables a semantic truth table has one Boolean entry.
-- Its value is the literal SAT.evaluate result on any zero-arity restriction
-- node representing that canonical key.
--
-- The chosen restriction is proved to originate in the rooted enumeration,
-- and semantic-key equality makes the chosen history irrelevant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalFutureCongruenceExact as Future
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableNumericQuotientExact as Reachable
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalRepresentativeSelectionExact as Rep
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1IndexedTruthTableAutomatonExact as Indexed

------------------------------------------------------------------------
-- This is a real computed zero-arity output, with no terminal-label oracle.
------------------------------------------------------------------------

reachableTerminalLabel :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (path : Root.DescentPath root zero) →
  Reachable.ReachableNumericState path →
  Bool
reachableTerminalLabel path index =
  Vec.lookup
    (Reachable.decodeReachableState path index)
    Fin.zero

------------------------------------------------------------------------
-- Sound on the literal formula of an actual representative.
------------------------------------------------------------------------

reachableTerminalLabelExact :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (path : Root.DescentPath root zero)
    (index : Reachable.ReachableNumericState path) →
  let representative =
        Rep.representativeOfIndex path index
  in
  reachableTerminalLabel path index
  ≡
  SAT.evaluate
    (Family.currentFormula
      (Width.node (Rep.node representative)))
    Future.emptyAssignment
reachableTerminalLabelExact path index
    with Rep.representativeOfIndex path index
... | representative =
  trans
    (cong
      (λ key → Vec.lookup key Fin.zero)
      (sym (Rep.keyMatchesIndex representative)))
    (trans
      (sym
        (cong
          (λ key → Vec.lookup key Fin.zero)
          (Indexed.indexRestrictionNodeExact
            (Rep.node representative))))
      (Indexed.indexedTerminalLabelCorrect
        (Rep.node representative)))

------------------------------------------------------------------------
-- This is a correctness result on the ACTUAL same-root terminal restrictions.
-- A Clay Q1 compiler additionally needs its own formula-rewrite admission,
-- budgeted operational execution and mandatory-success theorem.
------------------------------------------------------------------------
