module DASHI.Cognition.PNF.SensibLawFiniteLegalCutGuardExact where

------------------------------------------------------------------------
-- REACHABILITY-GUARDED FINITE CUT SEARCH
--
-- A cut explains which enabled rules are essential to a route that presently
-- exists. If the target is already unreachable, the empty disabled-rule set is
-- vacuously blocking but is not a useful legal cut. Such cases belong to the
-- obstruction/transformation search instead.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search

searchReachableMinimalCut :
  Nat → Algebra.LegalGraph → Algebra.FactSet → Algebra.LegalProposition →
  Search.SearchResult (List String)
searchReachableMinimalCut depth graph facts goal with
  Search.reachable depth graph facts goal
... | false = Search.notFound
... | true = Search.searchMinimalCut depth graph facts goal

------------------------------------------------------------------------
-- Firewall.
------------------------------------------------------------------------

data AlreadyUnreachableGoalHasMeaningfulEmptyCut : Set where

unreachableGoalRoutesToRepairSearch :
  AlreadyUnreachableGoalHasMeaningfulEmptyCut → ⊥
unreachableGoalRoutesToRepairSearch ()
