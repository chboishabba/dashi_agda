module DASHI.Mathematics.Complexity.PNotEqualsNPSATSelfReductionTerminalSizeNoGoExact where

------------------------------------------------------------------------
-- SAT SELF-REDUCTION CAN REACH ZERO VARIABLES WITHOUT SHRINKING THE TREE
--
-- Companion:
--   PNotEqualsNPSATSelfReductionSizeNoGoExact
--
-- One restriction lowers the free-variable index by one while preserving the
-- syntax-node count exactly.  Here we iterate that operation along a complete
-- assignment:
--
--   phi : BooleanFormula n
--   assignment : Vec Bool n
--
-- producing:
--
--   fullyRestrict assignment phi : BooleanFormula 0
--
-- with EXACTLY the same syntax-node count as phi.
--
-- So "strictly smaller number of free variables" is not the size descent the
-- resource-bounded self-diagonal construction needs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSATSelfReductionSizeNoGoExact as Size

------------------------------------------------------------------------
-- Restrict all head variables according to a complete assignment.
------------------------------------------------------------------------

fullyRestrict :
  ∀ {variables : Nat} →
  Vec Bool variables →
  SAT.BooleanFormula variables →
  SAT.BooleanFormula zero
fullyRestrict {zero} [] formula =
  formula
fullyRestrict {suc variables} (bit ∷ bits) formula =
  fullyRestrict
    bits
    (SAT.restrictHead bit formula)

------------------------------------------------------------------------
-- Full variable elimination preserves syntax size exactly.
------------------------------------------------------------------------

fullyRestrictPreservesNodeCount :
  ∀ {variables : Nat}
    (bits : Vec Bool variables)
    (formula : SAT.BooleanFormula variables) →
  Size.formulaNodeCount
    (fullyRestrict bits formula)
  ≡
  Size.formulaNodeCount formula
fullyRestrictPreservesNodeCount {zero} [] formula =
  refl
fullyRestrictPreservesNodeCount
    {suc variables}
    (bit ∷ bits)
    formula =
  transitive
    (fullyRestrictPreservesNodeCount
      bits
      (SAT.restrictHead bit formula))
    (Size.restrictHeadPreservesNodeCount
      bit
      formula)
  where
    transitive :
      ∀ {A : Set}
        {left middle right : A} →
      left ≡ middle →
      middle ≡ right →
      left ≡ right
    transitive refl refl =
      refl

------------------------------------------------------------------------
-- Research consequence.
--
-- Standard SAT decision-to-search self-reduction can descend:
--
--   n free variables -> 0 free variables
--
-- while retaining:
--
--   N syntax nodes -> N syntax nodes.
--
-- Therefore a well-founded recursion on variable count does not become a
-- sub-N recursion on the ordinary encoded input size seen by a hypothetical
-- polynomial-time SAT decider.
------------------------------------------------------------------------
