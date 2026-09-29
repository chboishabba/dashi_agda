module DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedWorkGateFailureExact where

------------------------------------------------------------------------
-- EXACT OUTPUT AND FAILURE FIREWALL FOR THE ROOTED WORK GATE
--
-- This is deliberately below DirectDPChargedConstructionRun:
-- the source-level ledger is not a machine-instruction execution receipt.
--
-- On success the output is definitionally the ACTUAL canonical layer keys,
-- not any fabricated key list. On failure the strict inequality is impossible.
-- In particular a budget bounded by the computed declared work forces
-- nothing, including at the exact candidate-quoted state.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_; _<_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable.Core using (yes; no)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; sym)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact as Merge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedWorkGateExact as Work

------------------------------------------------------------------------
-- Same-object success: the gate cannot return a different semantic quotient.
------------------------------------------------------------------------

rootedWorkGateOutputExact :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (path : Root.DescentPath root remaining)
    (budget : Nat)
    {result :
      Σ (List (Merge.SemanticKey remaining))
        (λ keys →
          Work.rootedDeclaredOperationalWork path < budget)} →
  Work.budgetedRootedKeys path budget ≡ just result →
  proj₁ result ≡ Root.rootedMergedSemanticKeys path
rootedWorkGateOutputExact path budget {result}
    successful
    with NatP._<?_
      (Work.rootedDeclaredOperationalWork path)
      budget
... | yes fits
    with successful
...   | refl = refl
... | no doesNotFit
    with successful
...   | ()

------------------------------------------------------------------------
-- Exhausted strict budgets force explicit failure. This is an algorithmic
-- limitation of THIS exhaustive constructor, not a SAT lower bound.
------------------------------------------------------------------------

rootedWorkGateFailsIfWorkExhaustsBudget :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (path : Root.DescentPath root remaining)
    (budget : Nat) →
  budget ≤ Work.rootedDeclaredOperationalWork path →
  Work.budgetedRootedKeys path budget ≡ nothing
rootedWorkGateFailsIfWorkExhaustsBudget
    path budget exhausted
    with NatP._<?_
      (Work.rootedDeclaredOperationalWork path)
      budget
... | yes fits =
  ⊥-elim
    (NatP.<⇒≱ fits exhausted)
... | no doesNotFit =
  refl

------------------------------------------------------------------------
-- Successful construction excludes any declared-work lower bound on its
-- budget. It does not imply execution completeness, Q1 local admission, or
-- the separate direct-DP charged recurrence.
------------------------------------------------------------------------

rootedWorkGateSuccessExcludesExhaustion :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (path : Root.DescentPath root remaining)
    (budget : Nat)
    {result :
      Σ (List (Merge.SemanticKey remaining))
        (λ keys →
          Work.rootedDeclaredOperationalWork path < budget)} →
  Work.budgetedRootedKeys path budget ≡ just result →
  budget ≤ Work.rootedDeclaredOperationalWork path →
  ⊥
rootedWorkGateSuccessExcludesExhaustion
    path budget successful exhausted =
  NatP.<⇒≱
    (proj₂ _)
    exhausted

------------------------------------------------------------------------
-- BOUNDARY:
-- A successful source-level gate is NOT an inhabitant of
-- DirectDPChargedConstructionRun. That record additionally requires:
--   * one actual finite TransitionTableCandidate;
--   * complete arity/terminal admission;
--   * a typed step-by-step machine execution yielding that SAME candidate;
--   * the independent strict evaluation+execution+payload inequality.
------------------------------------------------------------------------
