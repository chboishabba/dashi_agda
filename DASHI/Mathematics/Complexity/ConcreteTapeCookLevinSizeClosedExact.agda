module DASHI.Mathematics.Complexity.ConcreteTapeCookLevinSizeClosedExact where

------------------------------------------------------------------------
-- CLOSED COOK--LEVIN GRID / CLAUSE COUNTS
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _^_)
open import Data.Nat using (_∸_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.ConcreteTapeSelectedRuleWindowCNFExact as Selected
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinSizeExact as Size
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Generic list arithmetic
------------------------------------------------------------------------

appendLength :
  ∀ {A : Set} (xs ys : List A) →
  Size.listLength (Placed.append xs ys)
  ≡ Size.listLength xs + Size.listLength ys
appendLength [] ys = refl
appendLength (x ∷ xs) ys
  rewrite appendLength xs ys =
  refl

mapShiftWindowStartsLength :
  ∀ {cols}
    (starts : List (Transition.SomeWindowStart cols)) →
  Size.listLength (Transition.mapShiftWindowStarts starts)
  ≡ Size.listLength starts
mapShiftWindowStartsLength [] = refl
mapShiftWindowStartsLength (x ∷ xs)
  rewrite mapShiftWindowStartsLength xs =
  refl

mapShiftSlotsLength :
  ∀ {steps}
    (slots : List (Transition.SomeSlot steps)) →
  Size.listLength (Transition.mapShiftSlots slots)
  ≡ Size.listLength slots
mapShiftSlotsLength [] = refl
mapShiftSlotsLength (x ∷ xs)
  rewrite mapShiftSlotsLength xs =
  refl

------------------------------------------------------------------------
-- Exact grid cardinalities
------------------------------------------------------------------------

windowStartCount_exact :
  (cols : Nat) →
  Size.listLength (Transition.allWindowStarts cols)
  ≡ cols ∸ 2
windowStartCount_exact zero = refl
windowStartCount_exact (suc zero) = refl
windowStartCount_exact (suc (suc zero)) = refl
windowStartCount_exact (suc (suc (suc rest)))
  rewrite mapShiftWindowStartsLength
      (Transition.allWindowStarts (suc (suc rest)))
        | windowStartCount_exact (suc (suc rest)) =
  refl

timeSlotCount_exact :
  (steps : Nat) →
  Size.listLength (Transition.allSlots steps)
  ≡ steps
timeSlotCount_exact =
  Size.timeSlotCount

predicatesForOneTime_count :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot :
      Global.Slot
        timeIndex steps)
    (starts : List (Transition.SomeWindowStart cols)) →
  Size.listLength
    (Transition.predicatesForOneTime
      stateCoverage symbolCoverage nonempty timeSlot starts)
  ≡ Size.listLength starts
predicatesForOneTime_count
    stateCoverage symbolCoverage nonempty timeSlot [] =
  refl
predicatesForOneTime_count
    stateCoverage symbolCoverage nonempty timeSlot
    (x ∷ xs)
  rewrite predicatesForOneTime_count
      stateCoverage symbolCoverage nonempty timeSlot xs =
  refl

predicatesForAllTimes_count :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (times : List (Transition.SomeSlot steps)) →
  Size.listLength
    (Transition.predicatesForAllTimes
      stateCoverage symbolCoverage nonempty times)
  ≡ Size.listLength times *
      Size.listLength (Transition.allWindowStarts cols)
predicatesForAllTimes_count
    stateCoverage symbolCoverage nonempty [] =
  refl
predicatesForAllTimes_count
    {cols = cols}
    stateCoverage symbolCoverage nonempty
    (Transition.some-slot timeIndex timeSlot ∷ rest)
  rewrite appendLength
      (Transition.predicatesForOneTime
        stateCoverage symbolCoverage nonempty timeSlot
        (Transition.allWindowStarts cols))
      (Transition.predicatesForAllTimes
        stateCoverage symbolCoverage nonempty rest)
        | predicatesForOneTime_count
            stateCoverage symbolCoverage nonempty timeSlot
            (Transition.allWindowStarts cols)
        | predicatesForAllTimes_count
            stateCoverage symbolCoverage nonempty rest =
  refl

allGlobalTransitionPredicates_count :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat) →
  Size.listLength
    (Transition.allGlobalTransitionPredicates
      stateCoverage symbolCoverage nonempty steps cols)
  ≡ steps * (cols ∸ 2)
allGlobalTransitionPredicates_count
    stateCoverage symbolCoverage nonempty steps cols
  rewrite predicatesForAllTimes_count
      stateCoverage symbolCoverage nonempty
      (Transition.allSlots steps)
        | timeSlotCount_exact steps
        | windowStartCount_exact cols =
  refl

------------------------------------------------------------------------
-- Clause replication bounds
------------------------------------------------------------------------

renameCNF_length :
  ∀ {local global}
    (rename : Fin.Fin local → Fin.Fin global)
    (formula : CNF.CNF local) →
  Size.listLength
    (Rename.renameCNF
      rename formula)
  ≡ Size.listLength formula
renameCNF rename [] = refl
renameCNF rename (c ∷ cs)
  rewrite renameCNF_length rename cs =
  refl

compilePlaced_clause_bound :
  ∀ {local global}
    (placed : Placed.PlacedPredicate local global) →
  Σ Nat (λ slack →
    Size.listLength (Placed.compilePlaced placed) + slack
    ≡ 2 ^ local)
compilePlaced_clause_bound placed
  with Size.truthTableCNF_clause_bound (Placed.predicate placed)
... | slack , h
  rewrite renameCNF_length
    (Placed.rename placed)
    (CNF.truthTableCNF (Placed.predicate placed)) =
  slack , h

compilePlacedAll_clause_bound :
  ∀ {local global}
    (placed : List (Placed.PlacedPredicate local global)) →
  Σ Nat (λ slack →
    Size.listLength (Placed.compilePlacedAll placed) + slack
    ≡ Size.listLength placed * (2 ^ local))
compilePlacedAll_clause_bound [] =
  zero , refl
compilePlacedAll_clause_bound
    {local = local} (p ∷ ps)
    with compilePlaced_clause_bound p
       | compilePlacedAll_clause_bound ps
... | slackP , hp | slackRest , hrest =
  slackP + slackRest , proof
  where
    proof :
      Size.listLength (Placed.compilePlacedAll (p ∷ ps))
        + (slackP + slackRest)
      ≡
      Size.listLength (p ∷ ps) * (2 ^ local)
    proof
      rewrite appendLength
        (Placed.compilePlaced p)
        (Placed.compilePlacedAll ps)
            | hp | hrest =
      +-assoc-rearrange
      where
        +-assoc-rearrange :
          (2 ^ local) + (Size.listLength ps * (2 ^ local))
          ≡ suc (Size.listLength ps) * (2 ^ local)
        +-assoc-rearrange = refl

globalTransitionClause_bound :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat) →
  Σ Nat (λ slack →
    Size.listLength
      (Transition.globalTransitionCNF
        stateCoverage symbolCoverage nonempty steps cols)
      + slack
    ≡
      (steps * (cols ∸ 2))
      * (2 ^ Selected.TransitionLocalWidth machine))
globalTransitionClause_bound
    stateCoverage symbolCoverage nonempty steps cols
    with compilePlacedAll_clause_bound
      (Transition.allGlobalTransitionPredicates
        stateCoverage symbolCoverage nonempty steps cols)
... | slack , h
  rewrite allGlobalTransitionPredicates_count
    stateCoverage symbolCoverage nonempty steps cols =
  slack , h

------------------------------------------------------------------------
-- Endpoint exact/bounded counts
------------------------------------------------------------------------

unitClausesForTarget_count :
  ∀ {local global}
    (rename : Fin.Fin local → Fin.Fin global)
    (target : CNF.Bits local) →
  Size.listLength (Endpoint.unitClausesForTarget rename target)
  ≡ local
unitClausesForTarget_count rename CNF.[]ᵇ = refl
unitClausesForTarget_count rename (b CNF.∷ᵇ bs)
  rewrite unitClausesForTarget_count
    (λ i → rename (Fin.suc i)) bs =
  refl

initialEndpointClauseCount :
  ∀ {machine steps cols}
    (target : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  Size.listLength (Endpoint.initialEndpointCNF target)
  ≡ Decode.RowBitsWidth machine cols
initialEndpointClauseCount target =
  unitClausesForTarget_count Endpoint.initialRowExtendedRename target

mapFinSuc_count :
  ∀ {n} (xs : List (Fin.Fin n)) →
  Size.listLength (Endpoint.mapFinSuc xs)
  ≡ Size.listLength xs
mapFinSuc_count [] = refl
mapFinSuc_count (x ∷ xs)
  rewrite mapFinSuc_count xs =
  refl

finList_count :
  (n : Nat) →
  Size.listLength (Endpoint.finList n) ≡ n
finList_count zero = refl
finList_count (suc n)
  rewrite mapFinSuc_count (Endpoint.finList n)
        | finList_count n =
  refl


acceptancePredicate_count :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (indices : List (Fin.Fin cols)) →
  Size.listLength
    (Endpoint.acceptanceImplicationPredicatesFin
      stateCoverage symbolCoverage indices)
  ≡ Size.listLength indices
acceptancePredicate_count stateCoverage symbolCoverage [] =
  refl
acceptancePredicate_count stateCoverage symbolCoverage (i ∷ is)
  rewrite acceptancePredicate_count
    stateCoverage symbolCoverage is =
  refl

acceptanceImplicationClause_bound :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  Σ Nat (λ slack →
    Size.listLength
      (Placed.compilePlacedAll
        (Endpoint.acceptanceImplicationPredicatesFin
          stateCoverage symbolCoverage
          (Endpoint.finList cols)))
      + slack
    ≡ cols * (2 ^ Endpoint.AcceptanceLocalWidth machine))
acceptanceImplicationClause_bound
    {cols = cols} stateCoverage symbolCoverage
    with compilePlacedAll_clause_bound
      (Endpoint.acceptanceImplicationPredicatesFin
        stateCoverage symbolCoverage
        (Endpoint.finList cols))
... | slack , h
  rewrite acceptancePredicate_count
      stateCoverage symbolCoverage
      (Endpoint.finList cols)
        | finList_count cols =
  slack , h

acceptingEndpointClause_bound :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  Σ Nat (λ slack →
    Size.listLength
      (Endpoint.acceptingEndpointCNF
        stateCoverage symbolCoverage)
      + slack
    ≡ suc (cols * (2 ^ Endpoint.AcceptanceLocalWidth machine)))
acceptingEndpointClause_bound
    stateCoverage symbolCoverage
    with acceptanceImplicationClause_bound
      stateCoverage symbolCoverage
... | slack , h =
  slack , cong suc h

record ConcreteCookLevinClosedSizeReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    exactWindowStartCountPaid : Bool
    exactTransitionGridCountPaid : Bool
    transitionClauseProductBoundPaid : Bool
    initialClauseCountPaid : Bool
    acceptanceClauseLinearTimesConstantBoundPaid : Bool
    totalFormulaPolynomialClosurePaid : Bool

closedSizeReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  ConcreteCookLevinClosedSizeReceipt machine
closedSizeReceipt machine = record
  { exactWindowStartCountPaid = true
  ; exactTransitionGridCountPaid = true
  ; transitionClauseProductBoundPaid = true
  ; initialClauseCountPaid = true
  ; acceptanceClauseLinearTimesConstantBoundPaid = true
  ; totalFormulaPolynomialClosurePaid = false
  }
