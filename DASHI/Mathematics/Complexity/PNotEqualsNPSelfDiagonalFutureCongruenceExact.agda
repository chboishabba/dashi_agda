module DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalFutureCongruenceExact where

------------------------------------------------------------------------
-- SELF-DIAGONAL SHANNON RESTRICTION AS FUTURE OBSERVATIONAL REFINEMENT
--
-- Reuse:
--   DASHI.Core.FutureObservationalRefinement
--
-- State  = reachable restriction nodes of one fixed root.
-- Action = false | true Shannon restriction.
--
-- Actions are admissible only at nonterminal nodes. Terminal observation is
-- structural evaluation of a zero-variable formula; nonterminal nodes expose
-- only the fact that they are not terminal.
--
-- Thus no SAT oracle is used by the observer.
--
-- IMPORTANT DEPTH BOUNDARY:
--
-- The existing Q1 quotient may merge nodes with different remaining arities.
-- Such a merge need not preserve the terminal/nonterminal observation under a
-- common trace. Therefore the honest refinement theorem is same quotient
-- state + same remaining arity.
--
-- Within each restriction layer, every Q1 merge factors into the canonical
-- future-equivalence relation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationalRefinement as Future
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient

------------------------------------------------------------------------
-- Terminal/nonterminal observation.
------------------------------------------------------------------------

data RestrictionObservation : Set where
  nonterminal : RestrictionObservation
  terminal : Bool → RestrictionObservation

emptyAssignment : SAT.Assignment zero
emptyAssignment ()

restrictionObservation :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Family.RestrictionNode root →
  RestrictionObservation
restrictionObservation node
    with Family.currentVariables node
... | zero =
  terminal
    (SAT.evaluate
      (Family.currentFormula node)
      emptyAssignment)
... | suc remaining =
  nonterminal

------------------------------------------------------------------------
-- Proof that one Shannon action is admissible.
------------------------------------------------------------------------

NonTerminal :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Family.RestrictionNode root →
  Set
NonTerminal node =
  Σ Nat λ remaining →
    Family.currentVariables node ≡ suc remaining

restrictedNode :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (node : Family.RestrictionNode root)
    (bit : Bool) →
  NonTerminal node →
  Family.RestrictionNode root
restrictedNode node bit (remaining , arity)
    with arity
... | refl
    with bit
... | false =
  Family.falseChild
    (Family.derivation node)
... | true =
  Family.trueChild
    (Family.derivation node)

------------------------------------------------------------------------
-- Dependent action system.
------------------------------------------------------------------------

restrictionActionSystem :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  Dependency.DependentActionSystem
    (Family.RestrictionNode root)
    Bool
restrictionActionSystem root = record
  { Dependency.Precondition =
      λ node bit →
        NonTerminal node
  ; Dependency.Postcondition =
      λ before bit after →
        Σ (NonTerminal before) λ admissible →
          after ≡ restrictedNode before bit admissible
  ; Dependency.actionLabel =
      λ bit →
        actionLabel bit
  }
  where
    actionLabel : Bool → String
    actionLabel false = "restrict-false"
    actionLabel true = "restrict-true"

canonicalAdmissibleRestriction :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (node : Family.RestrictionNode root)
    (bit : Bool)
    (admissible : NonTerminal node) →
  Dependency.AdmissibleAction
    (restrictionActionSystem root)
    node
    bit
canonicalAdmissibleRestriction node bit admissible = record
  { Dependency.precondition = admissible
  ; Dependency.after =
      restrictedNode node bit admissible
  ; Dependency.postcondition =
      admissible , refl
  ; Dependency.dependencyReceipt =
      "literal Shannon restriction"
  }

------------------------------------------------------------------------
-- Terminal observation equals satisfiability at arity zero.
------------------------------------------------------------------------

terminalTrueGivesSatisfying :
  (formula : SAT.BooleanFormula zero) →
  SAT.evaluate formula emptyAssignment ≡ true →
  SAT.Satisfying formula
terminalTrueGivesSatisfying formula evaluatesTrue =
  SAT.satisfying
    emptyAssignment
    evaluatesTrue

satisfyingTerminalGivesTrue :
  (formula : SAT.BooleanFormula zero) →
  SAT.Satisfying formula →
  SAT.evaluate formula emptyAssignment ≡ true
satisfyingTerminalGivesTrue formula witness =
  trans
    (SAT.evaluateExtensional
      formula
      (λ ()))
    (SAT.evaluatesTrue witness)

zeroVariableEquisatisfiableImpliesEqualEvaluation :
  (left right : SAT.BooleanFormula zero) →
  Quotient.SatisfiabilityEquivalent left right →
  SAT.evaluate left emptyAssignment
  ≡
  SAT.evaluate right emptyAssignment
zeroVariableEquisatisfiableImpliesEqualEvaluation
    left
    right
    equivalent
    with SAT.evaluate left emptyAssignment
       | SAT.evaluate right emptyAssignment
... | false | false =
  refl
... | true | true =
  refl
... | true | false =
  falseNotTrue
    (satisfyingTerminalGivesTrue
      right
      (proj₁ equivalent
        (terminalTrueGivesSatisfying left refl)))
  where
    falseNotTrue : false ≡ true → ⊥
    falseNotTrue ()
... | false | true =
  falseNotTrue
    (satisfyingTerminalGivesTrue
      left
      (proj₂ equivalent
        (terminalTrueGivesSatisfying right refl)))
  where
    falseNotTrue : false ≡ true → ⊥
    falseNotTrue ()

------------------------------------------------------------------------
-- Same-layer Q1 merge relation.
------------------------------------------------------------------------

SameLayerQuotientMerge :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Quotient.RestrictionSemanticQuotient root →
  Family.RestrictionNode root →
  Family.RestrictionNode root →
  Set
SameLayerQuotientMerge quotient left right =
  (Family.currentVariables left
    ≡ Family.currentVariables right)
  ×
  (Quotient.classify quotient
      (Family.derivation left)
    ≡
    Quotient.classify quotient
      (Family.derivation right))

------------------------------------------------------------------------
-- Same-layer merge refines the structural terminal observer.
------------------------------------------------------------------------

sameLayerMergeRefinesCurrent :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {left right : Family.RestrictionNode root} →
  SameLayerQuotientMerge quotient left right →
  Future.CurrentEquivalent
    restrictionObservation
    left
    right
sameLayerMergeRefinesCurrent quotient
    {left} {right}
    (sameArity , sameState)
    with Family.currentVariables left
       | Family.currentVariables right
       | sameArity
... | zero | .zero | refl =
  cong terminal
    (zeroVariableEquisatisfiableImpliesEqualEvaluation
      (Family.currentFormula left)
      (Family.currentFormula right)
      (Quotient.sameStateImpliesSatisfiabilityEquivalent
        quotient
        (Family.derivation left)
        (Family.derivation right)
        sameState))
... | suc leftRemaining | .(suc leftRemaining) | refl =
  refl

------------------------------------------------------------------------
-- One common action preserves same-layer quotient merging.
------------------------------------------------------------------------

sameLayerMergeAfterCommonRestriction :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {left right : Family.RestrictionNode root}
    {bit : Bool} →
  SameLayerQuotientMerge quotient left right →
  (leftAdmissible : NonTerminal left) →
  (rightAdmissible : NonTerminal right) →
  SameLayerQuotientMerge
    quotient
    (restrictedNode left bit leftAdmissible)
    (restrictedNode right bit rightAdmissible)
sameLayerMergeAfterCommonRestriction
    quotient
    {left} {right} {bit}
    (sameArity , sameState)
    (leftRemaining , leftArity)
    (rightRemaining , rightArity)
    with leftArity | rightArity | sameArity | bit
... | refl | refl | refl | false =
  refl
  ,
  trans
    (Quotient.falseStepCompatible
      quotient
      (Family.derivation left))
    (trans
      (cong
        (λ state → Quotient.step quotient state false)
        sameState)
      (sym
        (Quotient.falseStepCompatible
          quotient
          (Family.derivation right))))
... | refl | refl | refl | true =
  refl
  ,
  trans
    (Quotient.trueStepCompatible
      quotient
      (Family.derivation left))
    (trans
      (cong
        (λ state → Quotient.step quotient state true)
        sameState)
      (sym
        (Quotient.trueStepCompatible
          quotient
          (Family.derivation right))))

------------------------------------------------------------------------
-- Common traces preserve the relation.
------------------------------------------------------------------------

sameLayerMergeClosedUnderCommonTrace :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {actions}
    {left right leftAfter rightAfter :
      Family.RestrictionNode root} →
  SameLayerQuotientMerge quotient left right →
  Reachability.Executes
    (restrictionActionSystem root)
    actions
    left
    leftAfter →
  Reachability.Executes
    (restrictionActionSystem root)
    actions
    right
    rightAfter →
  SameLayerQuotientMerge quotient leftAfter rightAfter
sameLayerMergeClosedUnderCommonTrace
    quotient
    related
    Reachability.executesNil
    Reachability.executesNil =
  related
sameLayerMergeClosedUnderCommonTrace
    quotient
    related
    (Reachability.executesCons leftAction leftRest)
    (Reachability.executesCons rightAction rightRest) =
  sameLayerMergeClosedUnderCommonTrace
    quotient
    nextRelated
    leftRest
    rightRest
  where
    leftProof :
      NonTerminal _
    leftProof =
      Dependency.precondition leftAction

    rightProof :
      NonTerminal _
    rightProof =
      Dependency.precondition rightAction

    leftAfterExact :
      Dependency.after leftAction
      ≡
      restrictedNode _ _ leftProof
    leftAfterExact =
      proj₂
        (Dependency.postcondition leftAction)

    rightAfterExact :
      Dependency.after rightAction
      ≡
      restrictedNode _ _ rightProof
    rightAfterExact =
      proj₂
        (Dependency.postcondition rightAction)

    restrictedRelated :
      SameLayerQuotientMerge
        quotient
        (restrictedNode _ _ leftProof)
        (restrictedNode _ _ rightProof)
    restrictedRelated =
      sameLayerMergeAfterCommonRestriction
        quotient
        related
        leftProof
        rightProof

    nextRelated :
      SameLayerQuotientMerge
        quotient
        (Dependency.after leftAction)
        (Dependency.after rightAction)
    nextRelated
      rewrite leftAfterExact | rightAfterExact =
      restrictedRelated

------------------------------------------------------------------------
-- Main reuse theorem.
------------------------------------------------------------------------

sameLayerQuotientMergeIsDynamicallyCongruent :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root) →
  Future.DynamicallyCongruentRefinement
    (restrictionActionSystem root)
    restrictionObservation
    (SameLayerQuotientMerge quotient)
sameLayerQuotientMergeIsDynamicallyCongruent quotient =
  Future.dynamicallyCongruentRefinement
    (sameLayerMergeRefinesCurrent quotient)
    (sameLayerMergeClosedUnderCommonTrace quotient)

sameLayerQuotientMergeContainedInFutureEquivalent :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {left right : Family.RestrictionNode root} →
  SameLayerQuotientMerge quotient left right →
  Future.FutureEquivalent
    (restrictionActionSystem root)
    restrictionObservation
    left
    right
sameLayerQuotientMergeContainedInFutureEquivalent quotient =
  Future.anyCongruentRefinementIsContainedInFutureEquivalent
    (sameLayerQuotientMergeIsDynamicallyCongruent quotient)

------------------------------------------------------------------------
-- Canonical coarsest dynamically safe refinement for Shannon restrictions.
------------------------------------------------------------------------

canonicalRestrictionFutureRefinement :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  Future.MaximalSafeRefinement
    (restrictionActionSystem root)
    restrictionObservation
canonicalRestrictionFutureRefinement root =
  Future.canonicalMaximalSafeRefinement
    (restrictionActionSystem root)
    restrictionObservation

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Future equivalence is now instantiated on the actual root-scoped Shannon
-- restriction system with a non-oracular terminal observer.
--
-- Every same-depth merge made by an honest Q1 semantic quotient is contained
-- in this canonical future relation.
--
-- Hence a surviving constructor must cheaply build a small transition system
-- whose within-layer state identifications are justified by future behaviour.
-- Generic formulas may still have exponentially many future classes; the only
-- remaining positive opportunity is a SPECIAL self-instantiation invariant
-- proving unusually strong future-equivalence collapse.
------------------------------------------------------------------------
