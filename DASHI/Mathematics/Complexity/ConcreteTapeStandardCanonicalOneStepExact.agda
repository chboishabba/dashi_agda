module DASHI.Mathematics.Complexity.ConcreteTapeStandardCanonicalOneStepExact where

------------------------------------------------------------------------
-- CANONICAL CONCRETE ROW PROJECTION -> EXACT STANDARD ONE STEP
--
-- This file identifies the canonical `ExactlyOneHead` projection with the
-- intrinsic interior projection used by the already-paid one-step weld.  It
-- then proves that the canonical projections of the actual before/after rows
-- are related by one literal `standardNext` step.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleKeyDeterminismExact as Determinism
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardOneStepExact as OneStep
import DASHI.Mathematics.Complexity.ConcreteTapeStandardCanonicalProjectionExact as Canonical

------------------------------------------------------------------------
-- The two proof-directed plain-symbol erasures are definitionally coherent.
------------------------------------------------------------------------

plainSymbols-coherent :
  ∀ {State Symbol : Set} {cells}
    (plain : WF.PlainCells {State} {Symbol} cells) →
  Canonical.plainCellsToSymbols plain ≡ OneStep.plainSymbols plain
plainSymbols-coherent WF.plainNil = refl
plainSymbols-coherent (WF.plainCons rest)
  rewrite plainSymbols-coherent rest = refl

------------------------------------------------------------------------
-- Canonical projection of a literal interior-shaped row.
------------------------------------------------------------------------

canonicalInteriorShape :
  ∀ {machine}
    {prefix suffix}
    {left read right : Local.Symbol machine}
    {q : Local.State machine}
    (prefixPlain : WF.PlainCells prefix)
    (suffixPlain : WF.PlainCells suffix) →
  Canonical.canonicalProjectionCells
      (WF.prependPlain prefixPlain
        (WF.plainBefore
          (WF.headHere (WF.plainCons suffixPlain))))
  ≡
  Standard.standard-configuration
    (left ∷ OneStep.farLeftSymbols prefixPlain)
    q read
    (right ∷ OneStep.plainSymbols suffixPlain)
canonicalInteriorShape WF.plainNil suffixPlain
  rewrite plainSymbols-coherent suffixPlain = refl
canonicalInteriorShape
    (WF.plainCons {symbol = symbol} prefixPlain) suffixPlain
  rewrite canonicalInteriorShape prefixPlain suffixPlain = refl

/-- Any genuine interior witness projects to exactly the existing intrinsic
standard before-configuration. -/
canonicalProjectionOfInterior :
  ∀ {machine row}
    (interior : Character.InteriorHeadConfiguration machine row) →
  Canonical.canonicalProjection (Character.interiorHeadIsUnique interior)
    ≡ OneStep.standardBeforeOfInterior interior
canonicalProjectionOfInterior interior
    with Character.rowShape interior
... | refl =
  canonicalInteriorShape
    (Character.prefixPlain interior)
    (Character.suffixPlain interior)

------------------------------------------------------------------------
-- Direction-specific canonical projections of the concrete after row.
------------------------------------------------------------------------

canonicalAfterLeftShape :
  ∀ {machine}
    {prefix suffix}
    {left right write : Local.Symbol machine}
    {target : Local.State machine}
    (prefixPlain : WF.PlainCells prefix)
    (suffixPlain : WF.PlainCells suffix) →
  Canonical.canonicalProjectionCells
    (WF.prependPlain prefixPlain
      (WF.headHere
        (WF.plainCons (WF.plainCons suffixPlain))))
  ≡
  Standard.standard-configuration
    (OneStep.farLeftSymbols prefixPlain)
    target left
    (write ∷ right ∷ OneStep.plainSymbols suffixPlain)
canonicalAfterLeftShape WF.plainNil suffixPlain
  rewrite plainSymbols-coherent suffixPlain = refl
canonicalAfterLeftShape
    (WF.plainCons {symbol = symbol} prefixPlain) suffixPlain
  rewrite canonicalAfterLeftShape prefixPlain suffixPlain = refl

canonicalAfterStayShape :
  ∀ {machine}
    {prefix suffix}
    {left right write : Local.Symbol machine}
    {target : Local.State machine}
    (prefixPlain : WF.PlainCells prefix)
    (suffixPlain : WF.PlainCells suffix) →
  Canonical.canonicalProjectionCells
    (WF.prependPlain prefixPlain
      (WF.plainBefore
        (WF.headHere (WF.plainCons suffixPlain))))
  ≡
  Standard.standard-configuration
    (left ∷ OneStep.farLeftSymbols prefixPlain)
    target write
    (right ∷ OneStep.plainSymbols suffixPlain)
canonicalAfterStayShape = canonicalInteriorShape

canonicalAfterRightShape :
  ∀ {machine}
    {prefix suffix}
    {left right write : Local.Symbol machine}
    {target : Local.State machine}
    (prefixPlain : WF.PlainCells prefix)
    (suffixPlain : WF.PlainCells suffix) →
  Canonical.canonicalProjectionCells
    (WF.prependPlain prefixPlain
      (WF.plainBefore
        (WF.plainBefore
          (WF.headHere suffixPlain))))
  ≡
  Standard.standard-configuration
    (write ∷ left ∷ OneStep.farLeftSymbols prefixPlain)
    target right
    (OneStep.plainSymbols suffixPlain)
canonicalAfterRightShape WF.plainNil suffixPlain
  rewrite plainSymbols-coherent suffixPlain = refl
canonicalAfterRightShape
    (WF.plainCons {symbol = symbol} prefixPlain) suffixPlain
  rewrite canonicalAfterRightShape prefixPlain suffixPlain = refl

/-- Canonical projection of the actual relational after-row is exactly the
existing directional `standardAfterOfRule`. -/
canonicalProjectionAfterWellFormed :
  ∀ {machine before after}
    (wellFormed : WF.WellFormedMachineStep machine before after) →
  Canonical.canonicalProjection (WF.afterExactlyOneHead wellFormed)
    ≡ OneStep.standardAfterOfRule
        (Character.wellFormedStepBeforeInterior wellFormed)
        (Local.rule (WF.step wellFormed))
canonicalProjectionAfterWellFormed wellFormed
    with Local.ruleIsConfigured (WF.step wellFormed)
... | Local.realizes-left
      {q = q} {q' = target} {a = read} {b = write}
      {leftSymbol = left} {rightSymbol = right}
    with Local.afterShape
      (WF.occurrence (WF.wellFormedOccurrence wellFormed))
...   | refl =
  canonicalAfterLeftShape
    (WF.prefixPlain (WF.wellFormedOccurrence wellFormed))
    (WF.suffixPlain (WF.wellFormedOccurrence wellFormed))
... | Local.realizes-stay
      {q = q} {q' = target} {a = read} {b = write}
      {leftSymbol = left} {rightSymbol = right}
    with Local.afterShape
      (WF.occurrence (WF.wellFormedOccurrence wellFormed))
...   | refl =
  canonicalAfterStayShape
    (WF.prefixPlain (WF.wellFormedOccurrence wellFormed))
    (WF.suffixPlain (WF.wellFormedOccurrence wellFormed))
... | Local.realizes-right
      {q = q} {q' = target} {a = read} {b = write}
      {leftSymbol = left} {rightSymbol = right}
    with Local.afterShape
      (WF.occurrence (WF.wellFormedOccurrence wellFormed))
...   | refl =
  canonicalAfterRightShape
    (WF.prefixPlain (WF.wellFormedOccurrence wellFormed))
    (WF.suffixPlain (WF.wellFormedOccurrence wellFormed))

/-- Canonical projection of the actual before-row agrees with the intrinsic
one-step owner. -/
canonicalProjectionBeforeWellFormed :
  ∀ {machine before after}
    (wellFormed : WF.WellFormedMachineStep machine before after) →
  Canonical.canonicalProjection (WF.beforeExactlyOneHead wellFormed)
    ≡ OneStep.standardBeforeOfInterior
        (Character.wellFormedStepBeforeInterior wellFormed)
canonicalProjectionBeforeWellFormed wellFormed =
  trans
    (Canonical.canonicalProjectionCells-unique
      (WF.beforeExactlyOneHead wellFormed)
      (Character.interiorHeadIsUnique
        (Character.wellFormedStepBeforeInterior wellFormed)))
    (canonicalProjectionOfInterior
      (Character.wellFormedStepBeforeInterior wellFormed))

------------------------------------------------------------------------
-- Exact canonical one-step theorem.
------------------------------------------------------------------------

canonicalWellFormedStepProjectsToStandard :
  ∀ {machine before after}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (wellFormed : WF.WellFormedMachineStep machine before after) →
  Standard.standardNext
      (Standard.standardControlOfConcrete machine)
      (Canonical.canonicalProjection (WF.beforeExactlyOneHead wellFormed))
    ≡ just
      (Canonical.canonicalProjection (WF.afterExactlyOneHead wellFormed))
canonicalWellFormedStepProjectsToStandard deterministic wellFormed =
  trans
    (cong
      (Standard.standardNext
        (Standard.standardControlOfConcrete _))
      (canonicalProjectionBeforeWellFormed wellFormed))
    (trans
      (OneStep.wellFormedConcreteStepProjectsToStandardStep
        deterministic wellFormed)
      (cong just (sym (canonicalProjectionAfterWellFormed wellFormed))))

/-- Proof witnesses for uniqueness do not affect the observable one-step
statement, so callers may use any ExactlyOneHead proofs for the same rows. -/
canonicalWellFormedStepProjectsToStandardAnyProof :
  ∀ {machine before after}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (wellFormed : WF.WellFormedMachineStep machine before after)
    (beforeUnique : WF.ExactlyOneHead (Local.cells before))
    (afterUnique : WF.ExactlyOneHead (Local.cells after)) →
  Standard.standardNext
      (Standard.standardControlOfConcrete machine)
      (Canonical.canonicalProjection beforeUnique)
    ≡ just (Canonical.canonicalProjection afterUnique)
canonicalWellFormedStepProjectsToStandardAnyProof
    deterministic wellFormed beforeUnique afterUnique
  rewrite Canonical.canonicalProjectionCells-unique
      beforeUnique (WF.beforeExactlyOneHead wellFormed)
        | Canonical.canonicalProjectionCells-unique
      afterUnique (WF.afterExactlyOneHead wellFormed) =
  canonicalWellFormedStepProjectsToStandard deterministic wellFormed

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID HERE (subject to exact-head Agda certification):
-- * canonical ExactlyOneHead projection = intrinsic interior projection;
-- * canonical actual after-row = the directional standard after-state;
-- * every deterministic WellFormedMachineStep becomes one exact standardNext;
-- * theorem is independent of the chosen uniqueness proofs.
--
-- NEXT:
-- * induction over the existing WellFormedTapeRun;
-- * exact run-length/acceptance preservation;
-- * polynomial clock translation and infrastructure freeze.
------------------------------------------------------------------------
