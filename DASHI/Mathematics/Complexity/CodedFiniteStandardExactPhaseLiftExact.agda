module DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact where

------------------------------------------------------------------------
-- EXACT FINITE-CONTROL PHASE LIFT
--
-- For one fixed diagonal target the candidate budget T is one fixed natural.
-- Lift source control to (sourceState, elapsedPhase), elapsedPhase : Fin (T+1).
-- Every source rule is copied at each k<T and advances k -> k+1.  No copied
-- rule exists at phase T.  Thus the exact-T boundary is quiescent by syntax.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Fin.Base as Fin
open import Data.Fin.Properties using (remQuot-combine)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode
import DASHI.Mathematics.Complexity.CodedFiniteStandardSingletonLinkExact as Singleton
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleKeyDeterminismExact as Determinism
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

------------------------------------------------------------------------
-- Phase arithmetic.
------------------------------------------------------------------------

raisePhase : ∀ {n : Nat} → Fin.Fin n → Fin.Fin (suc n)
raisePhase {zero} ()
raisePhase {suc n} Fin.zero = Fin.zero
raisePhase {suc n} (Fin.suc k) = Fin.suc (raisePhase k)

lastPhase : (n : Nat) → Fin.Fin (suc n)
lastPhase zero = Fin.zero
lastPhase (suc n) = Fin.suc (lastPhase n)

finSucInjective :
  ∀ {n : Nat} {x y : Fin.Fin n} →
  Fin.suc x ≡ Fin.suc y → x ≡ y
finSucInjective refl = refl

raisePhaseInjective :
  ∀ {n : Nat} {x y : Fin.Fin n} →
  raisePhase x ≡ raisePhase y → x ≡ y
raisePhaseInjective {zero} {x = ()}
raisePhaseInjective {suc n} {Fin.zero} {Fin.zero} equality = refl
raisePhaseInjective {suc n} {Fin.zero} {Fin.suc y} ()
raisePhaseInjective {suc n} {Fin.suc x} {Fin.zero} ()
raisePhaseInjective {suc n} {Fin.suc x} {Fin.suc y} equality =
  cong Fin.suc (raisePhaseInjective (finSucInjective equality))

raisePhaseNotLast :
  ∀ {n : Nat} (phase : Fin.Fin n) →
  raisePhase phase ≡ lastPhase n → ⊥
raisePhaseNotLast {zero} ()
raisePhaseNotLast {suc n} Fin.zero ()
raisePhaseNotLast {suc n} (Fin.suc phase) equality =
  raisePhaseNotLast phase (finSucInjective equality)

------------------------------------------------------------------------
-- Fin-product state codec.
------------------------------------------------------------------------

phaseState :
  ∀ {states steps : Nat} →
  Fin.Fin states → Fin.Fin (suc steps) →
  Fin.Fin (states * suc steps)
phaseState = Fin.combine

combineFirstInjective :
  ∀ {m n : Nat}
    {x y : Fin.Fin m}
    {u v : Fin.Fin n} →
  Fin.combine x u ≡ Fin.combine y v →
  x ≡ y
combineFirstInjective {m} {n} {x} {y} {u} {v} equality =
  trans
    (sym (cong proj₁ (remQuot-combine {n = m} {k = n} x u)))
    (trans
      (cong (λ code → proj₁ (Fin.remQuot {m = m} n code)) equality)
      (cong proj₁ (remQuot-combine {n = m} {k = n} y v)))

combineSecondInjective :
  ∀ {m n : Nat}
    {x y : Fin.Fin m}
    {u v : Fin.Fin n} →
  Fin.combine x u ≡ Fin.combine y v →
  u ≡ v
combineSecondInjective {m} {n} {x} {y} {u} {v} equality =
  trans
    (sym (cong proj₂ (remQuot-combine {n = m} {k = n} x u)))
    (trans
      (cong (λ code → proj₂ (Fin.remQuot {m = m} n code)) equality)
      (cong proj₂ (remQuot-combine {n = m} {k = n} y v)))

------------------------------------------------------------------------
-- Rule compilation.
------------------------------------------------------------------------

liftRuleAt :
  ∀ {states symbols steps : Nat} →
  Fin.Fin steps →
  Local.TapeRule (Fin.Fin states) (Fin.Fin symbols) →
  Local.TapeRule (Fin.Fin (states * suc steps)) (Fin.Fin symbols)
liftRuleAt phase rule =
  Local.tape-rule
    (phaseState (Local.sourceState rule) (raisePhase phase))
    (Local.readSymbol rule)
    (phaseState (Local.targetState rule) (Fin.suc phase))
    (Local.writeSymbol rule)
    (Local.direction rule)

mapPhaseRules :
  ∀ {states symbols steps : Nat} →
  Fin.Fin steps →
  List (Local.TapeRule (Fin.Fin states) (Fin.Fin symbols)) →
  List (Local.TapeRule (Fin.Fin (states * suc steps)) (Fin.Fin symbols))
mapPhaseRules phase [] = []
mapPhaseRules phase (rule ∷ rest) =
  liftRuleAt phase rule ∷ mapPhaseRules phase rest

mapPhaseRuleOccurs :
  ∀ {states symbols steps : Nat}
    {phase : Fin.Fin steps}
    {rule : Local.TapeRule (Fin.Fin states) (Fin.Fin symbols)}
    {rules : List (Local.TapeRule (Fin.Fin states) (Fin.Fin symbols))} →
  Local.RuleOccurs rule rules →
  Local.RuleOccurs (liftRuleAt phase rule) (mapPhaseRules phase rules)
mapPhaseRuleOccurs Local.ruleHere = Local.ruleHere
mapPhaseRuleOccurs (Local.ruleThere occurs) =
  Local.ruleThere (mapPhaseRuleOccurs occurs)

mapPhaseRulePreimage :
  ∀ {states symbols steps : Nat}
    (phase : Fin.Fin steps)
    {wanted : Local.TapeRule (Fin.Fin (states * suc steps)) (Fin.Fin symbols)}
    {rules : List (Local.TapeRule (Fin.Fin states) (Fin.Fin symbols))} →
  Local.RuleOccurs wanted (mapPhaseRules phase rules) →
  Σ (Local.TapeRule (Fin.Fin states) (Fin.Fin symbols)) λ original →
    Σ (Local.RuleOccurs original rules) λ _ →
      wanted ≡ liftRuleAt phase original
mapPhaseRulePreimage phase {rules = []} ()
mapPhaseRulePreimage phase {rules = rule ∷ rest} Local.ruleHere =
  rule , Local.ruleHere , refl
mapPhaseRulePreimage phase {rules = rule ∷ rest} (Local.ruleThere occurs)
  with mapPhaseRulePreimage phase occurs
... | original , originalOccurs , exact =
  original , Local.ruleThere originalOccurs , exact

compilePhases :
  ∀ {states symbols steps : Nat} →
  List (Fin.Fin steps) →
  List (Local.TapeRule (Fin.Fin states) (Fin.Fin symbols)) →
  List (Local.TapeRule (Fin.Fin (states * suc steps)) (Fin.Fin symbols))
compilePhases [] rules = []
compilePhases (phase ∷ phases) rules =
  Mode.append (mapPhaseRules phase rules) (compilePhases phases rules)

phaseLiftRules :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  List
    (Local.TapeRule
      (Fin.Fin (Coded.stateCount source * suc steps))
      (Fin.Fin (Coded.symbolCount source)))
phaseLiftRules source steps =
  compilePhases (Coded.allFin steps) (Coded.rules source)

------------------------------------------------------------------------
-- Occurrence transport / inversion.
------------------------------------------------------------------------

appendLeftRuleOccurs :
  ∀ {State Symbol : Set}
    {rule : Local.TapeRule State Symbol}
    {left right : List (Local.TapeRule State Symbol)} →
  Local.RuleOccurs rule left →
  Local.RuleOccurs rule (Mode.append left right)
appendLeftRuleOccurs Local.ruleHere = Local.ruleHere
appendLeftRuleOccurs (Local.ruleThere occurs) =
  Local.ruleThere (appendLeftRuleOccurs occurs)

appendRightRuleOccurs :
  ∀ {State Symbol : Set}
    {rule : Local.TapeRule State Symbol}
    (left : List (Local.TapeRule State Symbol))
    {right : List (Local.TapeRule State Symbol)} →
  Local.RuleOccurs rule right →
  Local.RuleOccurs rule (Mode.append left right)
appendRightRuleOccurs [] occurs = occurs
appendRightRuleOccurs (_ ∷ left) occurs =
  Local.ruleThere (appendRightRuleOccurs left occurs)

compiledRuleOccursFromMember :
  ∀ {states symbols steps : Nat}
    {phase : Fin.Fin steps}
    {phases : List (Fin.Fin steps)}
    {rule : Local.TapeRule (Fin.Fin states) (Fin.Fin symbols)}
    {rules : List (Local.TapeRule (Fin.Fin states) (Fin.Fin symbols))} →
  Canonical.Member phase phases →
  Local.RuleOccurs rule rules →
  Local.RuleOccurs (liftRuleAt phase rule) (compilePhases phases rules)
compiledRuleOccursFromMember Canonical.here ruleOccurs =
  appendLeftRuleOccurs (mapPhaseRuleOccurs ruleOccurs)
compiledRuleOccursFromMember
    {rules = rules}
    (Canonical.there {y = earlier} member)
    ruleOccurs =
  appendRightRuleOccurs
    (mapPhaseRules earlier rules)
    (compiledRuleOccursFromMember member ruleOccurs)

phaseLiftRuleOccurs :
  (source : Coded.CodedFiniteStandardTM) →
  ∀ {steps : Nat}
    (phase : Fin.Fin steps)
    {rule : Local.TapeRule
      (Fin.Fin (Coded.stateCount source))
      (Fin.Fin (Coded.symbolCount source))} →
  Local.RuleOccurs rule (Coded.rules source) →
  Local.RuleOccurs (liftRuleAt phase rule) (phaseLiftRules source steps)
phaseLiftRuleOccurs source phase ruleOccurs =
  compiledRuleOccursFromMember
    (Coded.allFinMember phase)
    ruleOccurs

phaseTablePreimage :
  ∀ {states symbols steps : Nat}
    (phases : List (Fin.Fin steps))
    {wanted : Local.TapeRule (Fin.Fin (states * suc steps)) (Fin.Fin symbols)}
    {rules : List (Local.TapeRule (Fin.Fin states) (Fin.Fin symbols))} →
  Local.RuleOccurs wanted (compilePhases phases rules) →
  Σ (Fin.Fin steps) λ phase →
    Σ (Local.TapeRule (Fin.Fin states) (Fin.Fin symbols)) λ original →
      Σ (Local.RuleOccurs original rules) λ _ →
        wanted ≡ liftRuleAt phase original
phaseTablePreimage [] ()
phaseTablePreimage (phase ∷ phases) {rules = rules} occurs
  with Mode.splitAppendOccurrence
        (mapPhaseRules phase rules)
        (compilePhases phases rules)
        occurs
... | Mode.occursLeft leftOccurs
  with mapPhaseRulePreimage phase leftOccurs
... | original , originalOccurs , exact =
  phase , original , originalOccurs , exact
... | Mode.occursRight rightOccurs
  with phaseTablePreimage phases rightOccurs
... | later , original , originalOccurs , exact =
  later , original , originalOccurs , exact

------------------------------------------------------------------------
-- Determinism.
------------------------------------------------------------------------

phaseLiftDispatchUnique :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  ∀ {left right} →
  Local.RuleOccurs left (phaseLiftRules source steps) →
  Local.RuleOccurs right (phaseLiftRules source steps) →
  Local.sourceState left ≡ Local.sourceState right →
  Local.readSymbol left ≡ Local.readSymbol right →
  left ≡ right
phaseLiftDispatchUnique source steps leftOccurs rightOccurs sourceEq readEq
  with phaseTablePreimage (Coded.allFin steps) leftOccurs
     | phaseTablePreimage (Coded.allFin steps) rightOccurs
... | leftPhase , leftRule , leftRuleOccurs , refl
    | rightPhase , rightRule , rightRuleOccurs , refl
  with combineFirstInjective sourceEq
     | combineSecondInjective sourceEq
... | sourceStateEq | raisedPhaseEq
  with raisePhaseInjective raisedPhaseEq
... | phaseEq
  with Coded.dispatchUnique source
        leftRuleOccurs rightRuleOccurs sourceStateEq readEq
... | ruleEq
  rewrite phaseEq | ruleEq = refl

phaseLiftFragment :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  Mode.CodedModeFragment (Coded.symbolCount source)
phaseLiftFragment source steps = record
  { Mode.stateCount = Coded.stateCount source * suc steps
  ; Mode.rules = phaseLiftRules source steps
  ; Mode.dispatchUnique = phaseLiftDispatchUnique source steps
  }

------------------------------------------------------------------------
-- Full coded carrier.
------------------------------------------------------------------------

phaseInitialState :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  Fin.Fin (Coded.stateCount source * suc steps)
phaseInitialState source steps =
  phaseState (Coded.initialState source) Fin.zero

phaseSourceState :
  ∀ {steps : Nat}
    (source : Coded.CodedFiniteStandardTM) →
  Fin.Fin (Coded.stateCount source) →
  Fin.Fin steps →
  Fin.Fin (Coded.stateCount source * suc steps)
phaseSourceState source q phase =
  phaseState q (raisePhase phase)

phaseTargetState :
  ∀ {steps : Nat}
    (source : Coded.CodedFiniteStandardTM) →
  Fin.Fin (Coded.stateCount source) →
  Fin.Fin steps →
  Fin.Fin (Coded.stateCount source * suc steps)
phaseTargetState source q phase =
  phaseState q (Fin.suc phase)

phaseTerminalState :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  Fin.Fin (Coded.stateCount source) →
  Fin.Fin (Coded.stateCount source * suc steps)
phaseTerminalState source steps q =
  phaseState q (lastPhase steps)

phaseLiftCode :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  Coded.CodedFiniteStandardTM
phaseLiftCode source steps = record
  { Coded.stateCount = Coded.stateCount source * suc steps
  ; Coded.symbolCount = Coded.symbolCount source
  ; Coded.blank = Coded.blank source
  ; Coded.initialState = phaseInitialState source steps
  ; Coded.acceptingState =
      phaseTerminalState source steps (Coded.acceptingState source)
  ; Coded.rules = phaseLiftRules source steps
  ; Coded.dispatchUnique = phaseLiftDispatchUnique source steps
  }

phaseLiftAcceptingStateExact :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  Coded.acceptingState (phaseLiftCode source steps)
    ≡ phaseTerminalState source steps (Coded.acceptingState source)
phaseLiftAcceptingStateExact source steps = refl

phaseLiftConcreteMachine :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  Local.ConcreteTapeMachine
phaseLiftConcreteMachine source steps =
  Presented.finitePresentedStandardToConcrete
    (Coded.decodeCodedStandardTM (phaseLiftCode source steps))

phaseLiftConcreteDeterministic :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  Determinism.RuleKeyDeterministic (phaseLiftConcreteMachine source steps)
phaseLiftConcreteDeterministic source steps =
  phaseLiftDispatchUnique source steps

------------------------------------------------------------------------
-- Operational rule theorem.
------------------------------------------------------------------------

phaseLiftListedRuleDeterminesStandardTransition :
  (source : Coded.CodedFiniteStandardTM) →
  ∀ {steps : Nat}
    (phase : Fin.Fin steps)
    {wanted : Local.TapeRule
      (Fin.Fin (Coded.stateCount source))
      (Fin.Fin (Coded.symbolCount source))} →
  Local.RuleOccurs wanted (Coded.rules source) →
  ∃ λ matched →
    Interpreter.fetchConcreteRule
      (phaseLiftConcreteMachine source steps)
      (phaseSourceState source (Local.sourceState wanted) phase)
      (Local.readSymbol wanted)
      ≡ just matched
    × Standard.concreteControlTransition
        (phaseLiftConcreteMachine source steps)
        (phaseSourceState source (Local.sourceState wanted) phase)
        (Local.readSymbol wanted)
      ≡ just
          (Standard.standard-transition
            (phaseTargetState source (Local.targetState wanted) phase)
            (Local.writeSymbol wanted)
            (Local.direction wanted))
phaseLiftListedRuleDeterminesStandardTransition source {steps} phase wantedOccurs =
  Standard.listedRuleDeterminesStandardTransition
    (phaseLiftConcreteDeterministic source steps)
    (phaseLiftRuleOccurs source phase wantedOccurs)
    refl
    refl

------------------------------------------------------------------------
-- Terminal phase is genuinely quiescent.
------------------------------------------------------------------------

noResidentRuleAtTerminalPhase :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  ∀ {rule}
    (occurs : Local.RuleOccurs rule (phaseLiftRules source steps))
    (q : Fin.Fin (Coded.stateCount source)) →
  Local.sourceState rule ≡ phaseTerminalState source steps q →
  ⊥
noResidentRuleAtTerminalPhase source steps occurs q sourceEq
  with phaseTablePreimage (Coded.allFin steps) occurs
... | phase , original , originalOccurs , refl =
  raisePhaseNotLast phase (combineSecondInjective sourceEq)

terminalDispatchKeyFresh :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  ∀ {resident}
    (residentOccurs : Local.RuleOccurs resident (phaseLiftRules source steps))
    (q : Fin.Fin (Coded.stateCount source))
    (symbol : Fin.Fin (Coded.symbolCount source)) →
  Local.sourceState resident ≡ phaseTerminalState source steps q →
  Local.readSymbol resident ≡ symbol →
  ⊥
terminalDispatchKeyFresh source steps residentOccurs q symbol sourceEq readEq =
  noResidentRuleAtTerminalPhase source steps residentOccurs q sourceEq

terminalResidentKeyFresh :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  (q : Fin.Fin (Coded.stateCount source)) →
  (symbol : Fin.Fin (Coded.symbolCount source)) →
  Singleton.ResidentKeyFresh
    (phaseLiftFragment source steps)
    (phaseTerminalState source steps q)
    symbol
terminalResidentKeyFresh source steps q symbol residentOccurs sourceEq readEq =
  terminalDispatchKeyFresh
    source steps residentOccurs q symbol sourceEq readEq

terminalFetchNothing :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  (q : Fin.Fin (Coded.stateCount source)) →
  (symbol : Fin.Fin (Coded.symbolCount source)) →
  Interpreter.fetchConcreteRule
    (phaseLiftConcreteMachine source steps)
    (phaseTerminalState source steps q)
    symbol
  ≡ nothing
terminalFetchNothing source steps q symbol
  with Interpreter.fetchConcreteRule
    (phaseLiftConcreteMachine source steps)
    (phaseTerminalState source steps q)
    symbol
... | nothing = refl
... | just matched =
  ⊥-elim
    (noResidentRuleAtTerminalPhase
      source steps
      (Interpreter.occurs matched)
      q
      (Interpreter.sourceExact matched))

terminalStandardTransitionNothing :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  (q : Fin.Fin (Coded.stateCount source)) →
  (symbol : Fin.Fin (Coded.symbolCount source)) →
  Standard.concreteControlTransition
    (phaseLiftConcreteMachine source steps)
    (phaseTerminalState source steps q)
    symbol
  ≡ nothing
terminalStandardTransitionNothing source steps q symbol
  rewrite terminalFetchNothing source steps q symbol = refl

------------------------------------------------------------------------
-- MAX-CUT CONSEQUENCE
--
-- Exact-T endpoint quiescence is now a concrete compiler theorem.  The remaining
-- phase-lift work is whole-run induction: transport a source T-step exact run to
-- the same tape evolution under the phase-lift code, ending in terminal phase T.
------------------------------------------------------------------------
