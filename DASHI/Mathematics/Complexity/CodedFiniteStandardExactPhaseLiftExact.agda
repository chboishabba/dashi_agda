module DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact where

------------------------------------------------------------------------
-- EXACT FINITE-CONTROL PHASE LIFT
--
-- For the fixed diagonal target, the candidate budget T is one fixed natural.
-- We therefore do not need a runtime tape counter merely to obtain a fresh
-- return boundary.  Instead lift the source control to
--
--   sourceState x elapsedPhase,   elapsedPhase : Fin (T + 1),
--
-- encoded literally in Fin (|Q| * (T + 1)).  Every source rule is copied at
-- each phase k < T and advances k -> k+1.  No resident source rule is generated
-- at the terminal phase T.  Hence the T-boundary is quiescent by construction
-- and a cross-mode return link cannot collide with a resident candidate key.
--
-- This owner pays the finite rule-table / determinism / freshness construction.
-- Whole-run simulation is intentionally separated into the companion owner.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_) 
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Fin.Base as Fin
open import Data.Fin.Properties using (remQuot-combine)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode

------------------------------------------------------------------------
-- Fin n embeds as the nonterminal phases of Fin (suc n).
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
-- Product-state codec and injectivity projections.
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
    (sym
      (cong proj₁
        (remQuot-combine {n = m} {k = n} x u)))
    (trans
      (cong (λ code → proj₁ (Fin.remQuot {m = m} n code)) equality)
      (cong proj₁
        (remQuot-combine {n = m} {k = n} y v)))

combineSecondInjective :
  ∀ {m n : Nat}
    {x y : Fin.Fin m}
    {u v : Fin.Fin n} →
  Fin.combine x u ≡ Fin.combine y v →
  u ≡ v
combineSecondInjective {m} {n} {x} {y} {u} {v} equality =
  trans
    (sym
      (cong proj₂
        (remQuot-combine {n = m} {k = n} x u)))
    (trans
      (cong (λ code → proj₂ (Fin.remQuot {m = m} n code)) equality)
      (cong proj₂
        (remQuot-combine {n = m} {k = n} y v)))

------------------------------------------------------------------------
-- Copy one source rule at one nonterminal elapsed phase.
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

------------------------------------------------------------------------
-- Concatenate the copied table over every k : Fin T.
------------------------------------------------------------------------

compilePhases :
  ∀ {states symbols steps : Nat} →
  List (Fin.Fin steps) →
  List (Local.TapeRule (Fin.Fin states) (Fin.Fin symbols)) →
  List (Local.TapeRule (Fin.Fin (states * suc steps)) (Fin.Fin symbols))
compilePhases [] rules = []
compilePhases (phase ∷ phases) rules =
  Mode.append (mapPhaseRules phase rules) (compilePhases phases rules)

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
phaseTablePreimage (phase ∷ phases) {rules = rules} occurs
  | Mode.occursRight rightOccurs
  with phaseTablePreimage phases rightOccurs
... | later , original , originalOccurs , exact =
  later , original , originalOccurs , exact

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
-- Determinism is inherited from the source table plus injectivity of phase.
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
-- Initial and terminal phase-state embeddings.
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

------------------------------------------------------------------------
-- THE KEY RETURN-BOUNDARY THEOREM:
-- no copied candidate rule has a source state in terminal phase T.
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

------------------------------------------------------------------------
-- MAX-CUT CONSEQUENCE
--
-- The old exact-T return obstruction is no longer an architectural blocker.
-- For one fixed budget T, the candidate can be compiled into a finite control
-- product with T+1 phase slices.  The T-th slice has no resident rules at all,
-- so return/opposite-mode links are fresh regardless of endpoint source state
-- and scanned symbol.  Remaining work is the exact whole-run lift into this
-- phase-indexed fragment and assembly with the generator/opposite modes.
------------------------------------------------------------------------
