module DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact where

------------------------------------------------------------------------
-- DISJOINT FINITE-MODE COMPOSITION FOR CODED STANDARD MACHINES
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded

embedLeft : ∀ {m n : Nat} → Fin.Fin m → Fin.Fin (m + n)
embedLeft {zero} ()
embedLeft {suc m} {n} Fin.zero = Fin.zero
embedLeft {suc m} {n} (Fin.suc x) = Fin.suc (embedLeft {m} {n} x)

embedRight : ∀ {m n : Nat} → Fin.Fin n → Fin.Fin (m + n)
embedRight {zero} {n} x = x
embedRight {suc m} {n} x = Fin.suc (embedRight {m} {n} x)

finSucInjective : ∀ {n} {a b : Fin.Fin n} → Fin.suc a ≡ Fin.suc b → a ≡ b
finSucInjective refl = refl

embedLeftInjective :
  ∀ {m n : Nat} {x y : Fin.Fin m} →
  embedLeft {m} {n} x ≡ embedLeft y → x ≡ y
embedLeftInjective {zero} {x = ()}
embedLeftInjective {suc m} {n} {Fin.zero} {Fin.zero} equality = refl
embedLeftInjective {suc m} {n} {Fin.zero} {Fin.suc y} ()
embedLeftInjective {suc m} {n} {Fin.suc x} {Fin.zero} ()
embedLeftInjective {suc m} {n} {Fin.suc x} {Fin.suc y} equality
  with embedLeftInjective {m} {n} {x} {y} (finSucInjective equality)
... | refl = refl

embedRightInjective :
  ∀ {m n : Nat} {x y : Fin.Fin n} →
  embedRight {m} {n} x ≡ embedRight y → x ≡ y
embedRightInjective {zero} equality = equality
embedRightInjective {suc m} {n} equality =
  embedRightInjective {m} {n} (finSucInjective equality)

embedLeftRightDisjoint :
  ∀ {m n : Nat}
    (x : Fin.Fin m)
    (y : Fin.Fin n) →
  embedLeft {m} {n} x ≡ embedRight y → ⊥
embedLeftRightDisjoint {zero} () y equality
embedLeftRightDisjoint {suc m} {n} Fin.zero y ()
embedLeftRightDisjoint {suc m} {n} (Fin.suc x) y equality =
  embedLeftRightDisjoint {m} {n} x y (finSucInjective equality)

------------------------------------------------------------------------
-- State-only reindexing of literal tape rules.
------------------------------------------------------------------------

mapStateRule :
  ∀ {m n symbols : Nat} →
  (Fin.Fin m → Fin.Fin n) →
  Local.TapeRule (Fin.Fin m) (Fin.Fin symbols) →
  Local.TapeRule (Fin.Fin n) (Fin.Fin symbols)
mapStateRule stateMap rule =
  Local.tape-rule
    (stateMap (Local.sourceState rule))
    (Local.readSymbol rule)
    (stateMap (Local.targetState rule))
    (Local.writeSymbol rule)
    (Local.direction rule)

mapRules :
  ∀ {m n symbols : Nat} →
  (Fin.Fin m → Fin.Fin n) →
  List (Local.TapeRule (Fin.Fin m) (Fin.Fin symbols)) →
  List (Local.TapeRule (Fin.Fin n) (Fin.Fin symbols))
mapRules stateMap [] = []
mapRules stateMap (rule ∷ rest) =
  mapStateRule stateMap rule ∷ mapRules stateMap rest

mapRuleOccurs :
  ∀ {m n symbols : Nat}
    {stateMap : Fin.Fin m → Fin.Fin n}
    {rule : Local.TapeRule (Fin.Fin m) (Fin.Fin symbols)}
    {rules : List (Local.TapeRule (Fin.Fin m) (Fin.Fin symbols))} →
  Local.RuleOccurs rule rules →
  Local.RuleOccurs (mapStateRule stateMap rule) (mapRules stateMap rules)
mapRuleOccurs Local.ruleHere = Local.ruleHere
mapRuleOccurs (Local.ruleThere occurs) =
  Local.ruleThere (mapRuleOccurs occurs)

mappedRulePreimage :
  ∀ {m n symbols : Nat}
    (stateMap : Fin.Fin m → Fin.Fin n)
    {wanted : Local.TapeRule (Fin.Fin n) (Fin.Fin symbols)}
    {rules : List (Local.TapeRule (Fin.Fin m) (Fin.Fin symbols))} →
  Local.RuleOccurs wanted (mapRules stateMap rules) →
  Σ (Local.TapeRule (Fin.Fin m) (Fin.Fin symbols)) λ original →
    Σ (Local.RuleOccurs original rules) λ _ →
      wanted ≡ mapStateRule stateMap original
mappedRulePreimage stateMap {rules = []} ()
mappedRulePreimage stateMap {rules = rule ∷ rest} Local.ruleHere =
  rule , Local.ruleHere , refl
mappedRulePreimage stateMap {rules = rule ∷ rest} (Local.ruleThere occurs)
  with mappedRulePreimage stateMap occurs
... | original , originalOccurs , exact =
  original , Local.ruleThere originalOccurs , exact

------------------------------------------------------------------------
-- Append-membership view specialized to tape rules.
------------------------------------------------------------------------

append : ∀ {A : Set} → List A → List A → List A
append [] right = right
append (x ∷ left) right = x ∷ append left right

data AppendOccurrence {State Symbol : Set}
    (rule : Local.TapeRule State Symbol)
    (left right : List (Local.TapeRule State Symbol)) : Set where
  occursLeft :
    Local.RuleOccurs rule left →
    AppendOccurrence rule left right
  occursRight :
    Local.RuleOccurs rule right →
    AppendOccurrence rule left right

splitAppendOccurrence :
  ∀ {State Symbol : Set}
    {rule : Local.TapeRule State Symbol}
    (left right : List (Local.TapeRule State Symbol)) →
  Local.RuleOccurs rule (append left right) →
  AppendOccurrence rule left right
splitAppendOccurrence [] right occurs = occursRight occurs
splitAppendOccurrence (x ∷ left) right Local.ruleHere =
  occursLeft Local.ruleHere
splitAppendOccurrence (x ∷ left) right (Local.ruleThere occurs)
  with splitAppendOccurrence left right occurs
... | occursLeft leftOccurs =
  occursLeft (Local.ruleThere leftOccurs)
... | occursRight rightOccurs =
  occursRight rightOccurs

------------------------------------------------------------------------
-- A mode fragment has finite states and literal deterministic rules, but leaves
-- global blank/initial/accepting choices to the final enclosing target.
------------------------------------------------------------------------

record CodedModeFragment (symbols : Nat) : Set where
  field
    stateCount : Nat
    rules : List (Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbols))
    dispatchUnique :
      ∀ {left right} →
      Local.RuleOccurs left rules →
      Local.RuleOccurs right rules →
      Local.sourceState left ≡ Local.sourceState right →
      Local.readSymbol left ≡ Local.readSymbol right →
      left ≡ right

open CodedModeFragment public

fragmentFromCode :
  (code : Coded.CodedFiniteStandardTM) →
  CodedModeFragment (Coded.symbolCount code)
fragmentFromCode code = record
  { stateCount = Coded.stateCount code
  ; rules = Coded.rules code
  ; dispatchUnique = Coded.dispatchUnique code
  }

------------------------------------------------------------------------
-- Deterministic disjoint sum.
------------------------------------------------------------------------

sumFragments :
  ∀ {symbols : Nat} →
  (left right : CodedModeFragment symbols) →
  CodedModeFragment symbols
sumFragments {symbols} left right = record
  { stateCount = stateCount left + stateCount right
  ; rules =
      append
        (mapRules leftMap (rules left))
        (mapRules rightMap (rules right))
  ; dispatchUnique = combinedUnique
  }
  where
    leftMap : Fin.Fin (stateCount left) → Fin.Fin (stateCount left + stateCount right)
    leftMap = embedLeft

    rightMap : Fin.Fin (stateCount right) → Fin.Fin (stateCount left + stateCount right)
    rightMap = embedRight

    combinedUnique :
      ∀ {first second} →
      Local.RuleOccurs first
        (append (mapRules leftMap (rules left)) (mapRules rightMap (rules right))) →
      Local.RuleOccurs second
        (append (mapRules leftMap (rules left)) (mapRules rightMap (rules right))) →
      Local.sourceState first ≡ Local.sourceState second →
      Local.readSymbol first ≡ Local.readSymbol second →
      first ≡ second
    combinedUnique {first} {second} firstOccurs secondOccurs sourceEq readEq
      with splitAppendOccurrence
            (mapRules leftMap (rules left))
            (mapRules rightMap (rules right))
            firstOccurs
         | splitAppendOccurrence
            (mapRules leftMap (rules left))
            (mapRules rightMap (rules right))
            secondOccurs
    ... | occursLeft firstLeft | occursLeft secondLeft
      with mappedRulePreimage leftMap firstLeft
         | mappedRulePreimage leftMap secondLeft
    ... | firstRule , firstRuleOccurs , refl
        | secondRule , secondRuleOccurs , refl =
      cong (mapStateRule leftMap)
        (dispatchUnique left
          firstRuleOccurs secondRuleOccurs
          (embedLeftInjective sourceEq)
          readEq)
    ... | occursRight firstRight | occursRight secondRight
      with mappedRulePreimage rightMap firstRight
         | mappedRulePreimage rightMap secondRight
    ... | firstRule , firstRuleOccurs , refl
        | secondRule , secondRuleOccurs , refl =
      cong (mapStateRule rightMap)
        (dispatchUnique right
          firstRuleOccurs secondRuleOccurs
          (embedRightInjective sourceEq)
          readEq)
    ... | occursLeft firstLeft | occursRight secondRight
      with mappedRulePreimage leftMap firstLeft
         | mappedRulePreimage rightMap secondRight
    ... | firstRule , firstRuleOccurs , refl
        | secondRule , secondRuleOccurs , refl =
      ⊥-elim
        (embedLeftRightDisjoint
          (Local.sourceState firstRule)
          (Local.sourceState secondRule)
          sourceEq)
    ... | occursRight firstRight | occursLeft secondLeft
      with mappedRulePreimage rightMap firstRight
         | mappedRulePreimage leftMap secondLeft
    ... | firstRule , firstRuleOccurs , refl
        | secondRule , secondRuleOccurs , refl =
      ⊥-elim
        (embedLeftRightDisjoint
          (Local.sourceState secondRule)
          (Local.sourceState firstRule)
          (sym sourceEq))

------------------------------------------------------------------------
-- Close a fragment into literal low-universe coded standard syntax.
------------------------------------------------------------------------

closeFragment :
  ∀ {symbols : Nat}
    (fragment : CodedModeFragment symbols) →
  (blank : Fin.Fin symbols) →
  (initial accepting : Fin.Fin (stateCount fragment)) →
  Coded.CodedFiniteStandardTM
closeFragment {symbols} fragment blank initial accepting = record
  { Coded.stateCount = stateCount fragment
  ; Coded.symbolCount = symbols
  ; Coded.blank = blank
  ; Coded.initialState = initial
  ; Coded.acceptingState = accepting
  ; Coded.rules = rules fragment
  ; Coded.dispatchUnique = dispatchUnique fragment
  }

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Generator/candidate/opposite control can now be assembled as genuine disjoint
-- finite rule-table regions before adding explicit call/return bridge rules.  No
-- Agda-level semantic primitive is introduced by this composition step.
------------------------------------------------------------------------
