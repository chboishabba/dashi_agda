module DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact where

------------------------------------------------------------------------
-- FINITE MACHINE RULE TABLE -> FIXED-WIDTH SHARED RULE SELECTOR
--
-- A SAT transition must choose one rule from the machine table; individual
-- windows must not choose unrelated rules independently.
--
-- We encode a RuleOccurs witness as a one-hot vector of length |rules|.  An
-- arbitrary bit vector decodes to the first selected table rule; if no bit is
-- selected, a supplied nonempty-table witness provides a fallback.  Thus every
-- decoded selector is theorem-bearing evidence that its rule occurs in the
-- literal machine rule list.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Sigma using (Σ; _,_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

RuleWidth : Local.ConcreteTapeMachine → Agda.Builtin.Nat.Nat
RuleWidth machine =
  Canonical.listLength (Local.rules machine)

zeros :
  ∀ (n : Agda.Builtin.Nat.Nat) →
  CNF.Bits n
zeros Agda.Builtin.Nat.zero = CNF.[]ᵇ
zeros (Agda.Builtin.Nat.suc n) =
  false CNF.∷ᵇ zeros n

encodeRuleOccurs :
  ∀ {State Symbol : Set}
    {rule : Local.TapeRule State Symbol}
    {rules : List (Local.TapeRule State Symbol)} →
  Local.RuleOccurs rule rules →
  CNF.Bits (Canonical.listLength rules)
encodeRuleOccurs {rules = rule ∷ rest} Local.ruleHere =
  true CNF.∷ᵇ zeros (Canonical.listLength rest)
encodeRuleOccurs {rules = other ∷ rest}
    (Local.ruleThere occurrence) =
  false CNF.∷ᵇ encodeRuleOccurs occurrence

data ListedRule {State Symbol : Set}
    (rules : List (Local.TapeRule State Symbol)) : Set where
  listed-rule :
    (rule : Local.TapeRule State Symbol) →
    Local.RuleOccurs rule rules →
    ListedRule rules

selectedRule :
  ∀ {State Symbol rules} →
  ListedRule {State} {Symbol} rules →
  Local.TapeRule State Symbol
selectedRule (listed-rule rule occurrence) = rule

selectedOccurs :
  ∀ {State Symbol rules}
    (choice : ListedRule {State} {Symbol} rules) →
  Local.RuleOccurs (selectedRule choice) rules
selectedOccurs (listed-rule rule occurrence) = occurrence

liftListedRule :
  ∀ {State Symbol}
    {head : Local.TapeRule State Symbol}
    {tail : List (Local.TapeRule State Symbol)} →
  ListedRule tail →
  ListedRule (head ∷ tail)
liftListedRule (listed-rule rule occurrence) =
  listed-rule rule (Local.ruleThere occurrence)

decodePresent :
  ∀ {State Symbol}
    (rules : List (Local.TapeRule State Symbol)) →
  CNF.Bits (Canonical.listLength rules) →
  Maybe (ListedRule rules)
decodePresent [] CNF.[]ᵇ =
  nothing
decodePresent (head ∷ tail) (true CNF.∷ᵇ bits) =
  just (listed-rule head Local.ruleHere)
decodePresent (head ∷ tail) (false CNF.∷ᵇ bits)
    with decodePresent tail bits
... | nothing = nothing
... | just choice = just (liftListedRule choice)

record NonemptyRuleTable
    (machine : Local.ConcreteTapeMachine) : Set where
  field
    fallbackRule :
      Local.TapeRule
        (Local.State machine)
        (Local.Symbol machine)
    fallbackOccurs :
      Local.RuleOccurs fallbackRule (Local.rules machine)

open NonemptyRuleTable public

decodeRuleChoice :
  ∀ {machine} →
  NonemptyRuleTable machine →
  CNF.Bits (RuleWidth machine) →
  ListedRule (Local.rules machine)
decodeRuleChoice {machine} nonempty bits
    with decodePresent (Local.rules machine) bits
... | nothing =
  listed-rule
    (fallbackRule nonempty)
    (fallbackOccurs nonempty)
... | just choice = choice

decodeRule :
  ∀ {machine} →
  NonemptyRuleTable machine →
  CNF.Bits (RuleWidth machine) →
  Local.TapeRule
    (Local.State machine)
    (Local.Symbol machine)
decodeRule nonempty bits =
  selectedRule (decodeRuleChoice nonempty bits)

decodeRuleOccurs :
  ∀ {machine}
    (nonempty : NonemptyRuleTable machine)
    (bits : CNF.Bits (RuleWidth machine)) →
  Local.RuleOccurs
    (decodeRule nonempty bits)
    (Local.rules machine)
decodeRuleOccurs nonempty bits =
  selectedOccurs (decodeRuleChoice nonempty bits)

decodePresentEncode :
  ∀ {State Symbol}
    {rule : Local.TapeRule State Symbol}
    {rules : List (Local.TapeRule State Symbol)}
    (occurrence : Local.RuleOccurs rule rules) →
  decodePresent rules (encodeRuleOccurs occurrence)
  ≡ just (listed-rule rule occurrence)
decodePresentEncode {rules = rule ∷ rest} Local.ruleHere =
  refl
decodePresentEncode {rules = other ∷ rest}
    (Local.ruleThere occurrence)
    rewrite decodePresentEncode occurrence =
  refl

decodeEncodedRule :
  ∀ {machine}
    (nonempty : NonemptyRuleTable machine)
    {rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)}
    (occurrence : Local.RuleOccurs rule (Local.rules machine)) →
  decodeRule nonempty (encodeRuleOccurs occurrence)
  ≡ rule
decodeEncodedRule nonempty occurrence
    rewrite decodePresentEncode occurrence =
  refl

record RuleSelectorReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    nonemptyRuleTable : NonemptyRuleTable machine
    fixedWidth : Agda.Builtin.Nat.Nat
    widthExact : fixedWidth ≡ RuleWidth machine
    everyDecodedRuleOccurs :
      (bits : CNF.Bits fixedWidth) →
      Local.RuleOccurs
        (decodeRule nonemptyRuleTable
          (transportBits widthExact bits))
        (Local.rules machine)

  transportBits :
    ∀ {m n : Agda.Builtin.Nat.Nat} →
    m ≡ n → CNF.Bits m → CNF.Bits n
  transportBits refl bits = bits

canonicalRuleSelectorReceipt :
  ∀ (machine : Local.ConcreteTapeMachine)
    (nonempty : NonemptyRuleTable machine) →
  RuleSelectorReceipt machine
canonicalRuleSelectorReceipt machine nonempty = record
  { nonemptyRuleTable = nonempty
  ; fixedWidth = RuleWidth machine
  ; widthExact = refl
  ; everyDecodedRuleOccurs =
      decodeRuleOccurs nonempty
  }
