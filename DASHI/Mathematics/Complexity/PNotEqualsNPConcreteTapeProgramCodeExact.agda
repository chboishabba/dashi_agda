module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact where

------------------------------------------------------------------------
-- FINITE STATIC PROGRAM CODE FOR CONCRETE TAPE MACHINES
--
-- Resource-bounded self-reference cannot consume a bare extensional function;
-- it needs finite syntax for the machine under attack.
--
-- The existing concrete-tape layer already provides:
--
--   * finite State / Symbol enumerations with coverage;
--   * left-invertible fixed-width encodings of states and symbols;
--   * a finite literal transition-rule list.
--
-- This owner serializes the machine's STATIC program data:
--
--   blank symbol
--   initial state
--   accepting state
--   complete transition rule list
--
-- into one fixed-width Boolean vector and proves fieldwise decode-after-encode.
--
-- This is intentionally not yet a universal interpreter or a SAT self-fixed
-- point.  It pays only the finite program-description premise needed before
-- those constructions can be stated honestly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Direction codec.
------------------------------------------------------------------------

three : Nat
three = suc (suc (suc zero))

encodeDirection :
  Local.Direction →
  CNF.Bits three
encodeDirection Local.moveLeft =
  true CNF.∷ᵇ false CNF.∷ᵇ false CNF.∷ᵇ CNF.[]ᵇ
encodeDirection Local.stayPut =
  false CNF.∷ᵇ true CNF.∷ᵇ false CNF.∷ᵇ CNF.[]ᵇ
encodeDirection Local.moveRight =
  false CNF.∷ᵇ false CNF.∷ᵇ true CNF.∷ᵇ CNF.[]ᵇ

decodeDirection :
  CNF.Bits three →
  Local.Direction
decodeDirection (true CNF.∷ᵇ second CNF.∷ᵇ third CNF.∷ᵇ CNF.[]ᵇ) =
  Local.moveLeft
decodeDirection (false CNF.∷ᵇ true CNF.∷ᵇ third CNF.∷ᵇ CNF.[]ᵇ) =
  Local.stayPut
decodeDirection (false CNF.∷ᵇ false CNF.∷ᵇ third CNF.∷ᵇ CNF.[]ᵇ) =
  Local.moveRight

decodeEncodeDirection :
  (direction : Local.Direction) →
  decodeDirection (encodeDirection direction) ≡ direction
decodeEncodeDirection Local.moveLeft = refl
decodeEncodeDirection Local.stayPut = refl
decodeEncodeDirection Local.moveRight = refl

directionCodec :
  Canonical.FixedBitsCodec Local.Direction three
directionCodec = record
  { Canonical.encode = encodeDirection
  ; Canonical.decode = decodeDirection
  ; Canonical.decodeEncode = decodeEncodeDirection
  }

------------------------------------------------------------------------
-- Literal rule codec.
------------------------------------------------------------------------

RuleBitsWidth :
  Local.ConcreteTapeMachine →
  Nat
RuleBitsWidth machine =
  Canonical.StateWidth machine
  +
  (Canonical.SymbolWidth machine
  +
  (Canonical.StateWidth machine
  +
  (Canonical.SymbolWidth machine
  + three)))

RuleTuple :
  (machine : Local.ConcreteTapeMachine) →
  Set
RuleTuple machine =
  Local.State machine
  ×
  (Local.Symbol machine
  ×
  (Local.State machine
  ×
  (Local.Symbol machine
  × Local.Direction)))

open import Data.Product using (_×_; _,_)

ruleToTuple :
  ∀ {machine : Local.ConcreteTapeMachine} →
  Local.TapeRule
    (Local.State machine)
    (Local.Symbol machine) →
  RuleTuple machine
ruleToTuple
    (Local.tape-rule
      source read target write direction) =
  source , (read , (target , (write , direction)))

tupleToRule :
  ∀ {machine : Local.ConcreteTapeMachine} →
  RuleTuple machine →
  Local.TapeRule
    (Local.State machine)
    (Local.Symbol machine)
tupleToRule
    (source , (read , (target , (write , direction)))) =
  Local.tape-rule
    source read target write direction

tupleRuleRoundTrip :
  ∀ {machine : Local.ConcreteTapeMachine}
    (rule :
      Local.TapeRule
        (Local.State machine)
        (Local.Symbol machine)) →
  tupleToRule (ruleToTuple rule) ≡ rule
tupleRuleRoundTrip
    (Local.tape-rule source read target write direction) =
  refl

canonicalRuleTupleCodec :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  Canonical.FixedBitsCodec
    (RuleTuple machine)
    (RuleBitsWidth machine)
canonicalRuleTupleCodec machine stateCoverage symbolCoverage =
  Canonical.pairCodec state
    (Canonical.pairCodec symbol
      (Canonical.pairCodec state
        (Canonical.pairCodec symbol directionCodec)))
  where
    state =
      Canonical.canonicalStateCodec machine stateCoverage

    symbol =
      Canonical.canonicalSymbolCodec machine symbolCoverage

encodeRule :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  Local.TapeRule
    (Local.State machine)
    (Local.Symbol machine) →
  CNF.Bits (RuleBitsWidth machine)
encodeRule {machine} stateCoverage symbolCoverage rule =
  Canonical.encode
    (canonicalRuleTupleCodec
      machine stateCoverage symbolCoverage)
    (ruleToTuple rule)

decodeRule :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  CNF.Bits (RuleBitsWidth machine) →
  Local.TapeRule
    (Local.State machine)
    (Local.Symbol machine)
decodeRule {machine} stateCoverage symbolCoverage bits =
  tupleToRule
    (Canonical.decode
      (canonicalRuleTupleCodec
        machine stateCoverage symbolCoverage)
      bits)

decodeEncodeRule :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rule :
      Local.TapeRule
        (Local.State machine)
        (Local.Symbol machine)) →
  decodeRule stateCoverage symbolCoverage
    (encodeRule stateCoverage symbolCoverage rule)
  ≡ rule
decodeEncodeRule {machine}
    stateCoverage symbolCoverage rule =
  trans
    (cong tupleToRule
      (Canonical.decodeEncode
        (canonicalRuleTupleCodec
          machine stateCoverage symbolCoverage)
        (ruleToTuple rule)))
    (tupleRuleRoundTrip rule)

------------------------------------------------------------------------
-- Fixed-length list codec specialized to the literal machine rule table.
------------------------------------------------------------------------

encodeRuleList :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rules :
      List
        (Local.TapeRule
          (Local.State machine)
          (Local.Symbol machine))) →
  CNF.Bits
    (Canonical.listLength rules * RuleBitsWidth machine)
encodeRuleList stateCoverage symbolCoverage [] =
  CNF.[]ᵇ
encodeRuleList {machine}
    stateCoverage symbolCoverage
    (rule ∷ rules) =
  Canonical.appendBits
    (encodeRule stateCoverage symbolCoverage rule)
    (encodeRuleList stateCoverage symbolCoverage rules)

decodeRuleList :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (count : Nat) →
  CNF.Bits (count * RuleBitsWidth machine) →
  List
    (Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
decodeRuleList stateCoverage symbolCoverage zero CNF.[]ᵇ =
  []
decodeRuleList {machine}
    stateCoverage symbolCoverage
    (suc count) bits =
  decodeRule stateCoverage symbolCoverage
    (Canonical.takeBits (RuleBitsWidth machine) bits)
  ∷
  decodeRuleList
    stateCoverage symbolCoverage count
    (Canonical.dropBits (RuleBitsWidth machine) bits)

decodeEncodeRuleList :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rules :
      List
        (Local.TapeRule
          (Local.State machine)
          (Local.Symbol machine))) →
  decodeRuleList
    stateCoverage symbolCoverage
    (Canonical.listLength rules)
    (encodeRuleList stateCoverage symbolCoverage rules)
  ≡ rules
decodeEncodeRuleList stateCoverage symbolCoverage [] =
  refl
decodeEncodeRuleList {machine}
    stateCoverage symbolCoverage
    (rule ∷ rules)
    rewrite
      Canonical.takeAppendBits
        (encodeRule stateCoverage symbolCoverage rule)
        (encodeRuleList stateCoverage symbolCoverage rules)
      |
      Canonical.dropAppendBits
        (encodeRule stateCoverage symbolCoverage rule)
        (encodeRuleList stateCoverage symbolCoverage rules)
      |
      decodeEncodeRule stateCoverage symbolCoverage rule
      |
      decodeEncodeRuleList stateCoverage symbolCoverage rules =
  refl

------------------------------------------------------------------------
-- Whole static machine code.
------------------------------------------------------------------------

RuleTableBitsWidth :
  Local.ConcreteTapeMachine →
  Nat
RuleTableBitsWidth machine =
  Canonical.listLength (Local.rules machine)
  * RuleBitsWidth machine

StaticProgramBitsWidth :
  Local.ConcreteTapeMachine →
  Nat
StaticProgramBitsWidth machine =
  Canonical.SymbolWidth machine
  +
  (Canonical.StateWidth machine
  +
  (Canonical.StateWidth machine
  + RuleTableBitsWidth machine))

encodeStaticProgram :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  CNF.Bits (StaticProgramBitsWidth machine)
encodeStaticProgram machine stateCoverage symbolCoverage =
  Canonical.appendBits
    (Canonical.encode
      (Canonical.canonicalSymbolCodec machine symbolCoverage)
      (Local.blank machine))
    (Canonical.appendBits
      (Canonical.encode
        (Canonical.canonicalStateCodec machine stateCoverage)
        (Local.initialState machine))
      (Canonical.appendBits
        (Canonical.encode
          (Canonical.canonicalStateCodec machine stateCoverage)
          (Local.acceptingState machine))
        (encodeRuleList
          stateCoverage symbolCoverage
          (Local.rules machine))))

decodeProgramBlank :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  CNF.Bits (StaticProgramBitsWidth machine) →
  Local.Symbol machine
decodeProgramBlank machine stateCoverage symbolCoverage bits =
  Canonical.decode
    (Canonical.canonicalSymbolCodec machine symbolCoverage)
    (Canonical.takeBits
      (Canonical.SymbolWidth machine)
      bits)

decodeProgramAfterBlank :
  ∀ (machine : Local.ConcreteTapeMachine) →
  CNF.Bits (StaticProgramBitsWidth machine) →
  CNF.Bits
    (Canonical.StateWidth machine
      +
      (Canonical.StateWidth machine
      + RuleTableBitsWidth machine))
decodeProgramAfterBlank machine bits =
  Canonical.dropBits
    (Canonical.SymbolWidth machine)
    bits

decodeProgramInitialState :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  CNF.Bits (StaticProgramBitsWidth machine) →
  Local.State machine
decodeProgramInitialState machine stateCoverage symbolCoverage bits =
  Canonical.decode
    (Canonical.canonicalStateCodec machine stateCoverage)
    (Canonical.takeBits
      (Canonical.StateWidth machine)
      (decodeProgramAfterBlank machine bits))

decodeProgramAfterInitial :
  ∀ (machine : Local.ConcreteTapeMachine) →
  CNF.Bits (StaticProgramBitsWidth machine) →
  CNF.Bits
    (Canonical.StateWidth machine
      + RuleTableBitsWidth machine)
decodeProgramAfterInitial machine bits =
  Canonical.dropBits
    (Canonical.StateWidth machine)
    (decodeProgramAfterBlank machine bits)

decodeProgramAcceptingState :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  CNF.Bits (StaticProgramBitsWidth machine) →
  Local.State machine
decodeProgramAcceptingState
    machine stateCoverage symbolCoverage bits =
  Canonical.decode
    (Canonical.canonicalStateCodec machine stateCoverage)
    (Canonical.takeBits
      (Canonical.StateWidth machine)
      (decodeProgramAfterInitial machine bits))

decodeProgramRules :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  CNF.Bits (StaticProgramBitsWidth machine) →
  List
    (Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
decodeProgramRules machine stateCoverage symbolCoverage bits =
  decodeRuleList
    stateCoverage symbolCoverage
    (Canonical.listLength (Local.rules machine))
    (Canonical.dropBits
      (Canonical.StateWidth machine)
      (decodeProgramAfterInitial machine bits))

------------------------------------------------------------------------
-- Same-object round trips for the actual machine data.
------------------------------------------------------------------------

decodeStaticProgramBlank :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  decodeProgramBlank
    machine stateCoverage symbolCoverage
    (encodeStaticProgram machine stateCoverage symbolCoverage)
  ≡ Local.blank machine
decodeStaticProgramBlank machine stateCoverage symbolCoverage
    rewrite
      Canonical.takeAppendBits
        (Canonical.encode
          (Canonical.canonicalSymbolCodec machine symbolCoverage)
          (Local.blank machine))
        (Canonical.appendBits
          (Canonical.encode
            (Canonical.canonicalStateCodec machine stateCoverage)
            (Local.initialState machine))
          (Canonical.appendBits
            (Canonical.encode
              (Canonical.canonicalStateCodec machine stateCoverage)
              (Local.acceptingState machine))
            (encodeRuleList
              stateCoverage symbolCoverage
              (Local.rules machine))))
      |
      Canonical.decodeEncode
        (Canonical.canonicalSymbolCodec machine symbolCoverage)
        (Local.blank machine) =
  refl

decodeStaticProgramInitial :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  decodeProgramInitialState
    machine stateCoverage symbolCoverage
    (encodeStaticProgram machine stateCoverage symbolCoverage)
  ≡ Local.initialState machine
decodeStaticProgramInitial machine stateCoverage symbolCoverage
    rewrite
      Canonical.dropAppendBits
        (Canonical.encode
          (Canonical.canonicalSymbolCodec machine symbolCoverage)
          (Local.blank machine))
        (Canonical.appendBits
          (Canonical.encode
            (Canonical.canonicalStateCodec machine stateCoverage)
            (Local.initialState machine))
          (Canonical.appendBits
            (Canonical.encode
              (Canonical.canonicalStateCodec machine stateCoverage)
              (Local.acceptingState machine))
            (encodeRuleList
              stateCoverage symbolCoverage
              (Local.rules machine))))
      |
      Canonical.takeAppendBits
        (Canonical.encode
          (Canonical.canonicalStateCodec machine stateCoverage)
          (Local.initialState machine))
        (Canonical.appendBits
          (Canonical.encode
            (Canonical.canonicalStateCodec machine stateCoverage)
            (Local.acceptingState machine))
          (encodeRuleList
            stateCoverage symbolCoverage
            (Local.rules machine)))
      |
      Canonical.decodeEncode
        (Canonical.canonicalStateCodec machine stateCoverage)
        (Local.initialState machine) =
  refl

decodeStaticProgramAccepting :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  decodeProgramAcceptingState
    machine stateCoverage symbolCoverage
    (encodeStaticProgram machine stateCoverage symbolCoverage)
  ≡ Local.acceptingState machine
decodeStaticProgramAccepting machine stateCoverage symbolCoverage
    rewrite
      Canonical.dropAppendBits
        (Canonical.encode
          (Canonical.canonicalSymbolCodec machine symbolCoverage)
          (Local.blank machine))
        (Canonical.appendBits
          (Canonical.encode
            (Canonical.canonicalStateCodec machine stateCoverage)
            (Local.initialState machine))
          (Canonical.appendBits
            (Canonical.encode
              (Canonical.canonicalStateCodec machine stateCoverage)
              (Local.acceptingState machine))
            (encodeRuleList
              stateCoverage symbolCoverage
              (Local.rules machine))))
      |
      Canonical.dropAppendBits
        (Canonical.encode
          (Canonical.canonicalStateCodec machine stateCoverage)
          (Local.initialState machine))
        (Canonical.appendBits
          (Canonical.encode
            (Canonical.canonicalStateCodec machine stateCoverage)
            (Local.acceptingState machine))
          (encodeRuleList
            stateCoverage symbolCoverage
            (Local.rules machine)))
      |
      Canonical.takeAppendBits
        (Canonical.encode
          (Canonical.canonicalStateCodec machine stateCoverage)
          (Local.acceptingState machine))
        (encodeRuleList
          stateCoverage symbolCoverage
          (Local.rules machine))
      |
      Canonical.decodeEncode
        (Canonical.canonicalStateCodec machine stateCoverage)
        (Local.acceptingState machine) =
  refl

decodeStaticProgramRules :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  decodeProgramRules
    machine stateCoverage symbolCoverage
    (encodeStaticProgram machine stateCoverage symbolCoverage)
  ≡ Local.rules machine
decodeStaticProgramRules machine stateCoverage symbolCoverage
    rewrite
      Canonical.dropAppendBits
        (Canonical.encode
          (Canonical.canonicalSymbolCodec machine symbolCoverage)
          (Local.blank machine))
        (Canonical.appendBits
          (Canonical.encode
            (Canonical.canonicalStateCodec machine stateCoverage)
            (Local.initialState machine))
          (Canonical.appendBits
            (Canonical.encode
              (Canonical.canonicalStateCodec machine stateCoverage)
              (Local.acceptingState machine))
            (encodeRuleList
              stateCoverage symbolCoverage
              (Local.rules machine))))
      |
      Canonical.dropAppendBits
        (Canonical.encode
          (Canonical.canonicalStateCodec machine stateCoverage)
          (Local.initialState machine))
        (Canonical.appendBits
          (Canonical.encode
            (Canonical.canonicalStateCodec machine stateCoverage)
            (Local.acceptingState machine))
          (encodeRuleList
            stateCoverage symbolCoverage
            (Local.rules machine)))
      |
      Canonical.dropAppendBits
        (Canonical.encode
          (Canonical.canonicalStateCodec machine stateCoverage)
          (Local.acceptingState machine))
        (encodeRuleList
          stateCoverage symbolCoverage
          (Local.rules machine))
      |
      decodeEncodeRuleList
        stateCoverage symbolCoverage
        (Local.rules machine) =
  refl
