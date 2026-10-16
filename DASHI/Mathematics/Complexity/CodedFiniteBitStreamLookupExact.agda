module DASHI.Mathematics.Complexity.CodedFiniteBitStreamLookupExact where

------------------------------------------------------------------------
-- FIXED FINITE BITSTREAM -> LITERAL UNARY-INDEX CODED STANDARD TM
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkExtensionExact as Link
import DASHI.Mathematics.Complexity.CodedFiniteUnaryCursorExact as Cursor
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact as Phase

------------------------------------------------------------------------
-- Three quiescent output controls.
------------------------------------------------------------------------

sinkFragment : Mode.CodedModeFragment 3
sinkFragment = record
  { Mode.stateCount = 3
  ; Mode.rules = []
  ; Mode.dispatchUnique = λ ()
  }

baseFragment : Nat → Mode.CodedModeFragment 3
baseFragment n = Mode.sumFragments (Cursor.cursorFragment n) sinkFragment

cursorInBase :
  (n : Nat) → Fin.Fin (suc n) → Fin.Fin (Mode.stateCount (baseFragment n))
cursorInBase n phase = Mode.embedLeft (Cursor.cursorState n phase)

trueSink : (n : Nat) → Fin.Fin (Mode.stateCount (baseFragment n))
trueSink n = Mode.embedRight {m = Mode.stateCount (Cursor.cursorFragment n)} Fin.zero

falseSink : (n : Nat) → Fin.Fin (Mode.stateCount (baseFragment n))
falseSink n =
  Mode.embedRight {m = Mode.stateCount (Cursor.cursorFragment n)}
    (Fin.suc Fin.zero)

noneSink : (n : Nat) → Fin.Fin (Mode.stateCount (baseFragment n))
noneSink n =
  Mode.embedRight {m = Mode.stateCount (Cursor.cursorFragment n)}
    (Fin.suc (Fin.suc Fin.zero))

bitSink : (n : Nat) → Bool → Fin.Fin (Mode.stateCount (baseFragment n))
bitSink n false = falseSink n
bitSink n true = trueSink n

------------------------------------------------------------------------
-- One stop-link origin for every valid phase plus one overflow origin.
------------------------------------------------------------------------

data StopOrigin (n : Nat) : Set where
  valid : Fin.Fin n → StopOrigin n
  overflow : StopOrigin n

originSource :
  (n : Nat) → StopOrigin n → Fin.Fin (Mode.stateCount (baseFragment n))
originSource n (valid phase) = cursorInBase n (Phase.raisePhase phase)
originSource n overflow = cursorInBase n (Phase.lastPhase n)

originTarget :
  (n : Nat) → (Fin.Fin n → Bool) → StopOrigin n →
  Fin.Fin (Mode.stateCount (baseFragment n))
originTarget n bits (valid phase) = bitSink n (bits phase)
originTarget n bits overflow = noneSink n

stopRule :
  (n : Nat) → (Fin.Fin n → Bool) → StopOrigin n →
  Local.TapeRule
    (Fin.Fin (Mode.stateCount (baseFragment n)))
    (Fin.Fin 3)
stopRule n bits origin =
  Local.tape-rule
    (originSource n origin)
    Cursor.stopSymbol
    (originTarget n bits origin)
    Cursor.stopSymbol
    Local.stayPut

mapValidOrigins : ∀ {n : Nat} → List (Fin.Fin n) → List (StopOrigin n)
mapValidOrigins [] = []
mapValidOrigins (phase ∷ rest) = valid phase ∷ mapValidOrigins rest

origins : (n : Nat) → List (StopOrigin n)
origins n = Mode.append (mapValidOrigins (Coded.allFin n)) (overflow ∷ [])

mapStopRules :
  ∀ {n : Nat} →
  (Fin.Fin n → Bool) →
  List (StopOrigin n) →
  List (Local.TapeRule (Fin.Fin (Mode.stateCount (baseFragment n))) (Fin.Fin 3))
mapStopRules bits [] = []
mapStopRules {n} bits (origin ∷ rest) =
  stopRule n bits origin ∷ mapStopRules bits rest

stopRules :
  (n : Nat) → (Fin.Fin n → Bool) →
  List (Local.TapeRule (Fin.Fin (Mode.stateCount (baseFragment n))) (Fin.Fin 3))
stopRules n bits = mapStopRules bits (origins n)

------------------------------------------------------------------------
-- Forward occurrence constructors.
------------------------------------------------------------------------

mapValidOriginMember :
  ∀ {n : Nat} {phase : Fin.Fin n} {phases : List (Fin.Fin n)} →
  Canonical.Member phase phases →
  Canonical.Member (valid phase) (mapValidOrigins phases)
mapValidOriginMember Canonical.here = Canonical.here
mapValidOriginMember (Canonical.there member) =
  Canonical.there (mapValidOriginMember member)

memberLeftAppend :
  ∀ {A : Set} {x : A} {left right : List A} →
  Canonical.Member x left →
  Canonical.Member x (Mode.append left right)
memberLeftAppend Canonical.here = Canonical.here
memberLeftAppend (Canonical.there member) =
  Canonical.there (memberLeftAppend member)

memberRightAppend :
  ∀ {A : Set} {x : A}
    (left : List A) {right : List A} →
  Canonical.Member x right →
  Canonical.Member x (Mode.append left right)
memberRightAppend [] member = member
memberRightAppend (_ ∷ left) member =
  Canonical.there (memberRightAppend left member)

validOriginMember :
  ∀ {n : Nat} (phase : Fin.Fin n) →
  Canonical.Member (valid phase) (origins n)
validOriginMember phase =
  memberLeftAppend
    (mapValidOriginMember (Coded.allFinMember phase))

overflowOriginMember :
  (n : Nat) → Canonical.Member overflow (origins n)
overflowOriginMember n =
  memberRightAppend
    (mapValidOrigins (Coded.allFin n))
    Canonical.here

mapStopRuleOccurs :
  ∀ {n : Nat} {bits : Fin.Fin n → Bool}
    {origin : StopOrigin n} {source : List (StopOrigin n)} →
  Canonical.Member origin source →
  Local.RuleOccurs (stopRule n bits origin) (mapStopRules bits source)
mapStopRuleOccurs Canonical.here = Local.ruleHere
mapStopRuleOccurs (Canonical.there member) =
  Local.ruleThere (mapStopRuleOccurs member)

validStopRuleOccurs :
  ∀ {n : Nat} (bits : Fin.Fin n → Bool) (phase : Fin.Fin n) →
  Local.RuleOccurs (stopRule n bits (valid phase)) (stopRules n bits)
validStopRuleOccurs bits phase =
  mapStopRuleOccurs (validOriginMember phase)

overflowStopRuleOccurs :
  ∀ {n : Nat} (bits : Fin.Fin n → Bool) →
  Local.RuleOccurs (stopRule n bits overflow) (stopRules n bits)
overflowStopRuleOccurs {n} bits =
  mapStopRuleOccurs (overflowOriginMember n)

------------------------------------------------------------------------
-- Inversion and determinism.
------------------------------------------------------------------------

stopRulePreimage :
  ∀ {n : Nat} {bits : Fin.Fin n → Bool}
    {wanted : Local.TapeRule (Fin.Fin (Mode.stateCount (baseFragment n))) (Fin.Fin 3)}
    {source : List (StopOrigin n)} →
  Local.RuleOccurs wanted (mapStopRules bits source) →
  Σ (StopOrigin n) λ origin → wanted ≡ stopRule n bits origin
stopRulePreimage {source = []} ()
stopRulePreimage {source = origin ∷ rest} Local.ruleHere = origin , refl
stopRulePreimage {source = origin ∷ rest} (Local.ruleThere occurs)
  with stopRulePreimage occurs
... | found , exact = found , exact

cursorInBaseInjective :
  ∀ {n : Nat} {left right : Fin.Fin (suc n)} →
  cursorInBase n left ≡ cursorInBase n right → left ≡ right
cursorInBaseInjective equality =
  Phase.combineSecondInjective (Mode.embedLeftInjective equality)

originSourceInjective :
  ∀ {n : Nat} {left right : StopOrigin n} →
  originSource n left ≡ originSource n right → left ≡ right
originSourceInjective {left = valid left} {valid right} equality =
  cong valid (Phase.raisePhaseInjective (cursorInBaseInjective equality))
originSourceInjective {left = valid left} {overflow} equality =
  ⊥-elim (Phase.raisePhaseNotLast left (cursorInBaseInjective equality))
originSourceInjective {left = overflow} {valid right} equality =
  ⊥-elim
    (Phase.raisePhaseNotLast right (cursorInBaseInjective (sym equality)))
originSourceInjective {left = overflow} {overflow} equality = refl

stopRulesUnique :
  (n : Nat) → (bits : Fin.Fin n → Bool) →
  Link.RuleTableUnique (stopRules n bits)
stopRulesUnique n bits leftOccurs rightOccurs sourceEq readEq
  with stopRulePreimage leftOccurs | stopRulePreimage rightOccurs
... | leftOrigin , refl | rightOrigin , refl
  with originSourceInjective sourceEq
... | refl = refl

stopRuleReadsStop :
  ∀ {n : Nat} {bits : Fin.Fin n → Bool} {rule} →
  Local.RuleOccurs rule (stopRules n bits) →
  Local.readSymbol rule ≡ Cursor.stopSymbol
stopRuleReadsStop occurs
  with stopRulePreimage occurs
... | origin , refl = refl

------------------------------------------------------------------------
-- Resident cursor table and stop-link table are disjoint by read symbol.
------------------------------------------------------------------------

residentCursorPreimage :
  ∀ {n : Nat} {resident} →
  Local.RuleOccurs resident (Mode.rules (baseFragment n)) →
  Σ (Local.TapeRule
      (Fin.Fin (Mode.stateCount (Cursor.cursorFragment n)))
      (Fin.Fin 3)) λ original →
    Local.RuleOccurs original (Mode.rules (Cursor.cursorFragment n))
    × resident ≡ Mode.mapStateRule Mode.embedLeft original
residentCursorPreimage {n} residentOccurs
  with Mode.splitAppendOccurrence
    (Mode.mapRules Mode.embedLeft (Mode.rules (Cursor.cursorFragment n)))
    (Mode.mapRules Mode.embedRight (Mode.rules sinkFragment))
    residentOccurs
... | Mode.occursLeft leftOccurs =
  Mode.mappedRulePreimage Mode.embedLeft leftOccurs
... | Mode.occursRight ()

residentStopDisjoint :
  (n : Nat) → (bits : Fin.Fin n → Bool) →
  Link.RuleKeyDisjoint (Mode.rules (baseFragment n)) (stopRules n bits)
residentStopDisjoint n bits residentOccurs linkOccurs sourceEq readEq
  with residentCursorPreimage residentOccurs
... | original , originalOccurs , residentExact
  rewrite residentExact
        | Cursor.cursorResidentReadsMore n originalOccurs
        | stopRuleReadsStop linkOccurs =
  Cursor.moreNotStop readEq

bitStreamExtension :
  (n : Nat) → (bits : Fin.Fin n → Bool) →
  Link.SafeLinkExtension (baseFragment n)
bitStreamExtension n bits = record
  { Link.links = stopRules n bits
  ; Link.linksUnique = stopRulesUnique n bits
  ; Link.residentLinkKeyDisjoint = residentStopDisjoint n bits
  }

lookupFragment :
  (n : Nat) → (Fin.Fin n → Bool) → Mode.CodedModeFragment 3
lookupFragment n bits =
  Link.extendFragmentWithLinks (bitStreamExtension n bits)

lookupCode :
  (n : Nat) → (Fin.Fin n → Bool) → Coded.CodedFiniteStandardTM
lookupCode n bits =
  Mode.closeFragment
    (lookupFragment n bits)
    Cursor.blankSymbol
    (cursorInBase n Fin.zero)
    (trueSink n)

lookupFalseState :
  (n : Nat) → (bits : Fin.Fin n → Bool) →
  Fin.Fin (Coded.stateCount (lookupCode n bits))
lookupFalseState n bits = falseSink n

lookupNoneState :
  (n : Nat) → (bits : Fin.Fin n → Bool) →
  Fin.Fin (Coded.stateCount (lookupCode n bits))
lookupNoneState n bits = noneSink n

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Fixed finite random access is actual finite rule-table syntax. No Agda
-- function is called at runtime: `bits` is compiled into literal stop-link
-- target controls. Named membership witnesses now expose every valid and
-- overflow output rule to the ordinary first-match transition theorem.
------------------------------------------------------------------------
