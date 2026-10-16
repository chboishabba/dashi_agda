module DASHI.Mathematics.Complexity.CodedFiniteStaticBitLookupExact where

------------------------------------------------------------------------
-- FIXED-DESCRIPTION BOOLEAN ANSWER STREAM -> LITERAL FINITE LOOKUP MACHINE
--
-- Given a compile-time table
--
--     table : Fin (n+1) -> Bool,
--
-- reuse the literal unary cursor.  Each cursor phase gets exactly one fresh
-- stop rule:
--
--     cursorPhase(i), stop
--       -> terminalPhase, encoded(table i), Stay.
--
-- Resident cursor rules read only `more`, while these added rules read only
-- `stop`, so the full rule table remains deterministic.  The emitted answer is
-- static program data; no runtime higher-order table lookup is introduced.
--
-- This is the first literal fixed-description generator compiler.  It does not
-- yet prove that the chosen finite table is extensionally identical to every
-- bit of the full guarded Cook formula; that same-object table-population weld
-- is the next generator payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkExtensionExact as Link
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact as Phase
import DASHI.Mathematics.Complexity.CodedFiniteUnaryCursorExact as Cursor

------------------------------------------------------------------------
-- 1. Output encoding on the cursor alphabet.
------------------------------------------------------------------------

outputSymbol : Bool → Fin.Fin 3
outputSymbol false = Cursor.blankSymbol
outputSymbol true = Cursor.moreSymbol

stopRuleAt :
  ∀ {n : Nat} →
  (table : Fin.Fin (suc n) → Bool) →
  Fin.Fin (suc n) →
  Local.TapeRule
    (Fin.Fin (Mode.stateCount (Cursor.cursorFragment n)))
    (Fin.Fin 3)
stopRuleAt {n} table phase =
  Local.tape-rule
    (Cursor.cursorState n phase)
    Cursor.stopSymbol
    (Cursor.cursorState n (Phase.lastPhase n))
    (outputSymbol (table phase))
    Local.stayPut

------------------------------------------------------------------------
-- 2. Compile one stop/output rule per selected phase.
------------------------------------------------------------------------

stopRules :
  ∀ {n : Nat} →
  (table : Fin.Fin (suc n) → Bool) →
  List (Fin.Fin (suc n)) →
  List
    (Local.TapeRule
      (Fin.Fin (Mode.stateCount (Cursor.cursorFragment n)))
      (Fin.Fin 3))
stopRules table [] = []
stopRules table (phase ∷ phases) =
  stopRuleAt table phase ∷ stopRules table phases

stopRuleOccursFromMember :
  ∀ {n : Nat}
    {table : Fin.Fin (suc n) → Bool}
    {phase : Fin.Fin (suc n)}
    {phases : List (Fin.Fin (suc n))} →
  Canonical.Member phase phases →
  Local.RuleOccurs (stopRuleAt table phase) (stopRules table phases)
stopRuleOccursFromMember Canonical.here = Local.ruleHere
stopRuleOccursFromMember (Canonical.there member) =
  Local.ruleThere (stopRuleOccursFromMember member)

stopRulePreimage :
  ∀ {n : Nat}
    (table : Fin.Fin (suc n) → Bool)
    {wanted : Local.TapeRule
      (Fin.Fin (Mode.stateCount (Cursor.cursorFragment n)))
      (Fin.Fin 3)}
    {phases : List (Fin.Fin (suc n))} →
  Local.RuleOccurs wanted (stopRules table phases) →
  Σ (Fin.Fin (suc n)) λ phase →
    Σ (Canonical.Member phase phases) λ _ →
      wanted ≡ stopRuleAt table phase
stopRulePreimage table {phases = []} ()
stopRulePreimage table {phases = phase ∷ phases} Local.ruleHere =
  phase , Canonical.here , refl
stopRulePreimage table {phases = phase ∷ phases} (Local.ruleThere occurs)
  with stopRulePreimage table occurs
... | found , member , exact =
  found , Canonical.there member , exact

------------------------------------------------------------------------
-- 3. Output-link determinism.
------------------------------------------------------------------------

stopRulesUnique :
  ∀ {n : Nat}
    (table : Fin.Fin (suc n) → Bool)
    (phases : List (Fin.Fin (suc n))) →
  Link.RuleTableUnique (stopRules table phases)
stopRulesUnique table phases leftOccurs rightOccurs sourceEq readEq
  with stopRulePreimage table leftOccurs
     | stopRulePreimage table rightOccurs
... | leftPhase , leftMember , refl
    | rightPhase , rightMember , refl
  with Phase.combineSecondInjective sourceEq
... | refl = refl

------------------------------------------------------------------------
-- 4. Resident cursor rules and stop/output rules are key-disjoint.
------------------------------------------------------------------------

cursorStopRulesDisjoint :
  ∀ {n : Nat}
    (table : Fin.Fin (suc n) → Bool)
    (phases : List (Fin.Fin (suc n))) →
  Link.RuleKeyDisjoint
    (Mode.rules (Cursor.cursorFragment n))
    (stopRules table phases)
cursorStopRulesDisjoint table phases residentOccurs stopOccurs sourceEq readEq
  with stopRulePreimage table stopOccurs
... | phase , member , refl =
  Cursor.cursorStopKeyFresh n phase residentOccurs sourceEq readEq

------------------------------------------------------------------------
-- 5. Literal safe-link extension and closed code.
------------------------------------------------------------------------

staticLookupExtension :
  ∀ {n : Nat} →
  (table : Fin.Fin (suc n) → Bool) →
  Link.SafeLinkExtension (Cursor.cursorFragment n)
staticLookupExtension {n} table = record
  { Link.links = stopRules table (Coded.allFin (suc n))
  ; Link.linksUnique = stopRulesUnique table (Coded.allFin (suc n))
  ; Link.residentLinkKeyDisjoint =
      cursorStopRulesDisjoint table (Coded.allFin (suc n))
  }

staticLookupFragment :
  ∀ {n : Nat} →
  (table : Fin.Fin (suc n) → Bool) →
  Mode.CodedModeFragment 3
staticLookupFragment table =
  Link.extendFragmentWithLinks (staticLookupExtension table)

staticLookupCode :
  ∀ {n : Nat} →
  (table : Fin.Fin (suc n) → Bool) →
  Coded.CodedFiniteStandardTM
staticLookupCode {n} table =
  Mode.closeFragment
    (staticLookupFragment table)
    Cursor.blankSymbol
    (Cursor.cursorState n Fin.zero)
    (Cursor.cursorState n (Phase.lastPhase n))

------------------------------------------------------------------------
-- 6. Every phase's literal stop/output rule occurs and has exact payload.
------------------------------------------------------------------------

stopRuleAtOccurs :
  ∀ {n : Nat}
    (table : Fin.Fin (suc n) → Bool)
    (phase : Fin.Fin (suc n)) →
  Local.RuleOccurs
    (stopRuleAt table phase)
    (Link.links (staticLookupExtension table))
stopRuleAtOccurs {n} table phase =
  stopRuleOccursFromMember (Coded.allFinMember phase)

stopRuleWritesTableBit :
  ∀ {n : Nat}
    (table : Fin.Fin (suc n) → Bool)
    (phase : Fin.Fin (suc n)) →
  Local.writeSymbol (stopRuleAt table phase)
  ≡ outputSymbol (table phase)
stopRuleWritesTableBit table phase = refl

stopRuleTargetsTerminal :
  ∀ {n : Nat}
    (table : Fin.Fin (suc n) → Bool)
    (phase : Fin.Fin (suc n)) →
  Local.targetState (stopRuleAt table phase)
  ≡ Cursor.cursorState n (Phase.lastPhase n)
stopRuleTargetsTerminal table phase = refl

stopRuleReadsStop :
  ∀ {n : Nat}
    (table : Fin.Fin (suc n) → Bool)
    (phase : Fin.Fin (suc n)) →
  Local.readSymbol (stopRuleAt table phase) ≡ Cursor.stopSymbol
stopRuleReadsStop table phase = refl

------------------------------------------------------------------------
-- 7. Max-cut boundary.
------------------------------------------------------------------------

record StaticBitLookupBoundary : Set where
  constructor static-bit-lookup-boundary
  field
    unaryCursorLiteralMachinePaid : Bool
    oneStopRulePerCompileTimeIndexPaid : Bool
    outputBitLiteralRulePayloadPaid : Bool
    cursorStopDispatchDisjointPaid : Bool
    lookupTerminalQuiescentPaid : Bool
    arbitraryRuntimePredicateCallRequired : Bool
    fullGuardedCookTablePopulationStillRequired : Bool
    exactLookupRunTheoremStillRequired : Bool

open StaticBitLookupBoundary public

canonicalStaticBitLookupBoundary : StaticBitLookupBoundary
canonicalStaticBitLookupBoundary =
  static-bit-lookup-boundary
    true true true true true false true true

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- A fixed finite answer stream can now be compiled into literal finite standard
-- syntax over the paid unary cursor.  Runtime performs no higher-order lookup:
-- it consumes `more^i ; stop`, then executes the unique phase-specific stop rule
-- carrying the precompiled answer bit.  Remaining generator work is to populate
-- this table from the SAME guarded Cook description and prove the exact run /
-- semantic correspondence to the existing costed streamed evaluator.
------------------------------------------------------------------------
