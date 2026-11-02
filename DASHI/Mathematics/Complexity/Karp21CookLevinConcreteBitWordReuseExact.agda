module DASHI.Mathematics.Complexity.Karp21CookLevinConcreteBitWordReuseExact where

------------------------------------------------------------------------
-- K00 DONOR REUSE: actual concrete tape Cook--Levin theorem, actual
-- Cook.BooleanFormula, and EXISTING exact three-bit-per-prefix-token codec.
--
-- This imports the real source owners rather than a hypothetical SAT axiom:
--  * ConcreteTapeCookLevinCookFormulaExact: SAT iff exact accepting run.
--  * PNotEqualsNPCookFormulaBinaryCodecExact: formula bit roundtrip,
--    exact bit count = 3 * original prefix syntax token count.
--  * FiniteWordSizeExact: SAME List Bool bitword carrier as Karp21 N21.
--
-- For every supplied concrete machine, state/symbol coverage, nonempty
-- rule table, input and exact step budget, the *serialized* Cook formula
-- faithfully preserves both directions of the accepting-run theorem.
--
-- Still missing for a complete K00 SAT NP-completeness theorem:
-- (i) universal arbitrary NP machine source-model representation and
--     standard-model resource equivalence;
-- (ii) a concrete binary machine algorithm emitting this word in
--     polynomial time in input length and clock;
-- (iii) one faithful total strict SAT parser for malformed bit words;
-- (iv) an actual machine-cost model instance and reduction clock.
--
-- Original theorem source: Cook (1971); Karp (1972).
-- Original DASHI tape/formula/codec authorship remains in those files.
-- No new Monster VOA, Fock, grade-character or unrelated source oracle.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Bits
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix
import DASHI.Mathematics.Complexity.Karp21CookStrictTripleBitBoundaryExact as Strict
import Data.Maybe.Base as Maybe
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Tape
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Rules
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinExactBudgetIff as Runs
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinCookFormulaExact as CL

-- The exact same word type as the N21 certificate and the repository's
-- finite Boolean-word size model: no hidden new encoding carrier.
SerializedSATWord : Set
SerializedSATWord = Word.BitWord

guardedCookLevinBitWord :
  ∀ {machine : Tape.ConcreteTapeMachine}
    (states : Canonical.EnumerationCoverage (Tape.finiteState machine))
    (symbols : Canonical.EnumerationCoverage (Tape.finiteSymbol machine))
    (nonempty : Rules.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  SerializedSATWord
guardedCookLevinBitWord states symbols nonempty input steps =
  Bits.encodeFormulaBits
    (CL.guardedCookFormula states symbols nonempty input steps)

-- Exact typed source ↔ bitword sameness, not mere character or syntax
-- token-count agreement.
guardedBitWordDecodesToActualCookFormula :
  ∀ {machine : Tape.ConcreteTapeMachine}
    (states : Canonical.EnumerationCoverage (Tape.finiteState machine))
    (symbols : Canonical.EnumerationCoverage (Tape.finiteSymbol machine))
    (nonempty : Rules.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Bits.decodeFormulaBits
    (guardedCookLevinBitWord states symbols nonempty input steps)
  ≡ CL.guardedCookFormula states symbols nonempty input steps
guardedBitWordDecodesToActualCookFormula states symbols nonempty input steps =
  Bits.decodeEncodeFormulaBits
    (CL.guardedCookFormula states symbols nonempty input steps)

-- Full local SAT → exact accepting-run direction on a real bit word,
-- reusing the existing theorem, not a Boolean oracle.
serializedCookSATToExactAcceptingRun :
  ∀ {machine : Tape.ConcreteTapeMachine}
    (states : Canonical.EnumerationCoverage (Tape.finiteState machine))
    (symbols : Canonical.EnumerationCoverage (Tape.finiteSymbol machine))
    (nonempty : Rules.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Cook.Satisfiable
    (Bits.decodeFormulaBits
      (guardedCookLevinBitWord states symbols nonempty input steps))
  → Runs.ExactBudgetAcceptingRun input steps
serializedCookSATToExactAcceptingRun states symbols nonempty input steps
  rewrite guardedBitWordDecodesToActualCookFormula
    states symbols nonempty input steps =
  CL.cookSatisfiableToExactBudgetRun
    states symbols nonempty input steps

-- Full exact accepting-run → SAT bitword direction on the SAME machine,
-- input, time budget and formula, with no empirical predicate involved.
exactAcceptingRunToSerializedCookSAT :
  ∀ {machine : Tape.ConcreteTapeMachine}
    (states : Canonical.EnumerationCoverage (Tape.finiteState machine))
    (symbols : Canonical.EnumerationCoverage (Tape.finiteSymbol machine))
    (nonempty : Rules.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Runs.ExactBudgetAcceptingRun input steps →
  Cook.Satisfiable
    (Bits.decodeFormulaBits
      (guardedCookLevinBitWord states symbols nonempty input steps))
exactAcceptingRunToSerializedCookSAT states symbols nonempty input steps
  rewrite guardedBitWordDecodesToActualCookFormula
    states symbols nonempty input steps =
  CL.exactBudgetRunToCookSatisfiable
    states symbols nonempty input steps

-- TWO pre-existing List-length definitions, one actual word metric:
-- pay their extensional equality explicitly instead of assuming it
-- judgmentally for an abstract formula expression.
wordLengthMatchesCookCodecLength :
  (word : List Bool) →
  Word.encodingSize word ≡ Bits.listLength word
wordLengthMatchesCookCodecLength [] = refl
wordLengthMatchesCookCodecLength (bit ∷ bits) =
  cong (λ length → suc length)
    (wordLengthMatchesCookCodecLength bits)

-- Exact encoded bit-size identity inherited from the PREVIOUS codec:
-- unlike a source-language theorem, this does NOT prove that the
-- tape machine computes the encoding in polynomial bit time.
serializedCookFormulaWordLength :
  ∀ {machine : Tape.ConcreteTapeMachine}
    (states : Canonical.EnumerationCoverage (Tape.finiteState machine))
    (symbols : Canonical.EnumerationCoverage (Tape.finiteSymbol machine))
    (nonempty : Rules.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Word.encodingSize
    (guardedCookLevinBitWord states symbols nonempty input steps)
  ≡ 3 * Prefix.cookFormulaTokenCount
      (CL.guardedCookFormula states symbols nonempty input steps)
serializedCookFormulaWordLength states symbols nonempty input steps =
  trans
    (wordLengthMatchesCookCodecLength
      (guardedCookLevinBitWord states symbols nonempty input steps))
    (Bits.formulaBitCodeLengthExact
      (CL.guardedCookFormula states symbols nonempty input steps))


------------------------------------------------------------------------
-- The actual Cook--Levin output also passes the new strict 3-bit
-- token parser (as distinct from the legacy tail-dropping decoder).
------------------------------------------------------------------------

strictSerializedCookWordTokenParse :
  ∀ {machine : Tape.ConcreteTapeMachine}
    (states : Canonical.EnumerationCoverage (Tape.finiteState machine))
    (symbols : Canonical.EnumerationCoverage (Tape.finiteSymbol machine))
    (nonempty : Rules.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Strict.strictDecodeThreeTokens
    (guardedCookLevinBitWord states symbols nonempty input steps)
  ≡ Maybe.just (Prefix.encodeCookFormula
      (CL.guardedCookFormula states symbols nonempty input steps))
strictSerializedCookWordTokenParse states symbols nonempty input steps =
  Strict.strictCookFormulaTokenRoundTrip
    (CL.guardedCookFormula states symbols nonempty input steps)

