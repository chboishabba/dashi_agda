module DASHI.Mathematics.Complexity.PNotEqualsNPCodedQuoteSensitiveKleeneExact where

------------------------------------------------------------------------
-- CODED STANDARD-TM LEAVES INSIDE THE EXISTING FINITE KLEENE SYNTAX
--
-- The old Q2 primitive erased its quoted-program operand.  That erasure is not
-- forced by the repository's finite specialization/diagonalization syntax.
-- Here the primitive carrier is the ACTUAL low-universe coded standard machine,
-- and the primitive body observes finite data of the quoted syntax itself.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardStaticQuotationExact as StaticQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code

------------------------------------------------------------------------
-- Finite quotation observables.
------------------------------------------------------------------------

quotedSyntaxNodeCount :
  Code.Program Coded.CodedFiniteStandardTM → Nat
quotedSyntaxNodeCount = Code.programSize

quotedMachinePayloadWidth :
  Code.Program Coded.CodedFiniteStandardTM → Nat
quotedMachinePayloadWidth (Code.primitive machine) =
  StaticQuote.codedStaticProgramWidth machine
quotedMachinePayloadWidth (Code.specialized program static) =
  quotedMachinePayloadWidth program + quotedMachinePayloadWidth static
quotedMachinePayloadWidth (Code.diagonalized program) =
  quotedMachinePayloadWidth program

record CodedQuoteObservation : Set where
  constructor coded-quote-observation
  field
    syntaxNodes : Nat
    machinePayloadBits : Nat

open CodedQuoteObservation public

observeQuotedProgram :
  Code.Program Coded.CodedFiniteStandardTM →
  CodedQuoteObservation
observeQuotedProgram quoted =
  coded-quote-observation
    (quotedSyntaxNodeCount quoted)
    (quotedMachinePayloadWidth quoted)

------------------------------------------------------------------------
-- Quote-sensitive primitive semantics.
--
-- Unary primitive execution is intentionally absent: this primitive is the
-- binary body consumed by the Kleene fixed-point construction.
------------------------------------------------------------------------

codedQuoteSensitiveSemantics :
  Code.PrimitiveSemantics
    Coded.CodedFiniteStandardTM
    ⊤
    CodedQuoteObservation
codedQuoteSensitiveSemantics = record
  { Code.runPrimitive1 = λ machine input → nothing
  ; Code.runPrimitive2 = λ machine quoted input →
      just (observeQuotedProgram quoted)
  }

codedQuoteSensitiveFixedPoint :
  Coded.CodedFiniteStandardTM →
  Code.Program Coded.CodedFiniteStandardTM
codedQuoteSensitiveFixedPoint machine =
  Code.primitiveBodyFixedPoint machine

codedFixedPointObservesOwnQuotation :
  (machine : Coded.CodedFiniteStandardTM) →
  Code.run1
    codedQuoteSensitiveSemantics
    (codedQuoteSensitiveFixedPoint machine)
    tt
  ≡
  just
    (observeQuotedProgram
      (codedQuoteSensitiveFixedPoint machine))
codedFixedPointObservesOwnQuotation machine = refl

------------------------------------------------------------------------
-- Exact feedback: the fixed syntax contains two diagonalized copies of the
-- primitive body, so its machine-leaf payload is duplicated exactly.
------------------------------------------------------------------------

codedFixedPointPayloadWidthExact :
  (machine : Coded.CodedFiniteStandardTM) →
  quotedMachinePayloadWidth
    (codedQuoteSensitiveFixedPoint machine)
  ≡
  StaticQuote.codedStaticProgramWidth machine
    + StaticQuote.codedStaticProgramWidth machine
codedFixedPointPayloadWidthExact machine = refl

codedFixedPointSyntaxNodesExact :
  (machine : Coded.CodedFiniteStandardTM) →
  quotedSyntaxNodeCount
    (codedQuoteSensitiveFixedPoint machine)
  ≡ suc (suc (suc zero) + suc (suc zero))
codedFixedPointSyntaxNodesExact machine =
  Code.primitiveBodyFixedPointSize machine

------------------------------------------------------------------------
-- MAX-CUT CONSEQUENCE
--
-- Behavioural self-reference with genuine quote consumption is now inhabited on
-- a finite syntax whose primitive leaves are actual CodedFiniteStandardTM data.
-- Therefore `q2PrimitiveExecutionErasesQuotedProgram` is a property of the old
-- Q2 primitive, not a no-go for the Kleene construction.
--
-- Still unpaid, deliberately:
--   * interpreting the quoted machine/program syntax by an ordinary standard TM;
--   * making the quote-sensitive body stream the guarded Cook behaviour of that
--     exact quoted code rather than merely inspect finite quotation observables;
--   * runtime/program-size closure of that compiled body.
------------------------------------------------------------------------
