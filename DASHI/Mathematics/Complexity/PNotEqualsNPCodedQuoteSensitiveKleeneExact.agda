module DASHI.Mathematics.Complexity.PNotEqualsNPCodedQuoteSensitiveKleeneExact where

------------------------------------------------------------------------
-- CODED STANDARD-TM LEAVES INSIDE THE EXISTING FINITE KLEENE SYNTAX
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardStaticQuotationExact as StaticQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code

append :
  ∀ {A : Set} →
  List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

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

quotedMachinePayload :
  Code.Program Coded.CodedFiniteStandardTM →
  List Bool
quotedMachinePayload (Code.primitive machine) =
  StaticQuote.codedStaticProgramList machine
quotedMachinePayload (Code.specialized program static) =
  append (quotedMachinePayload program) (quotedMachinePayload static)
quotedMachinePayload (Code.diagonalized program) =
  quotedMachinePayload program

record CodedQuoteObservation : Set where
  constructor coded-quote-observation
  field
    syntaxNodes : Nat
    machinePayloadBits : Nat
    literalMachinePayload : List Bool

open CodedQuoteObservation public

observeQuotedProgram :
  Code.Program Coded.CodedFiniteStandardTM →
  CodedQuoteObservation
observeQuotedProgram quoted =
  coded-quote-observation
    (quotedSyntaxNodeCount quoted)
    (quotedMachinePayloadWidth quoted)
    (quotedMachinePayload quoted)

------------------------------------------------------------------------
-- Quote-sensitive primitive semantics.
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
-- primitive body.  Both the width and the literal Boolean payload duplicate.
------------------------------------------------------------------------

codedFixedPointPayloadWidthExact :
  (machine : Coded.CodedFiniteStandardTM) →
  quotedMachinePayloadWidth
    (codedQuoteSensitiveFixedPoint machine)
  ≡
  StaticQuote.codedStaticProgramWidth machine
    + StaticQuote.codedStaticProgramWidth machine
codedFixedPointPayloadWidthExact machine = refl

codedFixedPointLiteralPayloadExact :
  (machine : Coded.CodedFiniteStandardTM) →
  quotedMachinePayload
    (codedQuoteSensitiveFixedPoint machine)
  ≡
  append
    (StaticQuote.codedStaticProgramList machine)
    (StaticQuote.codedStaticProgramList machine)
codedFixedPointLiteralPayloadExact machine = refl

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
-- Behavioural self-reference with genuine quote consumption is inhabited on a
-- finite syntax whose primitive leaves are actual CodedFiniteStandardTM data.
-- The observation now contains the literal static-program Boolean payload, not
-- merely its size.  Thus old-Q2 quote erasure is not intrinsic to Kleene syntax.
--
-- Still unpaid: literal standard-TM execution of this quote-sensitive body and
-- replacement of the diagnostic observation by streamed guarded-Cook behaviour
-- for the exact quoted code.
------------------------------------------------------------------------
