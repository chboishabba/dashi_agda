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

------------------------------------------------------------------------
-- Every program tree has a leftmost primitive machine.  The Kleene fixed point
-- generated from one primitive body recovers that exact body machine.
------------------------------------------------------------------------

headMachine :
  Code.Program Coded.CodedFiniteStandardTM →
  Coded.CodedFiniteStandardTM
headMachine (Code.primitive machine) = machine
headMachine (Code.specialized program static) = headMachine program
headMachine (Code.diagonalized program) = headMachine program

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

codedFixedPointHeadMachineExact :
  (machine : Coded.CodedFiniteStandardTM) →
  headMachine (codedQuoteSensitiveFixedPoint machine) ≡ machine
codedFixedPointHeadMachineExact machine = refl

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
-- The fixed-point quotation also recovers the exact primitive machine by
-- definition.  The remaining Clay-critical step is to use that recovered same
-- machine to drive guarded-Cook streaming in an ordinary finite TM execution.
------------------------------------------------------------------------
