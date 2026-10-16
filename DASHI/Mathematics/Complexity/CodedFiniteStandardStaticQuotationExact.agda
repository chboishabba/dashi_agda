module DASHI.Mathematics.Complexity.CodedFiniteStandardStaticQuotationExact where

------------------------------------------------------------------------
-- LITERAL STATIC QUOTATION FOR THE LOW-UNIVERSE CODED STANDARD MACHINE
--
-- `CodedFiniteStandardTM` already owns the finite state/symbol cardinalities and
-- literal transition table.  The older concrete-machine layer already owns a
-- left-invertible fixed-width static program serializer.  This file composes the
-- two SAME objects; it does not introduce another program code.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact as Program

codedConcreteMachine :
  Coded.CodedFiniteStandardTM →
  DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact.ConcreteTapeMachine
codedConcreteMachine code =
  Presented.finitePresentedStandardToConcrete
    (Coded.decodeCodedStandardTM code)

codedStaticProgramWidth :
  Coded.CodedFiniteStandardTM → Nat
codedStaticProgramWidth code =
  Program.StaticProgramBitsWidth (codedConcreteMachine code)

codedStaticProgramBits :
  (code : Coded.CodedFiniteStandardTM) →
  CNF.Bits (codedStaticProgramWidth code)
codedStaticProgramBits code =
  Program.encodeStaticProgram
    (codedConcreteMachine code)
    (Coded.codedStateCoverage code)
    (Coded.codedSymbolCoverage code)

codedStaticProgramViewRoundTrip :
  (code : Coded.CodedFiniteStandardTM) →
  Program.decodeStaticProgramView
    (codedConcreteMachine code)
    (Coded.codedStateCoverage code)
    (Coded.codedSymbolCoverage code)
    (codedStaticProgramBits code)
  ≡
  Program.canonicalStaticProgramView (codedConcreteMachine code)
codedStaticProgramViewRoundTrip code =
  Program.decodeEncodeStaticProgramView
    (codedConcreteMachine code)
    (Coded.codedStateCoverage code)
    (Coded.codedSymbolCoverage code)

------------------------------------------------------------------------
-- MAX-CUT CONSEQUENCE
--
-- The behavioural-self-reference route no longer has a separate machine-code
-- serialization leaf.  Every actual `CodedFiniteStandardTM` has one literal
-- fixed-width static quotation using the already-owned concrete serializer, and
-- decoding that quotation returns the canonical view of the same machine.
--
-- This theorem is intentionally weaker than a universal interpreter.  It pays
-- finite quotation/data identity only; executing an arbitrary quoted code on a
-- standard TM remains a separate compiler theorem.
------------------------------------------------------------------------
