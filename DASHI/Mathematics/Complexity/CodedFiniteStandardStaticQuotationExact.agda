module DASHI.Mathematics.Complexity.CodedFiniteStandardStaticQuotationExact where

------------------------------------------------------------------------
-- LITERAL STATIC QUOTATION FOR THE LOW-UNIVERSE CODED STANDARD MACHINE
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact as Program

codedConcreteMachine :
  Coded.CodedFiniteStandardTM →
  Local.ConcreteTapeMachine
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

bitsToList :
  ∀ {n : Nat} →
  CNF.Bits n →
  List Bool
bitsToList CNF.[]ᵇ = []
bitsToList (bit CNF.∷ᵇ rest) =
  bit ∷ bitsToList rest

codedStaticProgramList :
  Coded.CodedFiniteStandardTM →
  List Bool
codedStaticProgramList code =
  bitsToList (codedStaticProgramBits code)

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
-- Every actual `CodedFiniteStandardTM` now has one literal fixed-width static
-- quotation using the repository's existing concrete serializer.  Both the
-- indexed `Bits` value and its ordinary finite Boolean-list payload are exposed.
-- Decoding the indexed quotation returns the canonical view of the same machine.
-- No universal interpreter or execution theorem is manufactured here.
------------------------------------------------------------------------
