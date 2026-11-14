module DASHI.Mathematics.Complexity.CodedStandardFormulaInputNonblankExact where

------------------------------------------------------------------------
-- EVERY CODED FORMULA INPUT BIT IS A NONBLANK TAPE SYMBOL
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (zero; suc)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact as Decider
import DASHI.Mathematics.Complexity.ConcreteTapeGuardedNonblankExact as GuardedNonblank
import DASHI.Mathematics.Complexity.ConcreteTapeNonblankWriteBoundExact as Nonblank
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary

mappedBitsNonblankCountExact :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Decider.CodedStandardPolynomialDecider decider)
    (bits : List Bool) →
  Nonblank.nonblankCount
    (Coded.canonicalFinEnumeration
      (Coded.symbolCount (Decider.code witness)))
    (Coded.blank (Decider.code witness))
    (Decider.mapFormulaBits
      (Decider.zeroSymbol witness)
      (Decider.oneSymbol witness)
      bits)
  ≡ Binary.listLength bits
mappedBitsNonblankCountExact witness [] = refl
mappedBitsNonblankCountExact witness (false ∷ bits)
  rewrite GuardedNonblank.nonblankBitOneFromDistinct
            (Coded.canonicalFinEnumeration
              (Coded.symbolCount (Decider.code witness)))
            (Coded.blank (Decider.code witness))
            (Decider.zeroSymbol witness)
            (Decider.zeroSymbolNotBlank witness)
        | mappedBitsNonblankCountExact witness bits =
  refl
mappedBitsNonblankCountExact witness (true ∷ bits)
  rewrite GuardedNonblank.nonblankBitOneFromDistinct
            (Coded.canonicalFinEnumeration
              (Coded.symbolCount (Decider.code witness)))
            (Coded.blank (Decider.code witness))
            (Decider.oneSymbol witness)
            (Decider.oneSymbolNotBlank witness)
        | mappedBitsNonblankCountExact witness bits =
  refl

formulaInputNonblankCountExact :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : Decider.CodedStandardPolynomialDecider decider)
    (formula : Cook.BooleanFormula) →
  Nonblank.nonblankCount
    (Coded.canonicalFinEnumeration
      (Coded.symbolCount (Decider.code witness)))
    (Coded.blank (Decider.code witness))
    (Decider.formulaInput
      (Decider.code witness)
      (Decider.zeroSymbol witness)
      (Decider.oneSymbol witness)
      formula)
  ≡ Binary.formulaBitCodeLength formula
formulaInputNonblankCountExact witness formula =
  mappedBitsNonblankCountExact
    witness
    (Binary.encodeFormulaBits formula)

------------------------------------------------------------------------
-- The literal payload size and nonblank information content therefore coincide
-- for the canonical coded BooleanFormula input.
------------------------------------------------------------------------
