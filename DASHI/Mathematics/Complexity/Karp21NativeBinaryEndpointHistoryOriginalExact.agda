module DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryOriginalExact where

------------------------------------------------------------------------
-- B5 EXACT source original endpointConsistent semantic equality.
-- The executable binary endpoint-history checker scans original
-- repeated chronological labels using actual compareLE equality.
-- The RHS is THE ORIGINAL NatP._≟_ based Fin-free verifier, for
-- exactly the numerically observed same history, not a new scorer.
-- Nat decoding and Dec equality occur only in proof observations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (trans; cong)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21NativeNatDecisionReflectionExact as Decisions
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact as Binary
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original

numericHistorySameOriginal :
  (vertex : Nat)
  (label : Bool)
  (history : List (Nat × Bool)) →
  Binary.numericEndpointConsistent vertex label history
    ≡ Original.endpointConsistent vertex label history
numericHistorySameOriginal vertex label [] = refl
numericHistorySameOriginal vertex label ((other , observed) ∷ rest)
  rewrite Decisions.natEqualDecisionSameBoolean vertex other
  with NatP._≟_ vertex other
... | yes _ =
  cong (Boolean.andBool (Boolean.boolEqual label observed))
    (numericHistorySameOriginal vertex label rest)
... | no _ = numericHistorySameOriginal vertex label rest

-- B5: exact original source endpoint consistency for all binary
-- addresses, labels, repeated vertices and arbitrary history length.
nativeBinaryEndpointHistorySameOriginal :
  (vertex : Word.BitWord)
  (label : Bool)
  (history : Binary.BinaryEndpointHistory) →
  Binary.endpointConsistentBinary vertex label history
    ≡ Original.endpointConsistent
        (Value.valueLE vertex) label
        (Binary.observedBinaryHistory history)
nativeBinaryEndpointHistorySameOriginal vertex label history =
  trans
    (Binary.binaryEndpointHistorySameNumeric vertex label history)
    (numericHistorySameOriginal (Value.valueLE vertex) label
      (Binary.observedBinaryHistory history))
