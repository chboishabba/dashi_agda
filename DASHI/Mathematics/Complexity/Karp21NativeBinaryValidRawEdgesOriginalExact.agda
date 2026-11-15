module DASHI.Mathematics.Complexity.Karp21NativeBinaryValidRawEdgesOriginalExact where

------------------------------------------------------------------------
-- B2: original N21 raw-edge list validation, not a new graph language.
-- ACTUAL bit-only validNativeBinaryEdges agrees with original source
-- Fin-free Original.validRawEdges under the exact original numerical
-- observation of all native endpoints and signed edge list.
--
-- Induction respects source edge order, duplicates and reversal.
-- All original Nat and Dec operations are proof-side only.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointValidatorExact as Binary
import DASHI.Mathematics.Complexity.Karp21NativeBinaryStrictAfterOriginalExact as Strict
import DASHI.Mathematics.Complexity.Karp21NativeNatDecisionReflectionExact as Decisions
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original

-- Proof-side original validation expressed with numerical booleans,
-- to bridge the source Dec branches without making the runtime Nat.
validNumericRawEdges :
  Nat → Graph.PreviousPair → List Graph.RawEdge → Bool
validNumericRawEdges n previous [] = true
validNumericRawEdges n previous (Graph.raw-edge u v w ∷ rest)
  with Nat._≤ᵇ_ (suc u) v
     | Nat._≤ᵇ_ (suc v) n
     | Strict.strictAfterNumericBoolean previous u v
... | true | true | true =
  validNumericRawEdges n (Graph.previous u v) rest
... | _ | _ | _ = false

validNumericSameOriginal :
  (n : Nat) (previous : Graph.PreviousPair)
  (edges : List Graph.RawEdge) →
  validNumericRawEdges n previous edges ≡
    Original.validRawEdges n previous edges
validNumericSameOriginal n previous [] = refl
validNumericSameOriginal n previous (Graph.raw-edge u v w ∷ rest)
  rewrite Decisions.natStrictDecisionSameBoolean u v
        | Decisions.natStrictDecisionSameBoolean v n
        | Strict.strictAfterNumericSameOriginal previous u v
  with NatP._<?_ u v | NatP._<?_ v n
     | Graph.strictAfter previous u v
... | yes _ | yes _ | true =
  validNumericSameOriginal n (Graph.previous u v) rest
... | _ | _ | _ = refl

-- Every actual encoded binary original edge has the same old
-- numerical meaning; previous endpoint history is transported too.
validBinarySameNumeric :
  (nLE : Word.BitWord)
  (previous : Binary.BinaryPreviousPair)
  (edges : List Edge.BinaryRawEdge) →
  Binary.validNativeBinaryEdges nLE previous edges ≡
  validNumericRawEdges (Value.valueLE nLE)
    (Strict.observePrevious previous)
    (Edge.originalEdgeListObservation edges)
validBinarySameNumeric n previous [] = refl
validBinarySameNumeric n previous (Edge.binary-edge u v w ∷ rest)
  with Binary.lessNativeLE u v
     | Binary.lessNativeLE v n
     | Binary.strictAfterBinary previous u v
... | true | true | true
  rewrite sym (Binary.nativeStrictLessNumerical u v)
        | sym (Binary.nativeStrictLessNumerical v n)
        | sym (Strict.strictAfterBinarySameNumeric previous u v) =
  validBinarySameNumeric n (Binary.previous u v) rest
... | true | true | false
  rewrite sym (Binary.nativeStrictLessNumerical u v)
        | sym (Binary.nativeStrictLessNumerical v n)
        | sym (Strict.strictAfterBinarySameNumeric previous u v) = refl
... | true | false | _
  rewrite sym (Binary.nativeStrictLessNumerical u v)
        | sym (Binary.nativeStrictLessNumerical v n)
        | sym (Strict.strictAfterBinarySameNumeric previous u v) = refl
... | false | _ | _
  rewrite sym (Binary.nativeStrictLessNumerical u v)
        | sym (Binary.nativeStrictLessNumerical v n)
        | sym (Strict.strictAfterBinarySameNumeric previous u v) = refl

-- B2 terminal source declaration: exact original validRawEdges
-- on ALL actual native binary endpoints with duplicated/reversed
-- or nonascending source edge pairs rejected identically.
nativeBinaryValidRawEdgesSameOriginal :
  (nLE : Word.BitWord)
  (previous : Binary.BinaryPreviousPair)
  (edges : List Edge.BinaryRawEdge) →
  Binary.validNativeBinaryEdges nLE previous edges ≡
    Original.validRawEdges (Value.valueLE nLE)
      (Strict.observePrevious previous)
      (Edge.originalEdgeListObservation edges)
nativeBinaryValidRawEdgesSameOriginal n previous edges =
  trans
    (validBinarySameNumeric n previous edges)
    (validNumericSameOriginal
      (Value.valueLE n)
      (Strict.observePrevious previous)
      (Edge.originalEdgeListObservation edges))
