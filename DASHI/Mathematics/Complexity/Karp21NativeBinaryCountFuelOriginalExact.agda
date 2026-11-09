module DASHI.Mathematics.Complexity.Karp21NativeBinaryCountFuelOriginalExact where

------------------------------------------------------------------------
-- B6 decisive source seam: original Nat-counted raw edge reader is
-- the numerical observation of the ACTUAL binary-count+fuel reader,
-- whenever fuel >= the original decoded m.
--
-- All-word theorem: includes arbitrary zero-padding, malformed gamma
-- triples, arbitrary suffix, successful signed edge stream, and m=0.
-- Runtime never creates the decoded unary m: Value.valueLE and
-- Nat inequalities appear ONLY in the proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21NativePositiveThresholdNonzeroExact as Nonzero
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Whole
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Original

peelBudget :
  (k fuel : Nat) →
  suc k ≤ suc fuel → k ≤ fuel
peelBudget k fuel (s≤s bound) = bound

positiveBinaryPredecessorValue :
  (mLE : Word.BitWord) →
  Positive.anyOne mLE ≡ true →
  (k : Nat) →
  Value.valueLE mLE ≡ suc k →
  Value.valueLE (Positive.predecessorLE mLE) ≡ k
positiveBinaryPredecessorValue mLE nonzero k numeric =
  NatP.suc-injective
    (trans
      (sym (NatP.+-comm
        (Value.valueLE (Positive.predecessorLE mLE))
        (suc zero)))
      (trans (Positive.predecessorLEValue mLE nonzero) numeric))

-- No trusted external parse-success witness, no assumed positive m:
-- the actual binary anyOne test provides positive/zero cases, and
-- actual readOneBinaryRawEdge provides exact original edge outcome.
nativeBinaryCountFuelSameOriginal :
  (fuel : Nat) (mLE word : Word.BitWord) →
  Value.valueLE mLE ≤ fuel →
  Edge.observeBinaryEdgeStream
    (Whole.readBinaryRawEdgesFuel fuel mLE word)
    ≡ Original.readRawEdges (Value.valueLE mLE) word
nativeBinaryCountFuelSameOriginal zero mLE word budget
  with Positive.anyOne mLE in nonzero
... | false
  rewrite Nonzero.anyOneFalseMeansZero mLE nonzero = refl
... | true with Nonzero.anyOneTrueMeansPositive mLE nonzero
... | k , mEq
  with subst (λ m → m ≤ zero) mEq budget
... | ()
nativeBinaryCountFuelSameOriginal (suc fuel) mLE word budget
  with Positive.anyOne mLE in nonzero
... | false
  rewrite Nonzero.anyOneFalseMeansZero mLE nonzero = refl
... | true with Nonzero.anyOneTrueMeansPositive mLE nonzero
... | k , mEq =
  let
    predecessorEq :
      Value.valueLE (Positive.predecessorLE mLE) ≡ k
    predecessorEq =
      positiveBinaryPredecessorValue mLE nonzero k mEq

    smallerBudget : k ≤ fuel
    smallerBudget =
      peelBudget k fuel
        (subst (λ m → m ≤ suc fuel) mEq budget)

    recursiveBudget :
      Value.valueLE (Positive.predecessorLE mLE) ≤ fuel
    recursiveBudget =
      subst (λ m → m ≤ fuel) (sym predecessorEq)
        smallerBudget
  in
  countFuelStep mLE word fuel k mEq predecessorEq recursiveBudget
  where
    countFuelStep :
      (mLE word : Word.BitWord) (fuel k : Nat) →
      Value.valueLE mLE ≡ suc k →
      Value.valueLE (Positive.predecessorLE mLE) ≡ k →
      Value.valueLE (Positive.predecessorLE mLE) ≤ fuel →
      Edge.observeBinaryEdgeStream
        (Whole.readBinaryRawEdgesFuel (suc fuel) mLE word)
        ≡ Original.readRawEdges (Value.valueLE mLE) word
    countFuelStep mLE word fuel k mEq predEq bound
      with Edge.readOneBinaryRawEdge word
         | Edge.oneBinaryEndpointRawEdgeSameOriginal word
    ... | nothing | firstEq
      rewrite sym firstEq | mEq = refl
    ... | just (edge , rest) | firstEq
      rewrite sym firstEq | mEq | predEq
      with Whole.readBinaryRawEdgesFuel fuel
             (Positive.predecessorLE mLE) rest
         | nativeBinaryCountFuelSameOriginal
             fuel (Positive.predecessorLE mLE) rest bound
    ... | nothing | tailEq rewrite sym tailEq = refl
    ... | just (edges , suffix) | tailEq
      rewrite sym tailEq = refl
