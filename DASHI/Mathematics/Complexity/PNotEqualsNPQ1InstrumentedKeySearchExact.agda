module DASHI.Mathematics.Complexity.PNotEqualsNPQ1InstrumentedKeySearchExact where

------------------------------------------------------------------------
-- ONE EXECUTION PATH FOR KEY LOOKUP AND ITS COMPARISON WORK RECEIPT
--
-- Before this owner, findKeyIndex and findKeyComparisonCount were two
-- separately-written recursions. Here the scanner returns BOTH its result
-- and the number of finite-vector equality tests actually executed by that
-- same recursion.
--
-- Exact equality with the old scanner and its separate count is proved.
-- Every equality test is charged at the full key width as a conservative
-- bit-inspection envelope, not an unearned constant-time operation.
--
-- This does not count allocation, list indexing, finite-vector tabulation
-- or the concrete tape instructions needed to realize Boolean comparison.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.List.Base using (length)
import Data.Fin.Base as Fin
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact as Merge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableKeySearchExact as Search

------------------------------------------------------------------------
-- Actual execution result paired with actual count of equality calls.
------------------------------------------------------------------------

scanKeyWithCharge :
  ∀ {remaining : Nat} →
  Merge.SemanticKey remaining →
  (keys : List (Merge.SemanticKey remaining)) →
  Maybe (Fin.Fin (length keys)) × Nat
scanKeyWithCharge key [] =
  nothing , zero
scanKeyWithCharge key (head ∷ tail)
    with Merge.decideTableEqual key head
... | inj₁ same =
  just Fin.zero , suc zero
... | inj₂ different
    with scanKeyWithCharge key tail
...   | nothing , scanned =
  nothing , suc scanned
...   | just index , scanned =
  just (Fin.suc index) , suc scanned

------------------------------------------------------------------------
-- The new instrumented scanner computes exactly the same answer.
------------------------------------------------------------------------

scanKeyResultExact :
  ∀ {remaining : Nat}
    (key : Merge.SemanticKey remaining)
    (keys : List (Merge.SemanticKey remaining)) →
  proj₁ (scanKeyWithCharge key keys)
  ≡
  Search.findKeyIndexExact key keys
scanKeyResultExact key [] =
  refl
scanKeyResultExact key (head ∷ tail)
    with Merge.decideTableEqual key head
... | inj₁ same =
  refl
... | inj₂ different
    with scanKeyWithCharge key tail
       | scanKeyResultExact key tail
...   | nothing , count | tailExact =
  cong (λ value → value) tailExact
...   | just index , count | tailExact =
  cong (λ value → value) tailExact

------------------------------------------------------------------------
-- The scan count agrees with the prior explicit comparison-count recursion.
------------------------------------------------------------------------

scanKeyCountExact :
  ∀ {remaining : Nat}
    (key : Merge.SemanticKey remaining)
    (keys : List (Merge.SemanticKey remaining)) →
  proj₂ (scanKeyWithCharge key keys)
  ≡
  Search.findKeyComparisonCount key keys
scanKeyCountExact key [] =
  refl
scanKeyCountExact key (head ∷ tail)
    with Merge.decideTableEqual key head
... | inj₁ same =
  refl
... | inj₂ different
    with scanKeyWithCharge key tail
       | scanKeyCountExact key tail
...   | result , count | exact =
  cong suc exact

------------------------------------------------------------------------
-- Exact conservative bit-work charge for the same execution.
------------------------------------------------------------------------

scanKeyBitEnvelope :
  ∀ {remaining : Nat} →
  Merge.SemanticKey remaining →
  List (Merge.SemanticKey remaining) →
  Nat
scanKeyBitEnvelope {remaining = remaining} key keys =
  Bits.bitCardinality remaining
  * proj₂ (scanKeyWithCharge key keys)

scanKeyBitEnvelopeMatchesDeclared :
  ∀ {remaining : Nat}
    (key : Merge.SemanticKey remaining)
    (keys : List (Merge.SemanticKey remaining)) →
  scanKeyBitEnvelope key keys
  ≡
  Search.findKeyFullWidthCharge key keys
scanKeyBitEnvelopeMatchesDeclared
    {remaining = remaining} key keys =
  cong
    (λ count → Bits.bitCardinality remaining * count)
    (scanKeyCountExact key keys)

------------------------------------------------------------------------
-- No claim that the bit envelope is equal to actual bit comparisons:
-- decideTableEqual short-circuits on the first difference. The full-width
-- multiplication is a safe pessimistic charge per attempted table equality.
------------------------------------------------------------------------
