module DASHI.Mathematics.Complexity.Karp21FinFreeEndpointScanComparisonCountExact where

------------------------------------------------------------------------
-- N21: EXECUTABLE ADDRESS COMPARISON COUNT ON THE FIN-FREE VERIFIER.
--
-- This is NOT a fictional polynomialTimeVerifier record. The verifier
-- uses the ORIGINAL gamma-decoded binary endpoint addresses (Nat)
-- and the earlier endpoint history; it does not materialise Fin n.
--
-- Instrument the ACTUAL N21 endpointConsistent function with an
-- explicit natural count of candidate address comparisons. Prove:
--
-- 1. first projection agrees exactly with the original Boolean result;
-- 2. every history occurrence is examined once in this strict
--    structural evaluator; the returned count is length history.
--
-- Integer binary-comparison bit cost, parser complexity, signed score
-- addition, tape-machine compilation and overall PR.InNP are still
-- separate obligations.
--
-- Source owners: Richard Karp (1972); DASHI original
-- Karp21FinFreeRawSparseWordVerifierExact and BoolGolden.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Base using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality using (cong)
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as FinFree

-- Same argument order and equality decision as original owner.
endpointConsistentCounted :
  Nat → Bool → List (Nat × Bool) → Bool × Nat
endpointConsistentCounted vertex selected [] =
  Boolean.andBool (Boolean.boolEqual selected selected)
    (FinFree.endpointConsistent vertex selected []) , zero
endpointConsistentCounted vertex selected ((other , observed) ∷ rest)
  with NatP._≟_ vertex other
... | yes _ with endpointConsistentCounted vertex selected rest
...   | status , checks =
  Boolean.andBool
    (Boolean.boolEqual selected observed) status , suc checks
... | no _ with endpointConsistentCounted vertex selected rest
...   | status , checks = status , suc checks

-- On empty history the original owner reduces to true. Keep the
-- instrumented base a direct definitional witness, not a decision flag.
endpointConsistentValueSame :
  (vertex : Nat)
  (selected : Bool)
  (history : List (Nat × Bool)) →
  proj₁ (endpointConsistentCounted vertex selected history)
    ≡ FinFree.endpointConsistent vertex selected history
endpointConsistentValueSame vertex selected [] =
  refl
endpointConsistentValueSame vertex selected ((other , observed) ∷ rest)
  with NatP._≟_ vertex other
... | yes _ =
  cong
    (Boolean.andBool (Boolean.boolEqual selected observed))
    (endpointConsistentValueSame vertex selected rest)
... | no _ = endpointConsistentValueSame vertex selected rest

endpointConsistentComparisonCountExact :
  (vertex : Nat)
  (selected : Bool)
  (history : List (Nat × Bool)) →
  proj₂ (endpointConsistentCounted vertex selected history)
    ≡ length history
endpointConsistentComparisonCountExact vertex selected [] = refl
endpointConsistentComparisonCountExact
  vertex selected ((other , observed) ∷ rest)
  with NatP._≟_ vertex other
... | yes _ =
  cong suc (endpointConsistentComparisonCountExact vertex selected rest)
... | no _ =
  cong suc (endpointConsistentComparisonCountExact vertex selected rest)
