module DASHI.Mathematics.Complexity.Karp21FinFreeRawValidatorComparisonCountExact where

------------------------------------------------------------------------
-- ORIGINAL N21 raw graph edge VALIDATION: COUNTED, SAME-BOOL SCAN.
--
-- The original Runtime.validRawEdges visits each actual gamma-decoded
-- signed edge and applies the three original literal tests:
-- u < v, v < n, and Graph.strictAfter previous u v.
-- A valid edge continues; an invalid edge returns false immediately.
--
-- The counted function follows the SAME decisions, recording three
-- address/pair comparisons for each visited edge. It proves literal
-- Boolean equality and a universal bound of 3*m comparisons on a
-- list of m edges, including malformed/unsorted/out-of-range edges.
-- This is an address-comparison COUNT, not bit machine steps.
--
-- Sources: Karp 1972; original DASHI gamma/fin-free N21 graph owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime

-- Three literal comparison positions on each visited raw edge.
countedRawValidator :
  Nat → Graph.PreviousPair → List Graph.RawEdge → Bool × Nat
countedRawValidator n prev [] = true , zero
countedRawValidator n prev (Graph.raw-edge u v w ∷ rest)
  with NatP._<?_ u v | NatP._<?_ v n | Graph.strictAfter prev u v
... | yes _ | yes _ | true =
  let later = countedRawValidator n (Graph.previous u v) rest
  in proj₁ later , suc (suc (suc (proj₂ later)))
... | _ | _ | _ = false , suc (suc (suc zero))

-- Exact Boolean agreement on every raw list, not merely valid E20 images.
originalRawValidatorValueSame :
  (n : Nat) (prev : Graph.PreviousPair)
  (edges : List Graph.RawEdge) →
  proj₁ (countedRawValidator n prev edges)
    ≡ Runtime.validRawEdges n prev edges
originalRawValidatorValueSame n prev [] = refl
originalRawValidatorValueSame n prev
    (Graph.raw-edge u v w ∷ rest)
  with NatP._<?_ u v | NatP._<?_ v n | Graph.strictAfter prev u v
... | yes _ | yes _ | true =
  originalRawValidatorValueSame n (Graph.previous u v) rest
... | _ | _ | _ = refl

-- The source validator short-circuits, so the count may be smaller
-- than 3*m; it is ALWAYS bounded by 3*m.
originalRawValidatorComparisonCountBound :
  (n : Nat) (prev : Graph.PreviousPair)
  (edges : List Graph.RawEdge) →
  proj₂ (countedRawValidator n prev edges)
    ≤ 3 * length edges
originalRawValidatorComparisonCountBound n prev [] = z≤n
originalRawValidatorComparisonCountBound n prev
    (Graph.raw-edge u v w ∷ rest)
  with NatP._<?_ u v | NatP._<?_ v n | Graph.strictAfter prev u v
... | yes _ | yes _ | true =
  s≤s (s≤s (s≤s
    (originalRawValidatorComparisonCountBound
      n (Graph.previous u v) rest)))
... | _ | _ | _ =
  s≤s (s≤s (s≤s z≤n))
