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
-- TOP-LEVEL PREDICATE INVOCATIONS for each visited edge. It proves literal
-- Boolean equality and a universal bound of 3*m predicate invocations on a
-- list of m edges, including malformed/unsorted/out-of-range edges.
-- Graph.strictAfter may itself use up to three primitive comparisons,
-- so the primitive comparison envelope is 5*m, NOT 3*m.
-- Neither result counts binary bit-machine steps.
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

------------------------------------------------------------------------
-- Account for the INTERNAL primitive comparisons in Graph.strictAfter:
-- * noPrevious: no numeric comparisons
-- * previous (a,b): compare a < u; on failure compare a == u;
--   on equality compare b < v.  The maximum is three.
-- This follows the ORIGINAL source branches and returns the same Bool.
------------------------------------------------------------------------

countedStrictAfter :
  Graph.PreviousPair → Nat → Nat → Bool × Nat
countedStrictAfter Graph.noPrevious u v = true , zero
countedStrictAfter (Graph.previous a b) u v
  with NatP._<?_ a u
... | yes _ = true , suc zero
... | no _ with NatP._≟_ a u
...   | no _ = false , suc (suc zero)
...   | yes _ with NatP._<?_ b v
...     | yes _ = true , suc (suc (suc zero))
...     | no _ = false , suc (suc (suc zero))

strictAfterValueSame :
  (prev : Graph.PreviousPair) (u v : Nat) →
  proj₁ (countedStrictAfter prev u v)
    ≡ Graph.strictAfter prev u v
strictAfterValueSame Graph.noPrevious u v = refl
strictAfterValueSame (Graph.previous a b) u v
  with NatP._<?_ a u
... | yes _ = refl
... | no _ with NatP._≟_ a u
...   | no _ = refl
...   | yes _ with NatP._<?_ b v
...     | yes _ = refl
...     | no _ = refl

strictAfterPrimitiveCountBound :
  (prev : Graph.PreviousPair) (u v : Nat) →
  proj₂ (countedStrictAfter prev u v)
    ≤ suc (suc (suc zero))
strictAfterPrimitiveCountBound Graph.noPrevious u v = z≤n
strictAfterPrimitiveCountBound (Graph.previous a b) u v
  with NatP._<?_ a u
... | yes _ = s≤s z≤n
... | no _ with NatP._≟_ a u
...   | no _ = s≤s (s≤s z≤n)
...   | yes _ with NatP._<?_ b v
...     | yes _ = NatP.≤-refl
...     | no _ = NatP.≤-refl

-- Worst-case per visited edge: 2 top-level numerical comparisons
-- plus up to 3 inside strictAfter. This exact static cap follows
-- the actual source syntax, with early exits only making it smaller.
primitiveValidatorComparisonBudget : Nat → Nat
primitiveValidatorComparisonBudget m = 5 * m

primitiveBudgetAtLeastMacroBudget :
  (m : Nat) → 3 * m ≤ primitiveValidatorComparisonBudget m
primitiveBudgetAtLeastMacroBudget zero = z≤n
primitiveBudgetAtLeastMacroBudget (suc m) =
  NatP.+-mono-≤
    (s≤s (s≤s (s≤s z≤n)))
    (primitiveBudgetAtLeastMacroBudget m)

------------------------------------------------------------------------
-- ACTUAL primitive comparison scheduling for the original validator.
-- This counts u<v, v<n and every primitive test inside strictAfter,
-- rather than incorrectly charging strictAfter as one primitive op.
------------------------------------------------------------------------

countedRawValidatorPrimitive :
  Nat → Graph.PreviousPair → List Graph.RawEdge → Bool × Nat
countedRawValidatorPrimitive n prev [] = true , zero
countedRawValidatorPrimitive n prev (Graph.raw-edge u v w ∷ rest)
  with NatP._<?_ u v | NatP._<?_ v n | Graph.strictAfter prev u v
... | yes _ | yes _ | true =
  let later = countedRawValidatorPrimitive n (Graph.previous u v) rest
  in proj₁ later ,
       suc (suc (proj₂ (countedStrictAfter prev u v) + proj₂ later))
... | _ | _ | _ =
  false , suc (suc (proj₂ (countedStrictAfter prev u v)))

primitiveValidatorValueSame :
  (n : Nat) (prev : Graph.PreviousPair)
  (edges : List Graph.RawEdge) →
  proj₁ (countedRawValidatorPrimitive n prev edges)
    ≡ Runtime.validRawEdges n prev edges
primitiveValidatorValueSame n prev [] = refl
primitiveValidatorValueSame n prev (Graph.raw-edge u v w ∷ rest)
  with NatP._<?_ u v | NatP._<?_ v n | Graph.strictAfter prev u v
... | yes _ | yes _ | true =
  primitiveValidatorValueSame n (Graph.previous u v) rest
... | _ | _ | _ = refl

primitiveValidatorCountBound :
  (n : Nat) (prev : Graph.PreviousPair)
  (edges : List Graph.RawEdge) →
  proj₂ (countedRawValidatorPrimitive n prev edges)
    ≤ primitiveValidatorComparisonBudget (length edges)
primitiveValidatorCountBound n prev [] = z≤n
primitiveValidatorCountBound n prev (Graph.raw-edge u v w ∷ rest)
  with NatP._<?_ u v | NatP._<?_ v n | Graph.strictAfter prev u v
... | yes _ | yes _ | true =
  s≤s (s≤s
    (NatP.+-mono-≤
      (strictAfterPrimitiveCountBound prev u v)
      (primitiveValidatorCountBound n (Graph.previous u v) rest)))
... | _ | _ | _ =
  s≤s (s≤s
    (NatP.≤-trans
      (strictAfterPrimitiveCountBound prev u v)
      (NatP.m≤m+n 3
        (5 * length rest))))
