module DASHI.Mathematics.Complexity.Karp21UpperPairStructuralLexOrderExact where

------------------------------------------------------------------------
-- E20 canonical upper-triangle enumeration: STRICT STRUCTURAL ORDER.
--
-- The original Pair.allFin n lists indices in increasing order.
-- Pair.allUpperPairs n lists all (0,j) before all (i,j) with i>0,
-- then recursively preserves that ordering after lifting both indices.
--
-- This module proves that EVERY earlier address precedes EVERY later
-- address by a source-owned lex relation on the original UpperPair.
--
-- It does not replace the graph, use a certificate as input, or assert
-- that Decode.strictAfter's decidable Bool comparison is proved equal
-- to the structural order. That last Bool-reflection and the dependent
-- vertex reconstruction are the remaining parser gates.
--
-- Credit: Karp 1972; existing DASHI UpperPair/allFin construction.
-- Source-written, unkernelled; no postulates or unsafe recursion.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_; z≤n; s≤s)
open import Data.List.Base using (List; []; _∷_; _++_; map)
import Data.Fin.Base as Fin
import DASHI.Mathematics.Complexity.Karp21IndexedUpperPairBijectionExact as Pair

-- Use literal integer index comparison on the same typed vertices.
FinBefore : ∀ {n : Nat} → Fin.Fin n → Fin.Fin n → Set
FinBefore i j = Fin.toℕ i < Fin.toℕ j

-- These three constructors are exactly lexicographic order on the
-- original zero-head / successor-tail upper-triangle addresses.
data UpperPairBefore :
  ∀ {n : Nat} →
  Pair.UpperPair n → Pair.UpperPair n → Set where

  headBeforeHead :
    ∀ {n : Nat} {i j : Fin.Fin n} →
    FinBefore i j →
    UpperPairBefore (Pair.headTail i) (Pair.headTail j)

  headBeforeTail :
    ∀ {n : Nat} {i : Fin.Fin n} {p : Pair.UpperPair n} →
    UpperPairBefore (Pair.headTail i) (Pair.tailPair p)

  tailBeforeTail :
    ∀ {n : Nat} {p q : Pair.UpperPair n} →
    UpperPairBefore p q →
    UpperPairBefore (Pair.tailPair p) (Pair.tailPair q)

------------------------------------------------------------------------
-- Strong sortedness, not merely a no-duplicates theorem: each head
-- is earlier than every element of the entire remaining tail.
------------------------------------------------------------------------

data AllAfter {A : Set} (R : A → A → Set) (x : A) :
  List A → Set where
  afterNil : AllAfter R x []
  afterCons :
    ∀ {y rest} →
    R x y →
    AllAfter R x rest →
    AllAfter R x (y ∷ rest)

data StrictSorted {A : Set} (R : A → A → Set) :
  List A → Set where
  sortedNil : StrictSorted R []
  sortedCons :
    ∀ {x rest} →
    AllAfter R x rest →
    StrictSorted R rest →
    StrictSorted R (x ∷ rest)

data CrossBefore {A : Set} (R : A → A → Set) :
  List A → List A → Set where
  crossNil :
    ∀ {right} →
    CrossBefore R [] right
  crossCons :
    ∀ {x left right} →
    AllAfter R x right →
    CrossBefore R left right →
    CrossBefore R (x ∷ left) right

allAfterAppend :
  ∀ {A : Set} {R : A → A → Set} {x : A}
    (left right : List A) →
  AllAfter R x left →
  AllAfter R x right →
  AllAfter R x (left ++ right)
allAfterAppend [] right afterNil rightAfter = rightAfter
allAfterAppend (_ ∷ rest) right (afterCons headBefore tailAfter)
  rightAfter =
  afterCons headBefore (allAfterAppend rest right tailAfter rightAfter)

sortedAppend :
  ∀ {A : Set} {R : A → A → Set}
    (left right : List A) →
  StrictSorted R left →
  StrictSorted R right →
  CrossBefore R left right →
  StrictSorted R (left ++ right)
sortedAppend [] right sortedNil rightSorted crossNil = rightSorted
sortedAppend (_ ∷ left) right
  (sortedCons headAfter leftSorted)
  rightSorted (crossCons headCross crossTail) =
  sortedCons
    (allAfterAppend left right headAfter headCross)
    (sortedAppend left right leftSorted rightSorted crossTail)

------------------------------------------------------------------------
-- Reusable map transport. The map is applied to the ORIGINAL
-- source-owned lists; no new enumeration is built here.
------------------------------------------------------------------------

mapAllAfter :
  ∀ {A B : Set} {R : A → A → Set} {S : B → B → Set}
    (f : A → B)
    (preserves : ∀ {x y} → R x y → S (f x) (f y))
    (head : A) (rest : List A) →
  AllAfter R head rest →
  AllAfter S (f head) (map f rest)
mapAllAfter f preserves head [] afterNil = afterNil
mapAllAfter f preserves head (x ∷ xs) (afterCons order rest) =
  afterCons (preserves order)
    (mapAllAfter f preserves head xs rest)

mapStrictSorted :
  ∀ {A B : Set} {R : A → A → Set} {S : B → B → Set}
    (f : A → B)
    (preserves : ∀ {x y} → R x y → S (f x) (f y))
    (xs : List A) →
  StrictSorted R xs →
  StrictSorted S (map f xs)
mapStrictSorted f preserves [] sortedNil = sortedNil
mapStrictSorted f preserves (x ∷ xs) (sortedCons before rest) =
  sortedCons
    (mapAllAfter f preserves x xs before)
    (mapStrictSorted f preserves xs rest)

------------------------------------------------------------------------
-- The original finite vertex enumeration is strictly ascending.
------------------------------------------------------------------------

zeroBeforeEverySuccessor :
  ∀ {n : Nat} (xs : List (Fin.Fin n)) →
  AllAfter FinBefore Fin.zero (map Fin.suc xs)
zeroBeforeEverySuccessor [] = afterNil
zeroBeforeEverySuccessor (x ∷ xs) =
  afterCons (s≤s z≤n) (zeroBeforeEverySuccessor xs)

allFinStrictIncreasing :
  (n : Nat) →
  StrictSorted FinBefore (Pair.allFin n)
allFinStrictIncreasing zero = sortedNil
allFinStrictIncreasing (suc n) =
  sortedCons
    (zeroBeforeEverySuccessor (Pair.allFin n))
    (mapStrictSorted Fin.suc (λ order → s≤s order)
      (Pair.allFin n) (allFinStrictIncreasing n))

------------------------------------------------------------------------
-- Each earlier head pair precedes ALL later tail pairs. The tail
-- block is lifted from the previous upper-pair enumeration.
------------------------------------------------------------------------

headBeforeEveryTail :
  ∀ {n : Nat}
    (i : Fin.Fin n) (tails : List (Pair.UpperPair n)) →
  AllAfter UpperPairBefore (Pair.headTail i)
    (map Pair.tailPair tails)
headBeforeEveryTail i [] = afterNil
headBeforeEveryTail i (p ∷ rest) =
  afterCons headBeforeTail (headBeforeEveryTail i rest)

allHeadBeforeAllTails :
  ∀ {n : Nat}
    (heads : List (Fin.Fin n))
    (tails : List (Pair.UpperPair n)) →
  CrossBefore UpperPairBefore
    (map Pair.headTail heads)
    (map Pair.tailPair tails)
allHeadBeforeAllTails [] tails = crossNil
allHeadBeforeAllTails (i ∷ heads) tails =
  crossCons
    (headBeforeEveryTail i tails)
    (allHeadBeforeAllTails heads tails)

allUpperPairsStrictLexOrder :
  (n : Nat) →
  StrictSorted UpperPairBefore (Pair.allUpperPairs n)
allUpperPairsStrictLexOrder zero = sortedNil
allUpperPairsStrictLexOrder (suc n) =
  sortedAppend
    (map Pair.headTail (Pair.allFin n))
    (map Pair.tailPair (Pair.allUpperPairs n))
    (mapStrictSorted Pair.headTail headBeforeHead
      (Pair.allFin n) (allFinStrictIncreasing n))
    (mapStrictSorted Pair.tailPair tailBeforeTail
      (Pair.allUpperPairs n) (allUpperPairsStrictLexOrder n))
    (allHeadBeforeAllTails (Pair.allFin n) (Pair.allUpperPairs n))
