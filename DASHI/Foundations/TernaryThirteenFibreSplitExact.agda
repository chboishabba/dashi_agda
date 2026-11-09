{-# OPTIONS --safe #-}
module DASHI.Foundations.TernaryThirteenFibreSplitExact where

------------------------------------------------------------------------
-- H0.01–03: actual finite trit WORDS, not cardinality coincidences.
--
-- The original hyperfabric papers currently own the counts 3^12
-- and 3^13. This module supplies a canonical *new typed realisation*
-- with compositional split/join maps and both inverse laws. It does
-- NOT identify this word type with the source semantic completion.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

data Trit : Set where
  negative neutral positive : Trit

-- Length-indexed words with the original three-state interpretation.
TritWord : Nat → Set
TritWord zero = ⊤
TritWord (suc n) = Trit × TritWord n

-- Left-prefix append: m+n is computed by recursion on m.
joinTrit : (m n : Nat) →
  TritWord m → TritWord n → TritWord (m + n)
joinTrit zero n tt ys = ys
joinTrit (suc m) n (x , xs) ys =
  x , joinTrit m n xs ys

splitTrit : (m n : Nat) →
  TritWord (m + n) → TritWord m × TritWord n
splitTrit zero n ys = tt , ys
splitTrit (suc m) n (x , rest) with splitTrit m n rest
... | xs , ys = (x , xs) , ys

-- Generic two-sided equivalence, no cardinality or choice.
splitTritAfterJoin :
  (m n : Nat) (xs : TritWord m) (ys : TritWord n) →
  splitTrit m n (joinTrit m n xs ys) ≡ (xs , ys)
splitTritAfterJoin zero n tt ys = refl
splitTritAfterJoin (suc m) n (x , xs) ys =
  cong
    (λ pair → ((x , proj₁ pair) , proj₂ pair))
    (splitTritAfterJoin m n xs ys)

joinTritAfterSplit :
  (m n : Nat) (xs : TritWord (m + n)) →
  joinTrit m n
    (proj₁ (splitTrit m n xs))
    (proj₂ (splitTrit m n xs))
  ≡ xs
joinTritAfterSplit zero n xs = refl
joinTritAfterSplit (suc m) n (x , xs) =
  cong (λ zs → (x , zs)) (joinTritAfterSplit m n xs)

-- The two source-suggested length decompositions are definitionally 13.
ternaryThirteenSplitTwelvePlusOne :
  TritWord 13 → TritWord 12 × TritWord 1
ternaryThirteenSplitTwelvePlusOne =
  splitTrit 12 1

ternaryThirteenJoinTwelvePlusOne :
  TritWord 12 × TritWord 1 → TritWord 13
ternaryThirteenJoinTwelvePlusOne (xs , y) =
  joinTrit 12 1 xs y

ternaryThirteenSplitRoundTrip :
  (xs : TritWord 12 × TritWord 1) →
  ternaryThirteenSplitTwelvePlusOne
    (ternaryThirteenJoinTwelvePlusOne xs) ≡ xs
ternaryThirteenSplitRoundTrip (xs , y) =
  splitTritAfterJoin 12 1 xs y

ternaryThirteenJoinRoundTrip :
  (xs : TritWord 13) →
  ternaryThirteenJoinTwelvePlusOne
    (ternaryThirteenSplitTwelvePlusOne xs) ≡ xs
ternaryThirteenJoinRoundTrip =
  joinTritAfterSplit 12 1

-- Generic 3-block split explicitly respects associative grouping.
splitTriple :
  (a b c : Nat) →
  TritWord (a + (b + c)) →
  TritWord a × (TritWord b × TritWord c)
splitTriple a b c xs with splitTrit a (b + c) xs
... | first , rest = first , splitTrit b c rest

joinTriple :
  (a b c : Nat) →
  TritWord a × (TritWord b × TritWord c) →
  TritWord (a + (b + c))
joinTriple a b c (x , (y , z)) =
  joinTrit a (b + c) x (joinTrit b c y z)

splitTripleAfterJoin :
  (a b c : Nat)
  (x : TritWord a) (y : TritWord b) (z : TritWord c) →
  splitTriple a b c (joinTriple a b c (x , (y , z)))
  ≡ (x , (y , z))
splitTripleAfterJoin a b c x y z =
  trans
    (cong
      (λ pair → (proj₁ pair , splitTrit b c (proj₂ pair)))
      (splitTritAfterJoin a (b + c) x (joinTrit b c y z)))
    (cong (λ pair → (x , pair)) (splitTritAfterJoin b c y z))

joinTripleAfterSplit :
  (a b c : Nat) (x : TritWord (a + (b + c))) →
  joinTriple a b c (splitTriple a b c x) ≡ x
joinTripleAfterSplit a b c x with splitTrit a (b + c) x
... | first , rest =
  trans
    (cong (joinTrit a (b + c) first)
      (joinTritAfterSplit b c rest))
    (joinTritAfterSplit a (b + c) x)

ternaryThirteenSplitNineThreeOne :
  TritWord 13 →
  TritWord 9 × (TritWord 3 × TritWord 1)
ternaryThirteenSplitNineThreeOne = splitTriple 9 3 1

ternaryThirteenJoinNineThreeOne :
  TritWord 9 × (TritWord 3 × TritWord 1) →
  TritWord 13
ternaryThirteenJoinNineThreeOne = joinTriple 9 3 1

ternaryNineThreeOneSplitRoundTrip :
  (x : TritWord 9 × (TritWord 3 × TritWord 1)) →
  ternaryThirteenSplitNineThreeOne
    (ternaryThirteenJoinNineThreeOne x) ≡ x
ternaryNineThreeOneSplitRoundTrip (x , (y , z)) =
  splitTripleAfterJoin 9 3 1 x y z

ternaryNineThreeOneJoinRoundTrip :
  (x : TritWord 13) →
  ternaryThirteenJoinNineThreeOne
    (ternaryThirteenSplitNineThreeOne x) ≡ x
ternaryNineThreeOneJoinRoundTrip = joinTripleAfterSplit 9 3 1
