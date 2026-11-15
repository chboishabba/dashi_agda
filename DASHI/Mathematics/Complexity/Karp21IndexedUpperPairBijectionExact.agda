module DASHI.Mathematics.Complexity.Karp21IndexedUpperPairBijectionExact where

------------------------------------------------------------------------
-- Exact canonical vertex PAIR ADDRESS for the E20 complete graph.
--
-- The upper triangle has one typed address per unordered pair of
-- *distinct* Fin n vertices:
--   headTail j   ↔ (zero, suc j)
--   tailPair p   ↔ (suc first(p), suc second(p)).
--
-- No external vertex labels, word hashes, weights or Boolean cut
-- assignments enter this construction. We prove all addresses have
-- distinct endpoints, any address is uniquely determined by its
-- ordered endpoints, and every off-diagonal vertex pair has an
-- address (in either orientation). An exhaustive allUpperPairs list
-- contains every address. Together these facts provide the structural
-- pair coverage missing from merely counting n(n−1)/2 edges.
--
-- Remaining required: identify the list with Gen.completePairEdges at
-- the weighted edge-list level, prove list occurrence multiplicity one,
-- and provide binary graph codec/machine-time certificates.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Relation.Binary.PropositionalEquality using (cong; sym)

import Data.Fin.Base as Fin
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact as Gen

data UpperPair : Nat → Set where
  headTail : ∀ {n} → Fin.Fin n → UpperPair (suc n)
  tailPair : ∀ {n} → UpperPair n → UpperPair (suc n)

endpoints : ∀ {n} → UpperPair n → Fin.Fin n × Fin.Fin n
endpoints (headTail j) = Fin.zero , Fin.suc j
endpoints (tailPair p) =
  Fin.suc (proj₁ (endpoints p)) ,
  Fin.suc (proj₂ (endpoints p))

upperPairNoLoop :
  ∀ {n} (p : UpperPair n) →
  proj₁ (endpoints p) ≡ proj₂ (endpoints p) → ⊥
upperPairNoLoop (headTail j) ()
upperPairNoLoop (tailPair p) eq =
  upperPairNoLoop p (Gen.finSuccessorInjective eq)

pairEquality :
  ∀ {A B : Set} (left right : A × B) →
  proj₁ left ≡ proj₁ right →
  proj₂ left ≡ proj₂ right →
  left ≡ right
pairEquality (a , b) (.a , .b) refl refl = refl

-- Endpoint indices determine a typed upper-triangle address uniquely.
upperPairEndpointsInjective :
  ∀ {n} (p q : UpperPair n) →
  endpoints p ≡ endpoints q →
  p ≡ q
upperPairEndpointsInjective (headTail i) (headTail j) eq =
  cong headTail
    (Gen.finSuccessorInjective (cong proj₂ eq))
upperPairEndpointsInjective (headTail i) (tailPair q) eq
  with cong proj₁ eq
... | ()
upperPairEndpointsInjective (tailPair p) (headTail j) eq
  with cong proj₁ eq
... | ()
upperPairEndpointsInjective (tailPair p) (tailPair q) eq =
  cong tailPair
    (upperPairEndpointsInjective p q
      (pairEquality (endpoints p) (endpoints q)
        (Gen.finSuccessorInjective (cong proj₁ eq))
        (Gen.finSuccessorInjective (cong proj₂ eq))))

liftEndpoints :
  ∀ {n} (p : UpperPair n) →
  endpoints (tailPair p) ≡
  (Fin.suc (proj₁ (endpoints p)) ,
   Fin.suc (proj₂ (endpoints p)))
liftEndpoints p = refl

-- Every distinct pair is reached; an arbitrary input order is
-- represented by either the canonical upper orientation or its swap.
upperPairCoversDistinct :
  ∀ {n}
    (i j : Fin.Fin n) →
    (i ≡ j → ⊥) →
  Σ (UpperPair n) (λ p →
    (endpoints p ≡ (i , j)) ⊎
    (endpoints p ≡ (j , i)))
upperPairCoversDistinct Fin.zero Fin.zero neq =
  ⊥-elim (neq refl)
upperPairCoversDistinct Fin.zero (Fin.suc j) neq =
  headTail j , inj₁ refl
upperPairCoversDistinct (Fin.suc i) Fin.zero neq =
  headTail i , inj₂ refl
upperPairCoversDistinct (Fin.suc i) (Fin.suc j) neq
  with upperPairCoversDistinct i j
    (λ eq → neq (cong Fin.suc eq))
... | p , inj₁ eq =
  tailPair p ,
    inj₁ (cong
      (λ pair →
        Fin.suc (proj₁ pair) , Fin.suc (proj₂ pair)) eq)
... | p , inj₂ eq =
  tailPair p ,
    inj₂ (cong
      (λ pair →
        Fin.suc (proj₁ pair) , Fin.suc (proj₂ pair)) eq)

allFin : (n : Nat) → List (Fin.Fin n)
allFin zero = []
allFin (suc n) = Fin.zero ∷ map Fin.suc (allFin n)

allUpperPairs : (n : Nat) → List (UpperPair n)
allUpperPairs zero = []
allUpperPairs (suc n) =
  map headTail (allFin n) ++
  map tailPair (allUpperPairs n)

-- Internal list membership, so "complete enumeration" is not merely
-- an informal explanation of the recursive upper-triangle shape.
data _∈_ {A : Set} (value : A) : List A → Set where
  here : ∀ {rest} → value ∈ (value ∷ rest)
  there : ∀ {head rest} → value ∈ rest → value ∈ (head ∷ rest)

mapContains :
  ∀ {A B : Set}
    (f : A → B) {value : A} {xs : List A} →
  value ∈ xs → f value ∈ map f xs
mapContains f here = here
mapContains f (there proof) = there (mapContains f proof)

leftContainsAppend :
  ∀ {A : Set} {x : A} {left right : List A} →
  x ∈ left → x ∈ (left ++ right)
leftContainsAppend here = here
leftContainsAppend (there proof) =
  there (leftContainsAppend proof)

rightContainsAppend :
  ∀ {A : Set} {x : A} {left right : List A} →
  x ∈ right → x ∈ (left ++ right)
rightContainsAppend {left = []} proof = proof
rightContainsAppend {left = _ ∷ _} proof =
  there (rightContainsAppend proof)

allFinContains :
  ∀ {n} (i : Fin.Fin n) → i ∈ allFin n
allFinContains Fin.zero = here
allFinContains (Fin.suc i) =
  there (mapContains Fin.suc (allFinContains i))

allUpperPairsContains :
  ∀ {n} (p : UpperPair n) → p ∈ allUpperPairs n
allUpperPairsContains (headTail j) =
  leftContainsAppend
    (mapContains headTail (allFinContains j))
allUpperPairsContains (tailPair p) =
  rightContainsAppend
    (mapContains tailPair (allUpperPairsContains p))

-- Existence at every distinct vertex pair *and* membership of the
-- chosen address in the actual finite enumerated upper-pair list.
enumeratedUpperPairCoversDistinct :
  ∀ {n} (i j : Fin.Fin n) (distinct : i ≡ j → ⊥) →
  Σ (UpperPair n) (λ p →
    (p ∈ allUpperPairs n) ×
    ((endpoints p ≡ (i , j)) ⊎
     (endpoints p ≡ (j , i))))
enumeratedUpperPairCoversDistinct i j distinct
  with upperPairCoversDistinct i j distinct
... | p , direction =
  p , (allUpperPairsContains p , direction)


------------------------------------------------------------------------
-- Injective upper-triangle addresses are also enumerated WITHOUT
-- duplicate list occurrences. The count lemma alone would not prove
-- this. No axiom, decidable oracle or cardinality arithmetic is used.
------------------------------------------------------------------------

data NoRepeat {A : Set} : List A → Set where
  noRepeatNil : NoRepeat []
  noRepeatCons :
    ∀ {x xs} →
    (x ∈ xs → ⊥) →
    NoRepeat xs →
    NoRepeat (x ∷ xs)

mapSuccessorReflect :
  ∀ {n} {i : Fin.Fin n} {xs : List (Fin.Fin n)} →
  Fin.suc i ∈ map Fin.suc xs →
  i ∈ xs
mapSuccessorReflect {xs = _ ∷ _} here = here
mapSuccessorReflect {xs = _ ∷ _} (there proof) =
  there (mapSuccessorReflect proof)

zeroNotInSuccessorMap :
  ∀ {n} {xs : List (Fin.Fin n)} →
  Fin.zero ∈ map Fin.suc xs → ⊥
zeroNotInSuccessorMap {xs = _ ∷ _} (there proof) =
  zeroNotInSuccessorMap proof

mapSuccessorNoRepeat :
  ∀ {n} {xs : List (Fin.Fin n)} →
  NoRepeat xs → NoRepeat (map Fin.suc xs)
mapSuccessorNoRepeat noRepeatNil = noRepeatNil
mapSuccessorNoRepeat (noRepeatCons notIn unique) =
  noRepeatCons
    (λ proof → notIn (mapSuccessorReflect proof))
    (mapSuccessorNoRepeat unique)

allFinNoRepeat :
  (n : Nat) → NoRepeat (allFin n)
allFinNoRepeat zero = noRepeatNil
allFinNoRepeat (suc n) =
  noRepeatCons zeroNotInSuccessorMap
    (mapSuccessorNoRepeat (allFinNoRepeat n))

headMapReflect :
  ∀ {n} {i : Fin.Fin n} {xs : List (Fin.Fin n)} →
  headTail i ∈ map headTail xs → i ∈ xs
headMapReflect {xs = _ ∷ _} here = here
headMapReflect {xs = _ ∷ _} (there proof) =
  there (headMapReflect proof)

tailMapReflect :
  ∀ {n} {p : UpperPair n} {xs : List (UpperPair n)} →
  tailPair p ∈ map tailPair xs → p ∈ xs
tailMapReflect {xs = _ ∷ _} here = here
tailMapReflect {xs = _ ∷ _} (there proof) =
  there (tailMapReflect proof)

headMapNoRepeat :
  ∀ {n} {xs : List (Fin.Fin n)} →
  NoRepeat xs → NoRepeat (map headTail xs)
headMapNoRepeat noRepeatNil = noRepeatNil
headMapNoRepeat (noRepeatCons notIn unique) =
  noRepeatCons
    (λ proof → notIn (headMapReflect proof))
    (headMapNoRepeat unique)

tailMapNoRepeat :
  ∀ {n} {xs : List (UpperPair n)} →
  NoRepeat xs → NoRepeat (map tailPair xs)
tailMapNoRepeat noRepeatNil = noRepeatNil
tailMapNoRepeat (noRepeatCons notIn unique) =
  noRepeatCons
    (λ proof → notIn (tailMapReflect proof))
    (tailMapNoRepeat unique)

headNotInTailMap :
  ∀ {n} {i : Fin.Fin n} {xs : List (UpperPair n)} →
  headTail i ∈ map tailPair xs → ⊥
headNotInTailMap {xs = _ ∷ _} (there proof) =
  headNotInTailMap proof

headMapOnlyHead :
  ∀ {n} {p : UpperPair (suc n)}
    {xs : List (Fin.Fin n)} →
  p ∈ map headTail xs →
  Σ (Fin.Fin n) (λ i → p ≡ headTail i)
headMapOnlyHead {xs = j ∷ xs} here =
  j , refl
headMapOnlyHead {xs = j ∷ xs} (there proof) =
  headMapOnlyHead proof

splitAppendMembership :
  ∀ {A : Set} {x : A}
    (left right : List A) →
  x ∈ (left ++ right) →
  (x ∈ left) ⊎ (x ∈ right)
splitAppendMembership [] right proof = inj₂ proof
splitAppendMembership (x ∷ xs) right here = inj₁ here
splitAppendMembership (x ∷ xs) right (there proof)
  with splitAppendMembership xs right proof
... | inj₁ inLeft = inj₁ (there inLeft)
... | inj₂ inRight = inj₂ inRight

noRepeatAppendSeparated :
  ∀ {A : Set} (left right : List A) →
  NoRepeat left →
  NoRepeat right →
  (∀ {x} → x ∈ left → x ∈ right → ⊥) →
  NoRepeat (left ++ right)
noRepeatAppendSeparated [] right noRepeatNil valid disjoint =
  valid
noRepeatAppendSeparated
  (x ∷ xs) right (noRepeatCons notIn tailUnique)
  valid disjoint =
  noRepeatCons
    (λ member →
      caseSplit (splitAppendMembership xs right member))
    (noRepeatAppendSeparated xs right tailUnique valid
      (λ inTail inRight →
        disjoint (there inTail) inRight))
  where
    caseSplit :
      (x ∈ xs) ⊎ (x ∈ right) → ⊥
    caseSplit (inj₁ inTail) = notIn inTail
    caseSplit (inj₂ inRight) = disjoint here inRight

headAndTailDisjoint :
  ∀ {n}
    {p : UpperPair (suc n)}
    {heads : List (Fin.Fin n)}
    {tails : List (UpperPair n)} →
  p ∈ map headTail heads →
  p ∈ map tailPair tails →
  ⊥
headAndTailDisjoint belongsHead belongsTail
  with headMapOnlyHead belongsHead
... | j , refl = headNotInTailMap belongsTail

allUpperPairsNoRepeat :
  (n : Nat) → NoRepeat (allUpperPairs n)
allUpperPairsNoRepeat zero = noRepeatNil
allUpperPairsNoRepeat (suc n) =
  noRepeatAppendSeparated
    (map headTail (allFin n))
    (map tailPair (allUpperPairs n))
    (headMapNoRepeat (allFinNoRepeat n))
    (tailMapNoRepeat (allUpperPairsNoRepeat n))
    headAndTailDisjoint

-- Every distinct pair has one *unique* canonical typed address in
-- allUpperPairs n: existence + no-repeated-address occurrence +
-- injective ordered endpoint projection. The orientation flip remains
-- exactly as in upperPairCoversDistinct, not a directed graph edge.
upperTriangleOccurrenceUnique :
  (n : Nat) → NoRepeat (allUpperPairs n)
upperTriangleOccurrenceUnique = allUpperPairsNoRepeat
