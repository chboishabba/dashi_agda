module DASHI.Physics.Common.SameSourceGluedProducerExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- A combined producer is forced by two views of one source object.  The
-- components are not independently selected compatible-looking witnesses:
-- both are computed from the same source, and the resulting paired producer
-- satisfies the pointwise universal property of the product.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; _⊔_)

infixr 4 _×_

record _×_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B
open _×_ public

pairExt :
  ∀ {a b} {A : Set a} {B : Set b} {x y : A × B} →
  fst x ≡ fst y →
  snd x ≡ snd y →
  x ≡ y
pairExt {x = x₁ , x₂} {y = y₁ , y₂} refl refl = refl

record SameSourceGluedProducer
    {s l r : Level}
    (Source : Set s)
    (Left : Set l)
    (Right : Set r)
    (left : Source → Left)
    (right : Source → Right) :
    Set (s ⊔ l ⊔ r) where
  field
    total : Source → Left × Right

    leftExact :
      ∀ source → fst (total source) ≡ left source

    rightExact :
      ∀ source → snd (total source) ≡ right source

    uniquePointwise :
      ∀ (candidate : Source → Left × Right) source →
      fst (candidate source) ≡ left source →
      snd (candidate source) ≡ right source →
      candidate source ≡ total source
open SameSourceGluedProducer public

literalSameSourceGluedProducer :
  ∀ {s l r}
    {Source : Set s} {Left : Set l} {Right : Set r} →
  (left : Source → Left) →
  (right : Source → Right) →
  SameSourceGluedProducer Source Left Right left right
literalSameSourceGluedProducer left right = record
  { total = λ source → left source , right source
  ; leftExact = λ source → refl
  ; rightExact = λ source → refl
  ; uniquePointwise = λ candidate source left-proof right-proof →
      pairExt left-proof right-proof
  }

sameSourceCombined :
  ∀ {s l r}
    {Source : Set s} {Left : Set l} {Right : Set r} →
  (left : Source → Left) →
  (right : Source → Right) →
  Source → Left × Right
sameSourceCombined left right =
  total (literalSameSourceGluedProducer left right)

sameSourceCombinedLeftExact :
  ∀ {s l r}
    {Source : Set s} {Left : Set l} {Right : Set r}
    (left : Source → Left) (right : Source → Right) source →
  fst (sameSourceCombined left right source) ≡ left source
sameSourceCombinedLeftExact left right =
  leftExact (literalSameSourceGluedProducer left right)

sameSourceCombinedRightExact :
  ∀ {s l r}
    {Source : Set s} {Left : Set l} {Right : Set r}
    (left : Source → Left) (right : Source → Right) source →
  snd (sameSourceCombined left right source) ≡ right source
sameSourceCombinedRightExact left right =
  rightExact (literalSameSourceGluedProducer left right)

sameSourceCombinedUniquePointwise :
  ∀ {s l r}
    {Source : Set s} {Left : Set l} {Right : Set r}
    (left : Source → Left) (right : Source → Right)
    (candidate : Source → Left × Right) source →
  fst (candidate source) ≡ left source →
  snd (candidate source) ≡ right source →
  candidate source ≡ sameSourceCombined left right source
sameSourceCombinedUniquePointwise left right =
  uniquePointwise (literalSameSourceGluedProducer left right)
