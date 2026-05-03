module DASHI.Algebra.TritTriTruthBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import Base369 using
  ( TriTruth
  ; tri-low ; tri-mid ; tri-high
  ; rotateTri
  ; triXor
  ; triXor-identityˡ
  ; triXor-assoc
  )
import DASHI.Algebra.Trit as T

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

toTriTruth : T.Trit → TriTruth
toTriTruth T.neg = tri-low
toTriTruth T.zer = tri-mid
toTriTruth T.pos = tri-high

fromTriTruth : TriTruth → T.Trit
fromTriTruth tri-low  = T.neg
fromTriTruth tri-mid  = T.zer
fromTriTruth tri-high = T.pos

toFrom : ∀ t → toTriTruth (fromTriTruth t) ≡ t
toFrom tri-low  = refl
toFrom tri-mid  = refl
toFrom tri-high = refl

fromTo : ∀ t → fromTriTruth (toTriTruth t) ≡ t
fromTo T.neg = refl
fromTo T.zer = refl
fromTo T.pos = refl

rotTrit : T.Trit → T.Trit
rotTrit T.neg = T.zer
rotTrit T.zer = T.pos
rotTrit T.pos = T.neg

rotTrit-equivariant-to :
  ∀ t →
  toTriTruth (rotTrit t) ≡ rotateTri (toTriTruth t)
rotTrit-equivariant-to T.neg = refl
rotTrit-equivariant-to T.zer = refl
rotTrit-equivariant-to T.pos = refl

rotTrit-equivariant-from :
  ∀ t →
  fromTriTruth (rotateTri t) ≡ rotTrit (fromTriTruth t)
rotTrit-equivariant-from tri-low  = refl
rotTrit-equivariant-from tri-mid  = refl
rotTrit-equivariant-from tri-high = refl

inv-reflection-not-rotation-at-neg :
  T.inv T.neg ≢ rotTrit T.neg
inv-reflection-not-rotation-at-neg ()

tritXor : T.Trit → T.Trit → T.Trit
tritXor a b = fromTriTruth (triXor (toTriTruth a) (toTriTruth b))

triXor-equivariant :
  ∀ a b →
  toTriTruth (tritXor a b) ≡ triXor (toTriTruth a) (toTriTruth b)
triXor-equivariant a b = toFrom (triXor (toTriTruth a) (toTriTruth b))

tritXor-identityˡ : ∀ t → tritXor T.neg t ≡ t
tritXor-identityˡ t
  rewrite triXor-identityˡ (toTriTruth t)
        | fromTo t = refl

tritXor-assoc :
  ∀ a b c →
  tritXor a (tritXor b c) ≡ tritXor (tritXor a b) c
tritXor-assoc a b c
  rewrite toFrom (triXor (toTriTruth b) (toTriTruth c))
        | toFrom (triXor (toTriTruth a) (toTriTruth b))
        | triXor-assoc (toTriTruth a) (toTriTruth b) (toTriTruth c) = refl

inv-reflection-involutive : ∀ t → T.inv (T.inv t) ≡ t
inv-reflection-involutive = T.inv-invol

inv-reflection-not-tritXor-hom-at-neg :
  T.inv (tritXor T.neg T.neg) ≢
  tritXor (T.inv T.neg) (T.inv T.neg)
inv-reflection-not-tritXor-hom-at-neg ()

record TritTriTruthIso : Set where
  constructor tritTriTruthIso
  field
    to : T.Trit → TriTruth
    from : TriTruth → T.Trit
    to-from : ∀ t → to (from t) ≡ t
    from-to : ∀ t → from (to t) ≡ t
    rotation-equivariant :
      ∀ t → to (rotTrit t) ≡ rotateTri (to t)
    xor-equivariant :
      ∀ a b → to (tritXor a b) ≡ triXor (to a) (to b)
    xor-identityˡ : ∀ t → tritXor T.neg t ≡ t
    xor-assoc :
      ∀ a b c →
      tritXor a (tritXor b c) ≡ tritXor (tritXor a b) c
    reflection-involutive : ∀ t → T.inv (T.inv t) ≡ t
    reflection-not-rotation : T.inv T.neg ≢ rotTrit T.neg
    reflection-not-xor-hom :
      T.inv (tritXor T.neg T.neg) ≢
      tritXor (T.inv T.neg) (T.inv T.neg)

tritTriTruthIsoSurface : TritTriTruthIso
tritTriTruthIsoSurface =
  tritTriTruthIso
    toTriTruth
    fromTriTruth
    toFrom
    fromTo
    rotTrit-equivariant-to
    triXor-equivariant
    tritXor-identityˡ
    tritXor-assoc
    inv-reflection-involutive
    inv-reflection-not-rotation-at-neg
    inv-reflection-not-tritXor-hom-at-neg
