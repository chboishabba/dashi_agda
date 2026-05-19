module DASHI.Pressure where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; _⊔_)
open import Data.Nat.Properties as NatP using
  ( ≤-refl
  ; ≤-trans
  ; ⊔-assoc
  ; ⊔-comm
  ; ⊔-idem
  ; ⊔-lub
  ; ⊔-monoˡ-≤
  ; ⊔-monoʳ-≤
  ; m≤m⊔n
  ; m≤n⊔m
  )
open import Relation.Binary.PropositionalEquality as Eq using (cong; sym; trans)

infix 4 _⊑p_
infixl 6 _⊔p_

data Pressure : Set where
  none : Pressure
  low : Pressure
  medium : Pressure
  high : Pressure
  critical : Pressure

toLevel : Pressure → Nat
toLevel none = zero
toLevel low = suc zero
toLevel medium = suc (suc zero)
toLevel high = suc (suc (suc zero))
toLevel critical = suc (suc (suc (suc zero)))

fromLevel : Nat → Pressure
fromLevel zero = none
fromLevel (suc zero) = low
fromLevel (suc (suc zero)) = medium
fromLevel (suc (suc (suc zero))) = high
fromLevel (suc (suc (suc (suc _)))) = critical

_⊑p_ : Pressure → Pressure → Set
a ⊑p b = toLevel a ≤ toLevel b

_⊔p_ : Pressure → Pressure → Pressure
a ⊔p b = fromLevel (toLevel a ⊔ toLevel b)

fromLevel-toLevel : ∀ p → fromLevel (toLevel p) ≡ p
fromLevel-toLevel none = refl
fromLevel-toLevel low = refl
fromLevel-toLevel medium = refl
fromLevel-toLevel high = refl
fromLevel-toLevel critical = refl

join-level : ∀ a b → toLevel (a ⊔p b) ≡ toLevel a ⊔ toLevel b
join-level none none = refl
join-level none low = refl
join-level none medium = refl
join-level none high = refl
join-level none critical = refl
join-level low none = refl
join-level low low = refl
join-level low medium = refl
join-level low high = refl
join-level low critical = refl
join-level medium none = refl
join-level medium low = refl
join-level medium medium = refl
join-level medium high = refl
join-level medium critical = refl
join-level high none = refl
join-level high low = refl
join-level high medium = refl
join-level high high = refl
join-level high critical = refl
join-level critical none = refl
join-level critical low = refl
join-level critical medium = refl
join-level critical high = refl
join-level critical critical = refl

toLevel-injective : ∀ {a b} → toLevel a ≡ toLevel b → a ≡ b
toLevel-injective {none} {none} _ = refl
toLevel-injective {none} {low} ()
toLevel-injective {none} {medium} ()
toLevel-injective {none} {high} ()
toLevel-injective {none} {critical} ()
toLevel-injective {low} {none} ()
toLevel-injective {low} {low} _ = refl
toLevel-injective {low} {medium} ()
toLevel-injective {low} {high} ()
toLevel-injective {low} {critical} ()
toLevel-injective {medium} {none} ()
toLevel-injective {medium} {low} ()
toLevel-injective {medium} {medium} _ = refl
toLevel-injective {medium} {high} ()
toLevel-injective {medium} {critical} ()
toLevel-injective {high} {none} ()
toLevel-injective {high} {low} ()
toLevel-injective {high} {medium} ()
toLevel-injective {high} {high} _ = refl
toLevel-injective {high} {critical} ()
toLevel-injective {critical} {none} ()
toLevel-injective {critical} {low} ()
toLevel-injective {critical} {medium} ()
toLevel-injective {critical} {high} ()
toLevel-injective {critical} {critical} _ = refl

refl-⊑p : ∀ {p} → p ⊑p p
refl-⊑p = ≤-refl

trans-⊑p : ∀ {a b c} → a ⊑p b → b ⊑p c → a ⊑p c
trans-⊑p = ≤-trans

⊔p-idem : ∀ a → a ⊔p a ≡ a
⊔p-idem a =
  toLevel-injective
    (trans
      (join-level a a)
      (⊔-idem (toLevel a)))

⊔p-comm : ∀ a b → a ⊔p b ≡ b ⊔p a
⊔p-comm a b =
  toLevel-injective
    (trans
      (join-level a b)
      (trans
        (⊔-comm (toLevel a) (toLevel b))
        (sym (join-level b a))))

⊔p-assoc : ∀ a b c → (a ⊔p b) ⊔p c ≡ a ⊔p (b ⊔p c)
⊔p-assoc a b c =
  toLevel-injective
    (trans
      (join-level (a ⊔p b) c)
      (trans
        (cong (_⊔ toLevel c) (join-level a b))
        (trans
          (⊔-assoc (toLevel a) (toLevel b) (toLevel c))
          (trans
            (sym (cong (toLevel a ⊔_) (join-level b c)))
            (sym (join-level a (b ⊔p c)))))))

join-upper-left : ∀ a b → a ⊑p (a ⊔p b)
join-upper-left a b rewrite join-level a b =
  m≤m⊔n (toLevel a) (toLevel b)

join-upper-right : ∀ a b → b ⊑p (a ⊔p b)
join-upper-right a b rewrite join-level a b =
  m≤n⊔m (toLevel a) (toLevel b)

join-least :
  ∀ {a b c} →
  a ⊑p c →
  b ⊑p c →
  (a ⊔p b) ⊑p c
join-least {a} {b} {c} a≤c b≤c rewrite join-level a b =
  ⊔-lub a≤c b≤c

⊔p-monoˡ : ∀ {a a' b} → a ⊑p a' → (a ⊔p b) ⊑p (a' ⊔p b)
⊔p-monoˡ {a} {a'} {b} a≤a'
  rewrite join-level a b | join-level a' b =
    ⊔-monoˡ-≤ (toLevel b) a≤a'

⊔p-monoʳ : ∀ {a b b'} → b ⊑p b' → (a ⊔p b) ⊑p (a ⊔p b')
⊔p-monoʳ {a} {b} {b'} b≤b'
  rewrite join-level a b | join-level a b' =
    ⊔-monoʳ-≤ (toLevel a) b≤b'
