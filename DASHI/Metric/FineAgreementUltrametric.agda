module DASHI.Metric.FineAgreementUltrametric where

open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Contraction using (_≢_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)
open import Data.Nat using (_<_; _≤_; _≥_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties as NatP
open import Data.Vec using (Vec; []; map; _++_; _∷_)
open import Data.Vec.Base using (reverse; _∷ʳ_; cast)
open import Data.Vec.Properties using (map-reverse; reverse-injective; reverse-∷; reverse-++; cast-is-id; cast-sym)
open import Ultrametric as UMetric
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)
open import DASHI.Physics.TailCollapseProof as TCP
import DASHI.Metric.AgreementUltrametric as AM

cong₂ : ∀ {A B C : Set} {x₁ x₂ : A} {y₁ y₂ : B}
        (g : A → B → C) →
        x₁ ≡ x₂ → y₁ ≡ y₂ → g x₁ y₁ ≡ g x₂ y₂
cong₂ g refl refl = refl

-- Fine agreement metric: use agreement depth on reversed vectors (suffix agreement).
agreeDepthFine : ∀ {n : Nat} → Vec Trit n → Vec Trit n → Nat
agreeDepthFine x y = AM.agreeDepth (reverse x) (reverse y)

dNatFine : ∀ {n : Nat} → Vec Trit n → Vec Trit n → Nat
dNatFine x y = AM.dNat (reverse x) (reverse y)

dNatFine-inv :
  ∀ {n : Nat} (x y : Vec Trit n) →
  dNatFine (map inv x) (map inv y) ≡ dNatFine x y
dNatFine-inv x y =
  let
    rx = reverse x
    ry = reverse y
    rx-inv : reverse (map inv x) ≡ map inv rx
    rx-inv = sym (map-reverse inv x)
    ry-inv : reverse (map inv y) ≡ map inv ry
    ry-inv = sym (map-reverse inv y)
  in
  trans
    (cong (λ a → AM.dNat a (reverse (map inv y))) rx-inv)
    (trans
      (cong (λ b → AM.dNat (map inv rx) b) ry-inv)
      (AM.dNat-inv rx ry)
    )

reverse≢ : ∀ {n : Nat} {x y : Vec Trit n} → x ≢ y → reverse x ≢ reverse y
reverse≢ x≢y rev≡ = x≢y (reverse-injective rev≡)

dNatFine-zero→eq :
  ∀ {n : Nat} (x y : Vec Trit n) → dNatFine x y ≡ 0 → x ≡ y
dNatFine-zero→eq x y d≡0 =
  reverse-injective (AM.dNat-zero→eq (reverse x) (reverse y) d≡0)

dNatFine-positive :
  ∀ {n : Nat} {x y : Vec Trit n} → x ≢ y → 0 < dNatFine x y
dNatFine-positive x≢y = AM.dNat-positive (reverse≢ x≢y)

------------------------------------------------------------------------
-- Agreement-depth monotonicity under pointwise maps

agreeDepth-map≤ :
  ∀ {n : Nat} (f : Trit → Trit) (x y : Vec Trit n) →
  AM.agreeDepth x y ≤ AM.agreeDepth (map f x) (map f y)
agreeDepth-map≤ {zero} f [] [] = z≤n
agreeDepth-map≤ {suc n} f (neg ∷ xs) (neg ∷ ys) with f neg
... | neg = s≤s (agreeDepth-map≤ f xs ys)
... | zer = s≤s (agreeDepth-map≤ f xs ys)
... | pos = s≤s (agreeDepth-map≤ f xs ys)
agreeDepth-map≤ {suc n} f (zer ∷ xs) (zer ∷ ys) with f zer
... | neg = s≤s (agreeDepth-map≤ f xs ys)
... | zer = s≤s (agreeDepth-map≤ f xs ys)
... | pos = s≤s (agreeDepth-map≤ f xs ys)
agreeDepth-map≤ {suc n} f (pos ∷ xs) (pos ∷ ys) with f pos
... | neg = s≤s (agreeDepth-map≤ f xs ys)
... | zer = s≤s (agreeDepth-map≤ f xs ys)
... | pos = s≤s (agreeDepth-map≤ f xs ys)
agreeDepth-map≤ {suc n} f (neg ∷ xs) (zer ∷ ys) = z≤n
agreeDepth-map≤ {suc n} f (neg ∷ xs) (pos ∷ ys) = z≤n
agreeDepth-map≤ {suc n} f (zer ∷ xs) (neg ∷ ys) = z≤n
agreeDepth-map≤ {suc n} f (zer ∷ xs) (pos ∷ ys) = z≤n
agreeDepth-map≤ {suc n} f (pos ∷ xs) (neg ∷ ys) = z≤n
agreeDepth-map≤ {suc n} f (pos ∷ xs) (zer ∷ ys) = z≤n

dNatFine-map≤ :
  ∀ {n : Nat} (f : Trit → Trit) (x y : Vec Trit n) →
  dNatFine (map f x) (map f y) ≤ dNatFine x y
dNatFine-map≤ {n} f x y =
  let
    rx-map : reverse (map f x) ≡ map f (reverse x)
    rx-map = sym (map-reverse f x)
    ry-map : reverse (map f y) ≡ map f (reverse y)
    ry-map = sym (map-reverse f y)
    step : AM.dNat (map f (reverse x)) (map f (reverse y)) ≤ AM.dNat (reverse x) (reverse y)
    step = NatP.∸-monoʳ-≤ n (agreeDepth-map≤ f (reverse x) (reverse y))
  in
  NatP.≤-trans
    (NatP.≤-reflexive (cong₂ AM.dNat rx-map ry-map))
    step

------------------------------------------------------------------------
-- Agreement depth for append (prefix metric on reverse)

agreeDepth-++≥ :
  ∀ {m n : Nat} (a b : Vec Trit m) (c : Vec Trit n) →
  AM.agreeDepth (a ++ c) (b ++ c) ≥ AM.agreeDepth a b
agreeDepth-++≥ {zero} {n} [] [] c = z≤n
agreeDepth-++≥ {suc m} {n} (neg ∷ as) (neg ∷ bs) c =
  s≤s (agreeDepth-++≥ as bs c)
agreeDepth-++≥ {suc m} {n} (zer ∷ as) (zer ∷ bs) c =
  s≤s (agreeDepth-++≥ as bs c)
agreeDepth-++≥ {suc m} {n} (pos ∷ as) (pos ∷ bs) c =
  s≤s (agreeDepth-++≥ as bs c)
agreeDepth-++≥ {suc m} {n} (neg ∷ as) (zer ∷ bs) c = z≤n
agreeDepth-++≥ {suc m} {n} (neg ∷ as) (pos ∷ bs) c = z≤n
agreeDepth-++≥ {suc m} {n} (zer ∷ as) (neg ∷ bs) c = z≤n
agreeDepth-++≥ {suc m} {n} (zer ∷ as) (pos ∷ bs) c = z≤n
agreeDepth-++≥ {suc m} {n} (pos ∷ as) (neg ∷ bs) c = z≤n
agreeDepth-++≥ {suc m} {n} (pos ∷ as) (zer ∷ bs) c = z≤n

------------------------------------------------------------------------
-- Reverse of snoc: reverse (xs ∷ʳ a) = a ∷ reverse xs

reverse-∷ʳ : ∀ {n : Nat} (xs : Vec Trit n) (a : Trit) →
  reverse (xs ∷ʳ a) ≡ a ∷ reverse xs
reverse-∷ʳ [] a = reverse-∷ a []
reverse-∷ʳ (x ∷ xs) a
  rewrite reverse-∷ x (xs ∷ʳ a)
        | reverse-∷ʳ xs a
        | reverse-∷ x xs
  = refl

agreeDepth-cast :
  ∀ {m n : Nat} (eq : m ≡ n) (x y : Vec Trit m) →
  AM.agreeDepth (cast eq x) (cast eq y) ≡ AM.agreeDepth x y
agreeDepth-cast refl x y
  rewrite cast-is-id refl x
        | cast-is-id refl y
  = refl

dNat-cast :
  ∀ {m n : Nat} (eq : m ≡ n) (x y : Vec Trit m) →
  AM.dNat (cast eq x) (cast eq y) ≡ AM.dNat x y
dNat-cast refl x y
  rewrite cast-is-id refl x
        | cast-is-id refl y
  = refl

------------------------------------------------------------------------
-- ShiftTail monotonicity on fine agreement

agreeDepth-++-mono :
  ∀ {m n : Nat} (u v u' v' : Vec Trit m) (p q : Vec Trit n) →
  AM.agreeDepth u v ≤ AM.agreeDepth u' v' →
  AM.agreeDepth (u ++ p) (v ++ q) ≤ AM.agreeDepth (u' ++ p) (v' ++ q)
agreeDepth-++-mono {zero} {n} [] [] [] [] p q h = NatP.≤-refl
agreeDepth-++-mono {suc m} {n} (neg ∷ us) (neg ∷ vs) (neg ∷ us') (neg ∷ vs') p q (s≤s h≤) =
  s≤s (agreeDepth-++-mono us vs us' vs' p q h≤)
agreeDepth-++-mono {suc m} {n} (neg ∷ us) (neg ∷ vs) (zer ∷ us') (zer ∷ vs') p q (s≤s h≤) =
  s≤s (agreeDepth-++-mono us vs us' vs' p q h≤)
agreeDepth-++-mono {suc m} {n} (neg ∷ us) (neg ∷ vs) (pos ∷ us') (pos ∷ vs') p q (s≤s h≤) =
  s≤s (agreeDepth-++-mono us vs us' vs' p q h≤)
agreeDepth-++-mono {suc m} {n} (zer ∷ us) (zer ∷ vs) (neg ∷ us') (neg ∷ vs') p q (s≤s h≤) =
  s≤s (agreeDepth-++-mono us vs us' vs' p q h≤)
agreeDepth-++-mono {suc m} {n} (zer ∷ us) (zer ∷ vs) (zer ∷ us') (zer ∷ vs') p q (s≤s h≤) =
  s≤s (agreeDepth-++-mono us vs us' vs' p q h≤)
agreeDepth-++-mono {suc m} {n} (zer ∷ us) (zer ∷ vs) (pos ∷ us') (pos ∷ vs') p q (s≤s h≤) =
  s≤s (agreeDepth-++-mono us vs us' vs' p q h≤)
agreeDepth-++-mono {suc m} {n} (pos ∷ us) (pos ∷ vs) (neg ∷ us') (neg ∷ vs') p q (s≤s h≤) =
  s≤s (agreeDepth-++-mono us vs us' vs' p q h≤)
agreeDepth-++-mono {suc m} {n} (pos ∷ us) (pos ∷ vs) (zer ∷ us') (zer ∷ vs') p q (s≤s h≤) =
  s≤s (agreeDepth-++-mono us vs us' vs' p q h≤)
agreeDepth-++-mono {suc m} {n} (pos ∷ us) (pos ∷ vs) (pos ∷ us') (pos ∷ vs') p q (s≤s h≤) =
  s≤s (agreeDepth-++-mono us vs us' vs' p q h≤)
agreeDepth-++-mono {suc m} {n} (neg ∷ us) (zer ∷ vs) u' v' p q h = z≤n
agreeDepth-++-mono {suc m} {n} (neg ∷ us) (pos ∷ vs) u' v' p q h = z≤n
agreeDepth-++-mono {suc m} {n} (zer ∷ us) (neg ∷ vs) u' v' p q h = z≤n
agreeDepth-++-mono {suc m} {n} (zer ∷ us) (pos ∷ vs) u' v' p q h = z≤n
agreeDepth-++-mono {suc m} {n} (pos ∷ us) (neg ∷ vs) u' v' p q h = z≤n
agreeDepth-++-mono {suc m} {n} (pos ∷ us) (zer ∷ vs) u' v' p q h = z≤n

agreeDepth-++-map≤ :
  ∀ {m n : Nat} (u v : Vec Trit m) (p q : Vec Trit n) (f : Trit → Trit) →
  AM.agreeDepth (u ++ p) (v ++ q) ≤ AM.agreeDepth (u ++ map f p) (v ++ map f q)
agreeDepth-++-map≤ {zero} {n} [] [] p q f = agreeDepth-map≤ f p q
agreeDepth-++-map≤ {suc m} {n} (neg ∷ us) (neg ∷ vs) p q f =
  s≤s (agreeDepth-++-map≤ us vs p q f)
agreeDepth-++-map≤ {suc m} {n} (zer ∷ us) (zer ∷ vs) p q f =
  s≤s (agreeDepth-++-map≤ us vs p q f)
agreeDepth-++-map≤ {suc m} {n} (pos ∷ us) (pos ∷ vs) p q f =
  s≤s (agreeDepth-++-map≤ us vs p q f)
agreeDepth-++-map≤ {suc m} {n} (neg ∷ us) (zer ∷ vs) p q f = z≤n
agreeDepth-++-map≤ {suc m} {n} (neg ∷ us) (pos ∷ vs) p q f = z≤n
agreeDepth-++-map≤ {suc m} {n} (zer ∷ us) (neg ∷ vs) p q f = z≤n
agreeDepth-++-map≤ {suc m} {n} (zer ∷ us) (pos ∷ vs) p q f = z≤n
agreeDepth-++-map≤ {suc m} {n} (pos ∷ us) (neg ∷ vs) p q f = z≤n
agreeDepth-++-map≤ {suc m} {n} (pos ∷ us) (zer ∷ vs) p q f = z≤n

agreeDepth-∷ʳ≤ :
  ∀ {n : Nat} (a b : Vec Trit n) (x y : Trit) →
  AM.agreeDepth (a ∷ʳ x) (b ∷ʳ y) ≤ suc (AM.agreeDepth a b)
agreeDepth-∷ʳ≤ {zero} [] [] neg neg = s≤s z≤n
agreeDepth-∷ʳ≤ {zero} [] [] zer zer = s≤s z≤n
agreeDepth-∷ʳ≤ {zero} [] [] pos pos = s≤s z≤n
agreeDepth-∷ʳ≤ {zero} [] [] neg zer = z≤n
agreeDepth-∷ʳ≤ {zero} [] [] neg pos = z≤n
agreeDepth-∷ʳ≤ {zero} [] [] zer neg = z≤n
agreeDepth-∷ʳ≤ {zero} [] [] zer pos = z≤n
agreeDepth-∷ʳ≤ {zero} [] [] pos neg = z≤n
agreeDepth-∷ʳ≤ {zero} [] [] pos zer = z≤n
agreeDepth-∷ʳ≤ {suc n} (neg ∷ as) (neg ∷ bs) x y =
  s≤s (agreeDepth-∷ʳ≤ as bs x y)
agreeDepth-∷ʳ≤ {suc n} (zer ∷ as) (zer ∷ bs) x y =
  s≤s (agreeDepth-∷ʳ≤ as bs x y)
agreeDepth-∷ʳ≤ {suc n} (pos ∷ as) (pos ∷ bs) x y =
  s≤s (agreeDepth-∷ʳ≤ as bs x y)
agreeDepth-∷ʳ≤ {suc n} (neg ∷ as) (zer ∷ bs) x y = z≤n
agreeDepth-∷ʳ≤ {suc n} (neg ∷ as) (pos ∷ bs) x y = z≤n
agreeDepth-∷ʳ≤ {suc n} (zer ∷ as) (neg ∷ bs) x y = z≤n
agreeDepth-∷ʳ≤ {suc n} (zer ∷ as) (pos ∷ bs) x y = z≤n
agreeDepth-∷ʳ≤ {suc n} (pos ∷ as) (neg ∷ bs) x y = z≤n
agreeDepth-∷ʳ≤ {suc n} (pos ∷ as) (zer ∷ bs) x y = z≤n

agreeDepthFine-shiftTail≥ :
  ∀ {k : Nat} (t1 t2 : Vec Trit k) →
  agreeDepthFine t1 t2 ≤ agreeDepthFine (TCP.shiftTail t1) (TCP.shiftTail t2)
agreeDepthFine-shiftTail≥ {zero} [] [] = z≤n
agreeDepthFine-shiftTail≥ {suc k} (x ∷ xs) (y ∷ ys) =
  NatP.≤-trans
    (subst
      (λ v → v ≤ suc (AM.agreeDepth (reverse xs) (reverse ys)))
      (sym lhs1)
      (agreeDepth-∷ʳ≤ (reverse xs) (reverse ys) x y))
    (NatP.≤-reflexive (sym lhs))
  where
    lhs1 : agreeDepthFine (x ∷ xs) (y ∷ ys)
           ≡ AM.agreeDepth (reverse xs ∷ʳ x) (reverse ys ∷ʳ y)
    lhs1 rewrite reverse-∷ x xs | reverse-∷ y ys = refl
    lhs : AM.agreeDepth (reverse (TCP.shiftTail (x ∷ xs)))
                        (reverse (TCP.shiftTail (y ∷ ys)))
          ≡ suc (AM.agreeDepth (reverse xs) (reverse ys))
    lhs rewrite reverse-∷ʳ xs zer | reverse-∷ʳ ys zer = refl

------------------------------------------------------------------------
-- Nonexpansive for shiftTail (tail-only)

dNatFine-shiftTail≤ :
  ∀ {k : Nat} (t1 t2 : Vec Trit k) →
  dNatFine (TCP.shiftTail t1) (TCP.shiftTail t2) ≤ dNatFine t1 t2
dNatFine-shiftTail≤ {k} t1 t2 =
  NatP.∸-monoʳ-≤ k (agreeDepthFine-shiftTail≥ t1 t2)

dNatFine-++ :
  ∀ {m n : Nat} (c c' : Vec Trit m) (t t' : Vec Trit n) →
  dNatFine (c ++ t) (c' ++ t') ≡
  AM.dNat (reverse t ++ reverse c) (reverse t' ++ reverse c')
dNatFine-++ {m} {n} c c' t t' =
  let
    eq : m + n ≡ n + m
    eq = NatP.+-comm m n
    rx : reverse (c ++ t) ≡ cast (sym eq) (reverse t ++ reverse c)
    rx = sym (cast-sym eq (reverse-++ eq c t))
    ry : reverse (c' ++ t') ≡ cast (sym eq) (reverse t' ++ reverse c')
    ry = sym (cast-sym eq (reverse-++ eq c' t'))
  in
  trans
    (cong₂ AM.dNat rx ry)
    (dNat-cast (sym eq) (reverse t ++ reverse c) (reverse t' ++ reverse c'))

dNatFine-++-map≤ :
  ∀ {m n : Nat} (c c' : Vec Trit m) (t t' : Vec Trit n) (f : Trit → Trit) →
  dNatFine (map f c ++ t) (map f c' ++ t') ≤ dNatFine (c ++ t) (c' ++ t')
dNatFine-++-map≤ {m} {n} c c' t t' f =
  let
    eq : m + n ≡ n + m
    eq = NatP.+-comm m n
    rx-cast : reverse (map f c ++ t) ≡ cast (sym eq) (reverse t ++ reverse (map f c))
    rx-cast = sym (cast-sym eq (reverse-++ eq (map f c) t))
    ry-cast : reverse (map f c' ++ t') ≡ cast (sym eq) (reverse t' ++ reverse (map f c'))
    ry-cast = sym (cast-sym eq (reverse-++ eq (map f c') t'))
    rx-map : reverse (map f c ++ t) ≡ cast (sym eq) (reverse t ++ map f (reverse c))
    rx-map = trans rx-cast (cong (cast (sym eq)) (cong (reverse t ++_) (sym (map-reverse f c))))
    ry-map : reverse (map f c' ++ t') ≡ cast (sym eq) (reverse t' ++ map f (reverse c'))
    ry-map = trans ry-cast (cong (cast (sym eq)) (cong (reverse t' ++_) (sym (map-reverse f c'))))
    step : AM.dNat (reverse t ++ map f (reverse c))
                   (reverse t' ++ map f (reverse c'))
           ≤ AM.dNat (reverse t ++ reverse c)
                    (reverse t' ++ reverse c')
    step = NatP.∸-monoʳ-≤ (n + m)
             (agreeDepth-++-map≤ (reverse t) (reverse t') (reverse c) (reverse c') f)

    rhs : dNatFine (c ++ t) (c' ++ t') ≡
          AM.dNat (reverse t ++ reverse c) (reverse t' ++ reverse c')
    rhs = dNatFine-++ c c' t t'
  in
  NatP.≤-trans
    (NatP.≤-reflexive (trans (cong₂ AM.dNat rx-map ry-map) (dNat-cast (sym eq) _ _)))
    (NatP.≤-trans step (NatP.≤-reflexive (sym rhs)))

dNatFine-++-shiftTail≤ :
  ∀ {m n : Nat} (c c' : Vec Trit m) (t t' : Vec Trit n) →
  dNatFine (c ++ TCP.shiftTail t) (c' ++ TCP.shiftTail t') ≤ dNatFine (c ++ t) (c' ++ t')
dNatFine-++-shiftTail≤ {m} {n} c c' t t'
  rewrite dNatFine-++ c c' (TCP.shiftTail t) (TCP.shiftTail t')
        | dNatFine-++ c c' t t' =
  let
    depth≤ :
      AM.agreeDepth (reverse t ++ reverse c) (reverse t' ++ reverse c')
      ≤ AM.agreeDepth (reverse (TCP.shiftTail t) ++ reverse c)
                     (reverse (TCP.shiftTail t') ++ reverse c')
    depth≤ =
      agreeDepth-++-mono
        (reverse t) (reverse t')
        (reverse (TCP.shiftTail t)) (reverse (TCP.shiftTail t'))
        (reverse c) (reverse c')
        (agreeDepthFine-shiftTail≥ t t')
  in
  NatP.∸-monoʳ-≤ (n + m) depth≤

ultrametricVec : ∀ {n : Nat} → UMetric.Ultrametric (Vec Trit n)
ultrametricVec {n} =
  record
    { d = dNatFine
    ; id-zero = λ x → UMetric.Ultrametric.id-zero AM.ultrametricVec (reverse x)
    ; symmetric = λ x y → UMetric.Ultrametric.symmetric AM.ultrametricVec (reverse x) (reverse y)
    ; ultratriangle = λ x y z → UMetric.Ultrametric.ultratriangle AM.ultrametricVec (reverse x) (reverse y) (reverse z)
    }
