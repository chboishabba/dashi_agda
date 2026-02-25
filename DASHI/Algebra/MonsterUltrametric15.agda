module DASHI.Algebra.MonsterUltrametric15 where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Nat using (_≤_; _<_; _⊔_; _⊓_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties as NatP using (≤-refl; ≤-trans; ≤-reflexive; n∸n≡0; ∸-monoʳ-≤; ∸-distribˡ-⊓-⊔; ⊓-zeroˡ; ⊓-zeroʳ)
open import Data.Vec using (Vec; []; _∷_)
-- Removed Relation.Binary.Reasoning.Base.Raw as it's not needed here.
-- Removed Relation.Binary.Reasoning.Nat as it's not needed here.

open import Ultrametric
open import DASHI.Algebra.MonsterMask15 using (Mask15)

lcpLen : ∀ {n} → Vec Bool n → Vec Bool n → Nat
lcpLen [] [] = 0
lcpLen (true  ∷ xs) (true  ∷ ys) = suc (lcpLen xs ys)
lcpLen (false ∷ xs) (false ∷ ys) = suc (lcpLen xs ys)
lcpLen (_ ∷ _) (_ ∷ _) = 0

len : ∀ {n} → Vec Bool n → Nat
len []       = 0
len (_ ∷ xs) = suc (len xs)

dMask : ∀ {n} → Vec Bool n → Vec Bool n → Nat
dMask {n} x y = len {n} x ∸ lcpLen x y

-- id-zero
lcpLen-self-eq : ∀ {n} (m : Vec Bool n) → lcpLen m m ≡ len {n} m
lcpLen-self-eq [] = refl
lcpLen-self-eq (true  ∷ xs) = cong suc (lcpLen-self-eq xs)
lcpLen-self-eq (false ∷ xs) = cong suc (lcpLen-self-eq xs)

id-zeroMask : ∀ m → dMask {15} m m ≡ 0
id-zeroMask m =
  let
    step : dMask {15} m m ≡ len {15} m ∸ len {15} m
    step = cong (λ k → len {15} m ∸ k) (lcpLen-self-eq m)
  in
  trans step (n∸n≡0 (len {15} m))

-- symmetric
lcpLen-symmetric : ∀ {n} (x y : Vec Bool n) → lcpLen x y ≡ lcpLen y x
lcpLen-symmetric [] [] = refl
lcpLen-symmetric (x ∷ xs) (y ∷ ys) with x | y
... | true | true = cong suc (lcpLen-symmetric xs ys)
... | false | false = cong suc (lcpLen-symmetric xs ys)
... | true | false = refl
... | false | true = refl

len-const : ∀ {n} (x : Vec Bool n) → len x ≡ n
len-const [] = refl
len-const (_ ∷ xs) = cong suc (len-const xs)

dMask-symmetric : ∀ {n} (x y : Vec Bool n) → dMask {n} x y ≡ dMask {n} y x
dMask-symmetric {n} x y =
  let
    lenx≡n : len {n} x ≡ n
    lenx≡n = len-const x
    leny≡n : len {n} y ≡ n
    leny≡n = len-const y
  in
  trans (cong (λ k → len {n} x ∸ k) (lcpLen-symmetric x y))
        (trans (cong (λ k → k ∸ lcpLen y x) lenx≡n)
               (cong (λ k → k ∸ lcpLen y x) (sym leny≡n)))

symMask : ∀ {n} (x y : Vec Bool n) → dMask {n} x y ≡ dMask {n} y x
symMask = dMask-symmetric

-- ultratriangle
lcpLen-ultratriangle :
  ∀ {n} (x y z : Vec Bool n) →
  (lcpLen x y ⊓ lcpLen y z) ≤ lcpLen x z
lcpLen-ultratriangle [] [] [] = z≤n
lcpLen-ultratriangle (x ∷ xs) (y ∷ ys) (z ∷ zs) with x | y | z
... | true  | true  | true  = s≤s (lcpLen-ultratriangle xs ys zs)
... | false | false | false = s≤s (lcpLen-ultratriangle xs ys zs)
... | true  | false | _     rewrite ⊓-zeroˡ (lcpLen (y ∷ ys) (z ∷ zs)) = z≤n
... | false | true  | _     rewrite ⊓-zeroˡ (lcpLen (y ∷ ys) (z ∷ zs)) = z≤n
... | true  | true  | false rewrite ⊓-zeroʳ (lcpLen (x ∷ xs) (y ∷ ys)) = z≤n
... | false | false | true  rewrite ⊓-zeroʳ (lcpLen (x ∷ xs) (y ∷ ys)) = z≤n

ultraMask : ∀ x y z → dMask {15} x z ≤ (dMask {15} x y ⊔ dMask {15} y z)
ultraMask x y z =
  let
    a = lcpLen x y
    b = lcpLen y z
    c = lcpLen x z
    lenx = len {15} x
    leny = len {15} y

    lenx≡n : lenx ≡ 15
    lenx≡n = len-const x

    leny≡n : leny ≡ 15
    leny≡n = len-const y

    lenx≡leny : lenx ≡ leny
    lenx≡leny = trans lenx≡n (sym leny≡n)

    c≥min : (a ⊓ b) ≤ c
    c≥min = lcpLen-ultratriangle x y z

    step1 : (lenx ∸ c) ≤ (lenx ∸ (a ⊓ b))
    step1 = ∸-monoʳ-≤ lenx c≥min

    step2 : (lenx ∸ (a ⊓ b)) ≡ (lenx ∸ a) ⊔ (lenx ∸ b)
    step2 = ∸-distribˡ-⊓-⊔ lenx a b

    step2' : (lenx ∸ (a ⊓ b)) ≡ (lenx ∸ a) ⊔ (leny ∸ b)
    step2' = trans step2 (cong (λ k → (lenx ∸ a) ⊔ (k ∸ b)) lenx≡leny)
  in
  NatP.≤-trans step1 (NatP.≤-reflexive step2')

UMask15 : Ultrametric Mask15
UMask15 = record
  { d             = dMask {15}
  ; id-zero       = id-zeroMask
  ; symmetric     = symMask {15}
  ; ultratriangle = ultraMask
  }
