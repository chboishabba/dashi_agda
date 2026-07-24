module DASHI.Cognition.TernaryDerivationUltrametric where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; _⊔_; _⊓_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties as NatP using
  ( ≤-trans
  ; ≤-reflexive
  ; n∸n≡0
  ; ∸-monoʳ-≤
  ; ∸-distribˡ-⊓-⊔
  ; ⊓-zeroˡ
  ; ⊓-zeroʳ
  )
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.BalancedTernary as BT
open import Ultrametric using (Ultrametric)

------------------------------------------------------------------------
-- The 3-adic address topology is represented constructively by longest
-- common prefixes.  Larger common-prefix depth means greater 3-adic
-- closeness; dTrit is the equivalent finite ultrametric distance code.
------------------------------------------------------------------------

lcpLen : ∀ {n} → Vec BT.Trit n → Vec BT.Trit n → Nat
lcpLen [] [] = 0
lcpLen (BT.neg  ∷ xs) (BT.neg  ∷ ys) = suc (lcpLen xs ys)
lcpLen (BT.zero ∷ xs) (BT.zero ∷ ys) = suc (lcpLen xs ys)
lcpLen (BT.pos  ∷ xs) (BT.pos  ∷ ys) = suc (lcpLen xs ys)
lcpLen (_ ∷ _) (_ ∷ _) = 0

len : ∀ {n} → Vec BT.Trit n → Nat
len [] = 0
len (_ ∷ xs) = suc (len xs)

dTrit : ∀ {n} → Vec BT.Trit n → Vec BT.Trit n → Nat
dTrit {n} x y = len {n} x ∸ lcpLen x y

lcpLen-self : ∀ {n} (x : Vec BT.Trit n) → lcpLen x x ≡ len x
lcpLen-self [] = refl
lcpLen-self (BT.neg ∷ xs) = cong suc (lcpLen-self xs)
lcpLen-self (BT.zero ∷ xs) = cong suc (lcpLen-self xs)
lcpLen-self (BT.pos ∷ xs) = cong suc (lcpLen-self xs)

id-zeroTrit : ∀ {n} (x : Vec BT.Trit n) → dTrit x x ≡ 0
id-zeroTrit {n} x =
  trans
    (cong (λ k → len {n} x ∸ k) (lcpLen-self x))
    (n∸n≡0 (len {n} x))

lcpLen-symmetric :
  ∀ {n} (x y : Vec BT.Trit n) → lcpLen x y ≡ lcpLen y x
lcpLen-symmetric [] [] = refl
lcpLen-symmetric (BT.neg ∷ xs) (BT.neg ∷ ys) =
  cong suc (lcpLen-symmetric xs ys)
lcpLen-symmetric (BT.zero ∷ xs) (BT.zero ∷ ys) =
  cong suc (lcpLen-symmetric xs ys)
lcpLen-symmetric (BT.pos ∷ xs) (BT.pos ∷ ys) =
  cong suc (lcpLen-symmetric xs ys)
lcpLen-symmetric (BT.neg ∷ xs) (BT.zero ∷ ys) = refl
lcpLen-symmetric (BT.neg ∷ xs) (BT.pos ∷ ys) = refl
lcpLen-symmetric (BT.zero ∷ xs) (BT.neg ∷ ys) = refl
lcpLen-symmetric (BT.zero ∷ xs) (BT.pos ∷ ys) = refl
lcpLen-symmetric (BT.pos ∷ xs) (BT.neg ∷ ys) = refl
lcpLen-symmetric (BT.pos ∷ xs) (BT.zero ∷ ys) = refl

len-const : ∀ {n} (x : Vec BT.Trit n) → len x ≡ n
len-const [] = refl
len-const (_ ∷ xs) = cong suc (len-const xs)

dTrit-symmetric :
  ∀ {n} (x y : Vec BT.Trit n) → dTrit x y ≡ dTrit y x
dTrit-symmetric {n} x y =
  let
    lenx≡n : len x ≡ n
    lenx≡n = len-const x

    leny≡n : len y ≡ n
    leny≡n = len-const y
  in
  trans
    (cong (λ k → len x ∸ k) (lcpLen-symmetric x y))
    (trans
      (cong (λ k → k ∸ lcpLen y x) lenx≡n)
      (cong (λ k → k ∸ lcpLen y x) (sym leny≡n)))

lcpLen-ultratriangle :
  ∀ {n} (x y z : Vec BT.Trit n) →
  (lcpLen x y ⊓ lcpLen y z) ≤ lcpLen x z
lcpLen-ultratriangle [] [] [] = z≤n
lcpLen-ultratriangle (x ∷ xs) (y ∷ ys) (z ∷ zs) with x | y | z
... | BT.neg  | BT.neg  | BT.neg  = s≤s (lcpLen-ultratriangle xs ys zs)
... | BT.zero | BT.zero | BT.zero = s≤s (lcpLen-ultratriangle xs ys zs)
... | BT.pos  | BT.pos  | BT.pos  = s≤s (lcpLen-ultratriangle xs ys zs)
... | BT.neg  | BT.zero | _ rewrite ⊓-zeroˡ (lcpLen (y ∷ ys) (z ∷ zs)) = z≤n
... | BT.neg  | BT.pos  | _ rewrite ⊓-zeroˡ (lcpLen (y ∷ ys) (z ∷ zs)) = z≤n
... | BT.zero | BT.neg  | _ rewrite ⊓-zeroˡ (lcpLen (y ∷ ys) (z ∷ zs)) = z≤n
... | BT.zero | BT.pos  | _ rewrite ⊓-zeroˡ (lcpLen (y ∷ ys) (z ∷ zs)) = z≤n
... | BT.pos  | BT.neg  | _ rewrite ⊓-zeroˡ (lcpLen (y ∷ ys) (z ∷ zs)) = z≤n
... | BT.pos  | BT.zero | _ rewrite ⊓-zeroˡ (lcpLen (y ∷ ys) (z ∷ zs)) = z≤n
... | BT.neg  | BT.neg  | BT.zero rewrite ⊓-zeroʳ (lcpLen (x ∷ xs) (y ∷ ys)) = z≤n
... | BT.neg  | BT.neg  | BT.pos rewrite ⊓-zeroʳ (lcpLen (x ∷ xs) (y ∷ ys)) = z≤n
... | BT.zero | BT.zero | BT.neg rewrite ⊓-zeroʳ (lcpLen (x ∷ xs) (y ∷ ys)) = z≤n
... | BT.zero | BT.zero | BT.pos rewrite ⊓-zeroʳ (lcpLen (x ∷ xs) (y ∷ ys)) = z≤n
... | BT.pos  | BT.pos  | BT.neg rewrite ⊓-zeroʳ (lcpLen (x ∷ xs) (y ∷ ys)) = z≤n
... | BT.pos  | BT.pos  | BT.zero rewrite ⊓-zeroʳ (lcpLen (x ∷ xs) (y ∷ ys)) = z≤n

ultraTrit :
  ∀ {n} (x y z : Vec BT.Trit n) →
  dTrit x z ≤ (dTrit x y ⊔ dTrit y z)
ultraTrit {n} x y z =
  let
    a = lcpLen x y
    b = lcpLen y z
    c = lcpLen x z
    lenx = len x
    leny = len y

    lenx≡n : lenx ≡ n
    lenx≡n = len-const x

    leny≡n : leny ≡ n
    leny≡n = len-const y

    lenx≡leny : lenx ≡ leny
    lenx≡leny = trans lenx≡n (sym leny≡n)

    c≥min : (a ⊓ b) ≤ c
    c≥min = lcpLen-ultratriangle x y z

    step1 : (lenx ∸ c) ≤ (lenx ∸ (a ⊓ b))
    step1 = ∸-monoʳ-≤ lenx c≥min

    step2 : (lenx ∸ (a ⊓ b)) ≡ (lenx ∸ a) ⊔ (lenx ∸ b)
    step2 = ∸-distribˡ-⊓-⊔ lenx a b

    step2′ : (lenx ∸ (a ⊓ b)) ≡ (lenx ∸ a) ⊔ (leny ∸ b)
    step2′ =
      trans step2
        (cong (λ k → (lenx ∸ a) ⊔ (k ∸ b)) lenx≡leny)
  in
  NatP.≤-trans step1 (NatP.≤-reflexive step2′)

TritUltrametric : ∀ {n} → Ultrametric (Vec BT.Trit n)
TritUltrametric = record
  { d = dTrit
  ; id-zero = id-zeroTrit
  ; symmetric = dTrit-symmetric
  ; ultratriangle = ultraTrit
  }
