module DASHI.Metric.AgreementUltrametric where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Nat using (_≤_; _<_; _≥_; _⊔_; _⊓_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties as NatP
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; map)
open import Contraction using (_≢_)
open import Data.Empty using (⊥-elim)
open import Ultrametric as UMetric
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Algebra.Trit using (inv)

-- Agreement depth (longest common prefix) for Vec Trit n.
agreeDepth : ∀ {n : Nat} → Vec Trit n → Vec Trit n → Nat
agreeDepth [] [] = zero
agreeDepth (neg ∷ xs) (neg ∷ ys) = suc (agreeDepth xs ys)
agreeDepth (zer ∷ xs) (zer ∷ ys) = suc (agreeDepth xs ys)
agreeDepth (pos ∷ xs) (pos ∷ ys) = suc (agreeDepth xs ys)
agreeDepth _ _ = zero

-- Distance: reversed depth.
dNat : ∀ {n : Nat} → Vec Trit n → Vec Trit n → Nat
dNat {n} x y = n ∸ agreeDepth x y

agreeDepth-self : ∀ {n : Nat} (x : Vec Trit n) → agreeDepth x x ≡ n
agreeDepth-self [] = refl
agreeDepth-self (neg ∷ xs) rewrite agreeDepth-self xs = refl
agreeDepth-self (zer ∷ xs) rewrite agreeDepth-self xs = refl
agreeDepth-self (pos ∷ xs) rewrite agreeDepth-self xs = refl

agreeDepth-sym : ∀ {n : Nat} (x y : Vec Trit n) → agreeDepth x y ≡ agreeDepth y x
agreeDepth-sym [] [] = refl
agreeDepth-sym (neg ∷ xs) (neg ∷ ys) rewrite agreeDepth-sym xs ys = refl
agreeDepth-sym (zer ∷ xs) (zer ∷ ys) rewrite agreeDepth-sym xs ys = refl
agreeDepth-sym (pos ∷ xs) (pos ∷ ys) rewrite agreeDepth-sym xs ys = refl
agreeDepth-sym (neg ∷ xs) (zer ∷ ys) = refl
agreeDepth-sym (neg ∷ xs) (pos ∷ ys) = refl
agreeDepth-sym (zer ∷ xs) (neg ∷ ys) = refl
agreeDepth-sym (zer ∷ xs) (pos ∷ ys) = refl
agreeDepth-sym (pos ∷ xs) (neg ∷ ys) = refl
agreeDepth-sym (pos ∷ xs) (zer ∷ ys) = refl

agreeDepth-inv :
  ∀ {n : Nat} (x y : Vec Trit n) →
  agreeDepth (map inv x) (map inv y) ≡ agreeDepth x y
agreeDepth-inv [] [] = refl
agreeDepth-inv (neg ∷ xs) (neg ∷ ys) rewrite agreeDepth-inv xs ys = refl
agreeDepth-inv (zer ∷ xs) (zer ∷ ys) rewrite agreeDepth-inv xs ys = refl
agreeDepth-inv (pos ∷ xs) (pos ∷ ys) rewrite agreeDepth-inv xs ys = refl
agreeDepth-inv (neg ∷ xs) (zer ∷ ys) = refl
agreeDepth-inv (neg ∷ xs) (pos ∷ ys) = refl
agreeDepth-inv (zer ∷ xs) (neg ∷ ys) = refl
agreeDepth-inv (zer ∷ xs) (pos ∷ ys) = refl
agreeDepth-inv (pos ∷ xs) (neg ∷ ys) = refl
agreeDepth-inv (pos ∷ xs) (zer ∷ ys) = refl

dNat-inv :
  ∀ {n : Nat} (x y : Vec Trit n) →
  dNat (map inv x) (map inv y) ≡ dNat x y
dNat-inv {n} x y = cong (λ k → n ∸ k) (agreeDepth-inv x y)

agreeDepth≤n : ∀ {n : Nat} (x y : Vec Trit n) → agreeDepth x y ≤ n
agreeDepth≤n [] [] = z≤n
agreeDepth≤n (neg ∷ xs) (neg ∷ ys) = s≤s (agreeDepth≤n xs ys)
agreeDepth≤n (zer ∷ xs) (zer ∷ ys) = s≤s (agreeDepth≤n xs ys)
agreeDepth≤n (pos ∷ xs) (pos ∷ ys) = s≤s (agreeDepth≤n xs ys)
agreeDepth≤n (neg ∷ xs) (zer ∷ ys) = z≤n
agreeDepth≤n (neg ∷ xs) (pos ∷ ys) = z≤n
agreeDepth≤n (zer ∷ xs) (neg ∷ ys) = z≤n
agreeDepth≤n (zer ∷ xs) (pos ∷ ys) = z≤n
agreeDepth≤n (pos ∷ xs) (neg ∷ ys) = z≤n
agreeDepth≤n (pos ∷ xs) (zer ∷ ys) = z≤n

agreeDepth-eq→eq : ∀ {n : Nat} (x y : Vec Trit n) → agreeDepth x y ≡ n → x ≡ y
agreeDepth-eq→eq [] [] _ = refl
agreeDepth-eq→eq (neg ∷ xs) (neg ∷ ys) eq =
  cong (neg ∷_) (agreeDepth-eq→eq xs ys (NatP.suc-injective eq))
agreeDepth-eq→eq (zer ∷ xs) (zer ∷ ys) eq =
  cong (zer ∷_) (agreeDepth-eq→eq xs ys (NatP.suc-injective eq))
agreeDepth-eq→eq (pos ∷ xs) (pos ∷ ys) eq =
  cong (pos ∷_) (agreeDepth-eq→eq xs ys (NatP.suc-injective eq))
agreeDepth-eq→eq (neg ∷ xs) (zer ∷ ys) ()
agreeDepth-eq→eq (neg ∷ xs) (pos ∷ ys) ()
agreeDepth-eq→eq (zer ∷ xs) (neg ∷ ys) ()
agreeDepth-eq→eq (zer ∷ xs) (pos ∷ ys) ()
agreeDepth-eq→eq (pos ∷ xs) (neg ∷ ys) ()
agreeDepth-eq→eq (pos ∷ xs) (zer ∷ ys) ()

dNat-zero→eq : ∀ {n : Nat} (x y : Vec Trit n) → dNat x y ≡ 0 → x ≡ y
dNat-zero→eq {n} x y d≡0 =
  let
    depth≥ : n ≤ agreeDepth x y
    depth≥ = NatP.m∸n≡0⇒m≤n d≡0
    depth≤ : agreeDepth x y ≤ n
    depth≤ = agreeDepth≤n x y
    depth≡ : agreeDepth x y ≡ n
    depth≡ = NatP.≤-antisym depth≤ depth≥
  in
  agreeDepth-eq→eq x y depth≡

dNat-nonzero : ∀ {n : Nat} {x y : Vec Trit n} → x ≢ y → dNat x y ≢ 0
dNat-nonzero x≢y d≡0 = x≢y (dNat-zero→eq _ _ d≡0)

dNat-positive : ∀ {n : Nat} {x y : Vec Trit n} → x ≢ y → 0 < dNat x y
dNat-positive x≢y = NatP.n≢0⇒n>0 (dNat-nonzero x≢y)

-- Strong triangle inequality for agreement depth (prefix metric).
agreeDepth-triangle :
  ∀ {n : Nat} (x y z : Vec Trit n) →
  (agreeDepth x y ⊓ agreeDepth y z) ≤ agreeDepth x z
agreeDepth-triangle [] [] [] = z≤n
agreeDepth-triangle (x ∷ xs) (y ∷ ys) (z ∷ zs) with x | y | z
... | neg | neg | neg =
  s≤s (agreeDepth-triangle xs ys zs)
... | zer | zer | zer =
  s≤s (agreeDepth-triangle xs ys zs)
... | pos | pos | pos =
  s≤s (agreeDepth-triangle xs ys zs)
... | neg | neg | zer = z≤n
... | neg | neg | pos = z≤n
... | zer | zer | neg = z≤n
... | zer | zer | pos = z≤n
... | pos | pos | neg = z≤n
... | pos | pos | zer = z≤n
... | neg | zer | _ = z≤n
... | neg | pos | _ = z≤n
... | zer | neg | _ = z≤n
... | zer | pos | _ = z≤n
... | pos | neg | _ = z≤n
... | pos | zer | _ = z≤n

-- Ultrametric inequality: d x z ≤ max (d x y) (d y z)
ultraNat : ∀ {n : Nat} (x y z : Vec Trit n) → dNat x z ≤ (dNat x y ⊔ dNat y z)
ultraNat {n} x y z with NatP.≤-total (agreeDepth x y) (agreeDepth y z)
... | inj₁ xy≤yz =
  let
    min≡ : (agreeDepth x y ⊓ agreeDepth y z) ≡ agreeDepth x y
    min≡ = NatP.m≤n⇒m⊓n≡m xy≤yz
    depth≤ : agreeDepth x y ≤ agreeDepth x z
    depth≤ = NatP.≤-trans (NatP.≤-reflexive (sym min≡)) (agreeDepth-triangle x y z)
    depth≥ : agreeDepth x z ≥ agreeDepth x y
    depth≥ = depth≤
    step1 : dNat x z ≤ dNat x y
    step1 = NatP.∸-mono (NatP.≤-refl {n}) depth≥
    step2 : dNat x z ≤ (dNat x y ⊔ dNat y z)
    step2 = NatP.≤-trans step1 (NatP.m≤m⊔n (dNat x y) (dNat y z))
  in step2
... | inj₂ yz≤xy =
  let
    min≡ : (agreeDepth x y ⊓ agreeDepth y z) ≡ agreeDepth y z
    min≡ = NatP.m≥n⇒m⊓n≡n yz≤xy
    depth≤ : agreeDepth y z ≤ agreeDepth x z
    depth≤ = NatP.≤-trans (NatP.≤-reflexive (sym min≡)) (agreeDepth-triangle x y z)
    depth≥ : agreeDepth x z ≥ agreeDepth y z
    depth≥ = depth≤
    step1 : dNat x z ≤ dNat y z
    step1 = NatP.∸-mono (NatP.≤-refl {n}) depth≥
    step2 : dNat x z ≤ (dNat x y ⊔ dNat y z)
    step2 = NatP.≤-trans step1 (NatP.m≤n⊔m (dNat x y) (dNat y z))
  in step2


------------------------------------------------------------------------
-- Ultrametric isosceles consequence.
--
-- If one leg is strictly shorter than another, the third leg equals the
-- longer one.  Equivalently, the two largest distances in a non-equilateral
-- ultrametric triangle coincide.
------------------------------------------------------------------------

dNat-sym :
  ∀ {n : Nat} (x y : Vec Trit n) →
  dNat x y ≡ dNat y x
dNat-sym {n} x y =
  cong (λ k → n ∸ k) (agreeDepth-sym x y)

strictLegForcesLongSideEquality :
  ∀ {n : Nat} (x y z : Vec Trit n) →
  dNat x y < dNat y z →
  dNat x z ≡ dNat y z
strictLegForcesLongSideEquality x y z xy<yz
  with NatP.≤-total (dNat x z) (dNat x y)
... | inj₁ xz≤xy =
  ⊥-elim (NatP.<⇒≱ xy<yz yz≤xy)
  where
    maxYXZ≡XY :
      (dNat y x ⊔ dNat x z) ≡ dNat x y
    maxYXZ≡XY
      rewrite dNat-sym y x =
      NatP.m≥n⇒m⊔n≡m xz≤xy

    yz≤xy : dNat y z ≤ dNat x y
    yz≤xy =
      subst
        (λ bound → dNat y z ≤ bound)
        maxYXZ≡XY
        (ultraNat y x z)

... | inj₂ xy≤xz =
  NatP.≤-antisym xz≤yz yz≤xz
  where
    xy≤yz : dNat x y ≤ dNat y z
    xy≤yz = NatP.<⇒≤ xy<yz

    maxXYZ≡YZ :
      (dNat x y ⊔ dNat y z) ≡ dNat y z
    maxXYZ≡YZ = NatP.m≤n⇒m⊔n≡n xy≤yz

    xz≤yz : dNat x z ≤ dNat y z
    xz≤yz =
      subst
        (λ bound → dNat x z ≤ bound)
        maxXYZ≡YZ
        (ultraNat x y z)

    maxYXZ≡XZ :
      (dNat y x ⊔ dNat x z) ≡ dNat x z
    maxYXZ≡XZ
      rewrite dNat-sym y x =
      NatP.m≤n⇒m⊔n≡n xy≤xz

    yz≤xz : dNat y z ≤ dNat x z
    yz≤xz =
      subst
        (λ bound → dNat y z ≤ bound)
        maxYXZ≡XZ
        (ultraNat y x z)

ultrametricVec : ∀ {n : Nat} → UMetric.Ultrametric (Vec Trit n)
ultrametricVec {n} =
  record
    { d = dNat
    ; id-zero = λ x →
        trans
          (cong (λ k → n ∸ k) (agreeDepth-self x))
          (NatP.n∸n≡0 n)
    ; symmetric = λ x y →
        cong (λ k → n ∸ k) (agreeDepth-sym x y)
    ; ultratriangle = ultraNat
    }
