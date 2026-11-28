module DASHI.Moonshine.JInvariantBishopLambertDegreeChartExact where

-- SOURCE-WRITTEN, kernel pending. Classical product-degree partition
-- m*d=r on the SAME factor-pair scan. The rectangle and triangular
-- degree prefixes are unique finite lists on literal positive keys.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s; _⊔_)
import Data.Nat.Properties as NP
open import Data.List.Base using (List; []; _∷_; _++_; map; cartesianProductWith)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using
  (∈-map⁺; ∈-map⁻; ∈-++⁻; ∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.AllPairs.Core as AP
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UP
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; subst; _≢_)
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as F
import DASHI.Mathematics.NumberTheory.FiniteDependentPairEnumerationExact as Dep
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as One
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as H

Key : Set
Key = Nat × Nat

degree : Key → Nat
degree (m , d) = m * d

Positive : Key → Set
Positive (m , d) = 1 ≤ m × 1 ≤ d

degreePositive : ∀ x → Positive x → 1 ≤ degree x
degreePositive (zero , d) (() , hd)
degreePositive (suc m , zero) (hm , ())
degreePositive (suc m , suc d) (hm , hd) = NP.≤-trans hm (NP.m≤m*n (suc m) (suc d))

mBelow : ∀ x → Positive x → proj₁ x ≤ degree x
mBelow (m , zero) (hm , ())
mBelow (m , suc d) h = NP.m≤m*n m (suc d)

dBelow : ∀ x → Positive x → proj₂ x ≤ degree x
dBelow (m , d) h = NP.≤-trans (mBelow (d , m) (proj₂ h , proj₁ h))
  (NP.≤-reflexive (NP.*-comm d m))

key : ∀ {r} → F.PositiveFactorPair r → Key
key p = suc (F.predecessor p) , F.divisor p

keyPositive : ∀ {r} (p : F.PositiveFactorPair r) → Positive (key p)
keyPositive p = s≤s z≤n , F.divisorPositive p

keyGrade : ∀ {r} (p : F.PositiveFactorPair r) → degree (key p) ≡ r
keyGrade p = sym (F.productExact p)

keyInject : ∀ {r} {p q : F.PositiveFactorPair r} → key p ≡ key q → p ≡ q
keyInject {p = F.positiveFactorPair d h b m e}
  {q = F.positiveFactorPair .d h' b' .m e'} refl
  rewrite NP.≤-irrelevant h h' | NP.≤-irrelevant b b' | NP.≡-irrelevant e e' = refl

fibre : Nat → List Key
fibre n = map key (F.positiveFactorPairs (suc n) (s≤s z≤n))

fibreUnique : ∀ n → Unique (fibre n)
fibreUnique n = UP.map⁺ keyInject (F.positiveFactorPairsUnique (suc n) (s≤s z≤n))

fibreSound : ∀ n {x} → x ∈ fibre n → Positive x × (degree x ≡ suc n)
fibreSound n h with ∈-map⁻ key h
... | p , _ , refl = keyPositive p , keyGrade p

fibreComplete : ∀ n x → Positive x → degree x ≡ suc n → x ∈ fibre n
fibreComplete n (zero , d) (() , hd) g
fibreComplete n (suc m , d) (hm , hd) g
  with F.positiveFactorPairCoordinatesComplete (suc n) (s≤s z≤n) {d = d} {predecessor = m}
    hd (subst (d ≤_) g (dBelow (suc m , d) (hm , hd))) (sym g)
... | p , pm , de , me = subst (_∈ fibre n) (cong₂ _,_ (cong suc me) de)
  (∈-map⁺ key pm)

triangle : Nat → List Key
triangle zero = []
triangle (suc n) = triangle n ++ fibre n

triangleSound : ∀ n {x} → x ∈ triangle n → Positive x × (degree x ≤ n)
triangleSound zero ()
triangleSound (suc n) h with ∈-++⁻ (triangle n) h
... | inj₁ m with triangleSound n m
...   | p , g = p , NP.≤-step g
triangleSound (suc n) h | inj₂ m with fibreSound n m
... | p , g = p , NP.≤-reflexive g

triangleComplete : ∀ n x → Positive x → degree x ≤ n → x ∈ triangle n
triangleComplete zero x p h = ⊥-elim (impossible (NP.≤-trans (degreePositive x p) h))
  where
  impossible : 1 ≤ zero → ⊥
  impossible ()
triangleComplete (suc n) x p h with NP.m≤n⇒m<n∨m≡n h
... | inj₁ lt = Dep.appendMemberLeft (triangleComplete n x p (One.≤-pred lt))
... | inj₂ eq = Dep.appendMemberRight (triangle n) (fibreComplete n x p eq)

triangleUnique : ∀ n → Unique (triangle n)
triangleUnique zero = AP.[]
triangleUnique (suc n) = Dep.uniqueAppendDisjoint (triangleUnique n) (fibreUnique n) cross
  where
  cross : ∀ {x y} → x ∈ triangle n → y ∈ fibre n → x ≢ y
  cross {x} xm ym refl = NP.1+n≰n
    (subst (_≤ n) (proj₂ (fibreSound n ym)) (proj₂ (triangleSound n xm)))

pairInject : ∀ {a b c d : Nat} → (a , b) ≡ (c , d) → (a ≡ c) × (b ≡ d)
pairInject refl = refl , refl

rectangle : Nat → Nat → List Key
rectangle n m = cartesianProductWith _,_ (H.oneTo n) (H.oneTo m)

rectUnique : ∀ n m → Unique (rectangle n m)
rectUnique n m = UP.cartesianProductWith⁺ _,_ pairInject (One.oneToUnique n) (One.oneToUnique m)

rectSound : ∀ n m {x} → x ∈ rectangle n m →
  Positive x × (proj₁ x ≤ n) × (proj₂ x ≤ m)
rectSound n m h with ∈-cartesianProductWith⁻ _,_ (H.oneTo n) (H.oneTo m) h
... | a , b , am , bm , refl =
  (One.oneToPositive am , One.oneToPositive bm) , One.oneToUpperBound am , One.oneToUpperBound bm

rectComplete : ∀ n m x → Positive x → proj₁ x ≤ n → proj₂ x ≤ m → x ∈ rectangle n m
rectComplete n m (a , b) (ha , hb) am bm =
  ∈-cartesianProductWith⁺ _,_ (One.oneToComplete ha am) (One.oneToComplete hb bm)

-- The hyperbolic product-degree triangle is enclosed by a cofinal box,
-- itself enclosed by the product-degree triangle at n*m.
inner : ∀ n m {x} → x ∈ triangle n → x ∈ rectangle n (n ⊔ m)
inner n m {x} h =
  let p , g = triangleSound n h
  in rectComplete n (n ⊔ m) x p
    (NP.≤-trans (mBelow x p) g)
    (NP.≤-trans (NP.≤-trans (dBelow x p) g) (NP.m≤m⊔n n m))

outer : ∀ n m {x} → x ∈ rectangle n (n ⊔ m) → x ∈ triangle (n * (n ⊔ m))
outer n m {x} h =
  let p , hm , hd = rectSound n (n ⊔ m) h
  in triangleComplete (n * (n ⊔ m)) x p (NP.*-mono-≤ hm hd)

outerRadius : ∀ n m → n ≤ n * (n ⊔ m)
outerRadius zero m = z≤n
outerRadius (suc n) m = NP.≤-trans (NP.m≤m*n (suc n) (suc n))
  (NP.*-monoʳ-≤ (suc n) (NP.m≤m⊔n (suc n) m))
