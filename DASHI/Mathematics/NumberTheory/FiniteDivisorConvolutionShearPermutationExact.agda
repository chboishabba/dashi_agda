module DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearPermutationExact where

-- SOURCE-WRITTEN, UNCOMPILED. Actual unique positive grade enumeration
-- and both chart permutations; reuse OneTo, stdlib product/filter and
-- the existing unique-membership permutation owner.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as N
open import Data.List.Base using (List; []; _∷_; map; filter; cartesianProductWith)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as M
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AP
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as U
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as One
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
open import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearExact
  using (Quad; quad; a; b; x; y; grade; Positive;
    left; right; leftBack; rightBack;
    leftGrade; rightGrade; leftBackGrade; rightBackGrade;
    leftInverse; rightInverse; leftRightInverse; rightRightInverse;
    leftPositive; rightPositive; leftBackPositive; rightBackPositive;
    leftTarget; rightTarget; leftSource; rightSource)

Pair : Set
Pair = Nat × Nat
pack : Pair → Pair → Quad
pack (a , b) (x , y) = quad a b x y

pairInjective : ∀ {a b c d : Nat} → (a , b) ≡ (c , d) → (a ≡ c) × (b ≡ d)
pairInjective refl = refl , refl

packInjective : ∀ {u v w z : Pair} → pack u v ≡ pack w z →
  (u ≡ w) × (v ≡ z)
packInjective {a , b} {x , y} {a′ , b′} {x′ , y′} refl = refl , refl

pairs : Nat → List Pair
pairs n = cartesianProductWith _,_ (Hecke.oneTo n) (Hecke.oneTo n)

allQuads : Nat → List Quad
allQuads n = cartesianProductWith pack (pairs n) (pairs n)

pairsUnique : ∀ n → Unique (pairs n)
pairsUnique n = U.cartesianProductWith⁺ _,_ pairInjective (One.oneToUnique n) (One.oneToUnique n)

quadsUnique : ∀ n → Unique (allQuads n)
quadsUnique n = U.cartesianProductWith⁺ pack packInjective (pairsUnique n) (pairsUnique n)

pairPositive : ∀ {n u v} → (u , v) ∈ pairs n → (zero < u) × (zero < v)
pairPositive {n} m with M.∈-cartesianProductWith⁻ _,_ (Hecke.oneTo n) (Hecke.oneTo n) m
... | u , v , hu , hv , refl = One.oneToPositive hu , One.oneToPositive hv

allPositive : ∀ {n q} → q ∈ allQuads n → Positive q
allPositive {n} m with M.∈-cartesianProductWith⁻ pack (pairs n) (pairs n) m
... | (a , b) , (x , y) , hab , hxy , refl =
  proj₁ (pairPositive hab) , proj₂ (pairPositive hab) ,
  proj₁ (pairPositive hxy) , proj₂ (pairPositive hxy)

mulBoundLeft : (a x : Nat) → zero < x → a ≤ a * x
mulBoundLeft a zero ()
mulBoundLeft a (suc x) _ = N.m≤m*n a (suc x)

mulBoundRight : (a x : Nat) → zero < a → x ≤ a * x
mulBoundRight zero x ()
mulBoundRight (suc a) x _ = N.m≤n*m x (suc a)

allComplete : ∀ {n q} → Positive q → grade q ≡ n → q ∈ allQuads n
allComplete {q = quad a b x y} (pa , pb , px , py) e =
  M.∈-cartesianProductWith⁺ pack
    (M.∈-cartesianProductWith⁺ _,_
      (One.oneToComplete pa (subst (a ≤_) e (N.≤-trans (mulBoundLeft a x px) (N.m≤m+n (a * x) (b * y)))))
      (One.oneToComplete pb (subst (b ≤_) e (N.≤-trans (mulBoundLeft b y py) (N.m≤n+m (b * y) (a * x))))))
    (M.∈-cartesianProductWith⁺ _,_
      (One.oneToComplete px (subst (x ≤_) e (N.≤-trans (mulBoundRight a x pa) (N.m≤m+n (a * x) (b * y)))))
      (One.oneToComplete py (subst (y ≤_) e (N.≤-trans (mulBoundRight b y pb) (N.m≤n+m (b * y) (a * x))))))

grade? : ∀ n q → Dec (grade q ≡ n)
grade? n q = grade q N.≟ n

omega : Nat → List Quad
omega n = filter (grade? n) (allQuads n)

omegaUnique : ∀ n → Unique (omega n)
omegaUnique n = U.filter⁺ (grade? n) (quadsUnique n)

omegaRead : ∀ {n q} → q ∈ omega n → Positive q × (grade q ≡ n)
omegaRead {n} m = let h = M.∈-filter⁻ (grade? n) m in allPositive (proj₁ h) , proj₂ h

omegaWrite : ∀ {n q} → Positive q → grade q ≡ n → q ∈ omega n
omegaWrite {n} p e = M.∈-filter⁺ (grade? n) (allComplete p e) e

-- A genuine restricted injectivity proof: truncated subtraction is
-- NOT claimed injective outside the strict positive source chart.
mapUniqueOn : ∀ {A B : Set} (f : A → B) (xs : List A) →
  Unique xs →
  (∀ {u v} → u ∈ xs → v ∈ xs → f u ≡ f v → u ≡ v) →
  Unique (map f xs)
mapUniqueOn f [] AP.[] inj = AP.[]
mapUniqueOn f (x ∷ xs) (AP._∷_ fresh unique) inj =
  AP._∷_
    (All.tabulate (λ m e →
      let v , hv , ev = M.∈-map⁻ m
      in All.lookup fresh hv
        (inj (Any.here refl) (Any.there hv) (trans e ev))))
    (mapUniqueOn f xs unique (λ u v → inj (Any.there u) (Any.there v)))

-- Shared chart compiler over the literal omega list. The parameters
-- are the actual forward/backward maps and their coordinate proofs,
-- instantiated immediately below, not a premise of the endpoint.
module Chart
  (P Q : Quad → Set)
  (P? : ∀ q → Dec (P q)) (Q? : ∀ q → Dec (Q q))
  (f g : Quad → Quad)
  (fg : ∀ q → P q → g (f q) ≡ q)
  (gf : ∀ q → Q q → f (g q) ≡ q)
  (fp : ∀ q → Positive q → P q → Positive (f q))
  (gp : ∀ q → Positive q → Q q → Positive (g q))
  (fe : ∀ q → P q → grade (f q) ≡ grade q)
  (ge : ∀ q → Q q → grade (g q) ≡ grade q)
  (fq : ∀ q → Positive q → Q (f q))
  (gq : ∀ q → Positive q → P (g q)) where

  source target : Nat → List Quad
  source n = filter P? (omega n)
  target n = filter Q? (omega n)

  sourceRead : ∀ {n q} → q ∈ source n → Positive q × ((grade q ≡ n) × P q)
  sourceRead m =
    let o , p = M.∈-filter⁻ P? m
        h , e = omegaRead o
    in h , e , p

  targetRead : ∀ {n q} → q ∈ target n → Positive q × ((grade q ≡ n) × Q q)
  targetRead m =
    let o , p = M.∈-filter⁻ Q? m
        h , e = omegaRead o
    in h , e , p

  forward : ∀ {n q} → q ∈ source n → f q ∈ target n
  forward {n} {q} m =
    let h , e , p = sourceRead m
    in M.∈-filter⁺ Q? (omegaWrite (fp q h p) (trans (fe q p) e)) (fq q h)

  backward : ∀ {n q} → q ∈ target n → g q ∈ source n
  backward {n} {q} m =
    let h , e , p = targetRead m
    in M.∈-filter⁺ P? (omegaWrite (gp q h p) (trans (ge q p) e)) (gq q h)

  mappedUnique : ∀ n → Unique (map f (source n))
  mappedUnique n =
    mapUniqueOn f (source n) (U.filter⁺ P? (omegaUnique n))
      (λ {u} {v} mu mv eq →
        trans (sym (fg u (proj₂ (M.∈-filter⁻ P? mu))))
          (trans (cong g eq) (fg v (proj₂ (M.∈-filter⁻ P? mv)))))

  mappedForward : ∀ {n q} → q ∈ map f (source n) → q ∈ target n
  mappedForward {n} m with M.∈-map⁻ m
  ... | v , hv , e = subst (λ z → z ∈ target n) (sym e) (forward hv)

  mappedBackward : ∀ {n q} → q ∈ target n → q ∈ map f (source n)
  mappedBackward {n} {q} m =
    subst (λ z → z ∈ map f (source n))
      (gf q (proj₂ (M.∈-filter⁻ Q? m)))
      (M.∈-map⁺ (backward m))

  permutation : ∀ n → map f (source n) Perm.↭ target n
  permutation n = Reindex.uniqueMembershipEquivalenceToPermutation
    (mappedUnique n) (U.filter⁺ Q? (omegaUnique n)) mappedForward mappedBackward

module L = Chart (λ q → b q < a q) (λ q → x q < y q)
  (λ q → b q N.<? a q) (λ q → x q N.<? y q)
  left leftBack leftInverse leftRightInverse leftPositive leftBackPositive
  leftGrade leftBackGrade leftTarget leftSource

module R = Chart (λ q → a q < b q) (λ q → y q < x q)
  (λ q → a q N.<? b q) (λ q → y q N.<? x q)
  right rightBack rightInverse rightRightInverse rightPositive rightBackPositive
  rightGrade rightBackGrade rightTarget rightSource

leftPermutation : ∀ n → map left (L.source n) Perm.↭ L.target n
leftPermutation = L.permutation

rightPermutation : ∀ n → map right (R.source n) Perm.↭ R.target n
rightPermutation = R.permutation
