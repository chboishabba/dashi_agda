module DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionEqualityPermutationExact where

-- SOURCE-WRITTEN, UNCOMPILED. Enumerate the two equality strata from
-- the existing factor-pair scan, not another divisor enumerator.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _<_; _∸_)
import Data.Nat.Properties as N
open import Data.Nat.Divisibility using (_∣_; _∣?_)
open import Data.Empty using (⊥-elim)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Base using (List; []; _∷_; map; filter; cartesianProductWith)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as M
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AP
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as U
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Integer.Base using (ℤ)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as F
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as One
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearPermutationExact as G
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionFactorChartExact as C
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSignedBoundaryExact as B
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
open import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearExact
  using (Quad; quad; a; b; x; y; grade)

factorKey : ∀ {n} → F.PositiveFactorPair n → G.Pair
factorKey p = F.divisor p , suc (F.predecessor p)

-- Projection freshness, not equality of proof-bearing factor records.
factorKeysFromUnique : (n : Nat) (pn : zero < n) (ds : List Nat)
  (bs : All.All (λ d → (zero < d) × (d ≤ n)) ds) →
  Unique ds → Unique (map factorKey (F.positiveFactorPairsFrom n pn ds bs))
factorKeysFromUnique n pn [] All.[] AP.[] = AP.[]
factorKeysFromUnique n pn (d ∷ ds) (All._∷_ bounds rest)
  (AP._∷_ fresh unique) with d ∣? n
... | no _ = factorKeysFromUnique n pn ds rest unique
... | yes dv with _∣_.quotient dv
...   | zero = ⊥-elim (F.positiveNotZero pn (trans (_∣_.equality dv) refl))
...   | suc k = AP._∷_
    (All.tabulate (λ m eq →
      let p , mp , e = M.∈-map⁻ m
      in All.lookup fresh (F.pairDivisorMemberCandidates n pn ds rest mp)
        (trans (cong proj₁ eq) (cong proj₁ e))))
    (factorKeysFromUnique n pn ds rest unique)

Key : Set
Key = G.Pair × Nat

keys : (n : Nat) → zero < n → List Key
keys n pn = cartesianProductWith _,_
  (map factorKey (F.positiveFactorPairs n pn)) (Hecke.oneTo n)

keysUnique : (n : Nat) (pn : zero < n) → Unique (keys n pn)
keysUnique n pn = U.cartesianProductWith⁺ _,_ inject
  (factorKeysFromUnique n pn (Hecke.oneTo n) (One.oneToAllBounds n) (One.oneToUnique n))
  (One.oneToUnique n)
  where
  inject : ∀ {u v : G.Pair} {s t : Nat} → (u , s) ≡ (v , t) →
    (u ≡ v) × (s ≡ t)
  inject refl = refl , refl

xyKeys abKeys : (n : Nat) → zero < n → List Key
xyKeys n pn = filter (λ ((d , k) , t) → t N.<? d) (keys n pn)
abKeys n pn = filter (λ ((d , k) , t) → t N.<? k) (keys n pn)

xyQuad abQuad : Key → Quad
xyQuad ((d , k) , t) = quad t (d ∸ t) k k
abQuad ((d , k) , t) = quad d d t (k ∸ t)

readXY readAB : Quad → Key
readXY q = (a q + b q , x q) , a q
readAB q = (a q , x q + y q) , x q

xyRead : ∀ {n pn z} → z ∈ xyKeys n pn → readXY (xyQuad z) ≡ z
xyRead {z = ((d , k) , t)} m =
  cong (λ v → (v , k) , t)
    (C.splitSum d t (proj₂ (M.∈-filter⁻ (λ ((d , k) , t) → t N.<? d) m)))

abRead : ∀ {n pn z} → z ∈ abKeys n pn → readAB (abQuad z) ≡ z
abRead {z = ((d , k) , t)} m =
  cong (λ v → (d , v) , t)
    (C.splitSum k t (proj₂ (M.∈-filter⁻ (λ ((d , k) , t) → t N.<? k) m)))

xyUnique : (n : Nat) (pn : zero < n) → Unique (map xyQuad (xyKeys n pn))
xyUnique n pn = G.mapUniqueOn xyQuad (xyKeys n pn)
  (U.filter⁺ (λ ((d , k) , t) → t N.<? d) (keysUnique n pn))
  (λ u v e → trans (sym (xyRead u)) (trans (cong readXY e) (xyRead v)))

abUnique : (n : Nat) (pn : zero < n) → Unique (map abQuad (abKeys n pn))
abUnique n pn = G.mapUniqueOn abQuad (abKeys n pn)
  (U.filter⁺ (λ ((d , k) , t) → t N.<? k) (keysUnique n pn))
  (λ u v e → trans (sym (abRead u)) (trans (cong readAB e) (abRead v)))

xyKeyForward : ∀ {n pn z} → z ∈ xyKeys n pn → xyQuad z ∈ B.eq x y (G.omega n)
xyKeyForward {n} {pn} m with M.∈-filter⁻ (λ ((d , k) , t) → t N.<? d) m
... | raw , hs with M.∈-cartesianProductWith⁻ _,_
  (map factorKey (F.positiveFactorPairs n pn)) (Hecke.oneTo n) raw
...   | u , t , mu , mt , refl with M.∈-map⁻ mu
...     | p , mp , refl = M.∈-filter⁺ (λ q → x q N.≟ y q)
  (C.fromXYOmega p t (One.oneToPositive mt) hs) refl

abKeyForward : ∀ {n pn z} → z ∈ abKeys n pn → abQuad z ∈ B.eq a b (G.omega n)
abKeyForward {n} {pn} m with M.∈-filter⁻ (λ ((d , k) , t) → t N.<? k) m
... | raw , hs with M.∈-cartesianProductWith⁻ _,_
  (map factorKey (F.positiveFactorPairs n pn)) (Hecke.oneTo n) raw
...   | u , t , mu , mt , refl with M.∈-map⁻ mu
...     | p , mp , refl = M.∈-filter⁺ (λ q → a q N.≟ b q)
  (C.fromABOmega p t (One.oneToPositive mt) hs) refl

xyForward : ∀ {n pn q} → q ∈ map xyQuad (xyKeys n pn) → q ∈ B.eq x y (G.omega n)
xyForward {n} {pn} m with M.∈-map⁻ m
... | z , mz , e = subst (λ q → q ∈ B.eq x y (G.omega n)) (sym e) (xyKeyForward mz)

abForward : ∀ {n pn q} → q ∈ map abQuad (abKeys n pn) → q ∈ B.eq a b (G.omega n)
abForward {n} {pn} m with M.∈-map⁻ m
... | z , mz , e = subst (λ q → q ∈ B.eq a b (G.omega n)) (sym e) (abKeyForward mz)

xyBackward : ∀ {n pn q} → q ∈ B.eq x y (G.omega n) → q ∈ map xyQuad (xyKeys n pn)
xyBackward {n} {pn} {q} m with M.∈-filter⁻ (λ q → x q N.≟ y q) m
... | o , e with G.omegaRead o
...   | h , refl with C.xyPair q h e pn
...     | p , mp , d , k =
  let hs = subst (a q <_) (sym d) (C.xySplitStrict q h)
      ht = One.oneToComplete (proj₁ h) (N.≤-trans (N.<⇒≤ hs) (F.divisorBound p))
      z = M.∈-filter⁺ (λ ((d , k) , t) → t N.<? d)
        (M.∈-cartesianProductWith⁺ _,_ (M.∈-map⁺ mp) ht) hs
  in subst (λ v → v ∈ map xyQuad (xyKeys (grade q) pn))
       (C.recoverXY q e p d k) (M.∈-map⁺ z)

abBackward : ∀ {n pn q} → q ∈ B.eq a b (G.omega n) → q ∈ map abQuad (abKeys n pn)
abBackward {n} {pn} {q} m with M.∈-filter⁻ (λ q → a q N.≟ b q) m
... | o , e with G.omegaRead o
...   | h , refl with C.abPair q h e pn
...     | p , mp , d , k =
  let hs = subst (x q <_) (sym k) (C.abSplitStrict q h)
      ht = One.oneToComplete (proj₁ (proj₂ (proj₂ h)))
        (N.≤-trans (N.<⇒≤ hs) (F.copiesBoundByProduct p))
      z = M.∈-filter⁺ (λ ((d , k) , t) → t N.<? k)
        (M.∈-cartesianProductWith⁺ _,_ (M.∈-map⁺ mp) ht) hs
  in subst (λ v → v ∈ map abQuad (abKeys (grade q) pn))
       (C.recoverAB q e p d k) (M.∈-map⁺ z)

xyPermutation : (n : Nat) (pn : zero < n) →
  map xyQuad (xyKeys n pn) Perm.↭ B.eq x y (G.omega n)
xyPermutation n pn = Reindex.uniqueMembershipEquivalenceToPermutation
  (xyUnique n pn) (U.filter⁺ (λ q → x q N.≟ y q) (G.omegaUnique n))
  xyForward xyBackward

abPermutation : (n : Nat) (pn : zero < n) →
  map abQuad (abKeys n pn) Perm.↭ B.eq a b (G.omega n)
abPermutation n pn = Reindex.uniqueMembershipEquivalenceToPermutation
  (abUnique n pn) (U.filter⁺ (λ q → a q N.≟ b q) (G.omegaUnique n))
  abForward abBackward

xyFold : (f : Quad → ℤ) (n : Nat) (pn : zero < n) →
  B.foldZ f (B.eq x y (G.omega n)) ≡ B.foldZ (λ z → f (xyQuad z)) (xyKeys n pn)
xyFold f n pn = trans (sym (B.foldPerm f (xyPermutation n pn)))
  (B.foldMap f xyQuad (xyKeys n pn))

abFold : (f : Quad → ℤ) (n : Nat) (pn : zero < n) →
  B.foldZ f (B.eq a b (G.omega n)) ≡ B.foldZ (λ z → f (abQuad z)) (abKeys n pn)
abFold f n pn = trans (sym (B.foldPerm f (abPermutation n pn)))
  (B.foldMap f abQuad (abKeys n pn))
