module DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionGradeFibreExact where

-- Source attempt: factor the actual positive grade by i=ax, preserving
-- both inverse coordinates. No proof-bearing factor record equality.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _<_; _∸_)
import Data.Nat.Properties as N
open import Data.List.Base using (List; []; _∷_; map; filter; cartesianProductWith)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as M
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Unique.Propositional.Properties as U
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as H
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as One
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSignedBoundaryExact as B
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionBoundaryRegroupExact as R
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionEqualityPermutationExact as E
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionFactorChartExact as C
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearExact as S
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as P
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearPermutationExact as G
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as W
open import Data.Integer.Base using (ℤ)

factorKeys : (n : Nat) → zero < n → List G.Pair
factorKeys n pn = map E.factorKey (P.positiveFactorPairs n pn)

keyQuad : G.Pair → G.Pair → S.Quad
keyQuad (a , x) (b , y) = S.quad a b x y

keyInjective : ∀ {u v w z : G.Pair} → keyQuad u v ≡ keyQuad w z →
  (u ≡ w) × (v ≡ z)
keyInjective {a , x} {b , y} {a′ , x′} {b′ , y′} refl = refl , refl

firstGrade : ∀ {r} (p : P.PositiveFactorPair r) →
  P.divisor p * suc (P.predecessor p) ≡ r
firstGrade p = trans (N.*-comm (P.divisor p) (suc (P.predecessor p))) (sym (P.productExact p))

module AtGrade (n i : Nat) (pi : zero < i) (hi : i < n) where
  j = n ∸ i
  pj : zero < j
  pj = C.splitPositive n i hi

  leftKeys = factorKeys i pi
  rightKeys = factorKeys j pj

  product = cartesianProductWith keyQuad leftKeys rightKeys
  fibre = filter (λ q → C.i q N.≟ i) (G.omega n)

  forward : ∀ {q} → q ∈ product → q ∈ fibre
  forward m with M.∈-cartesianProductWith⁻ keyQuad leftKeys rightKeys m
  ... | u , v , mu , mv , refl with M.∈-map⁻ mu | M.∈-map⁻ mv
  ...   | p , mp , refl | t , mt , refl =
    M.∈-filter⁺ (λ q → C.i q N.≟ i)
      (G.omegaWrite (C.fromFactorsPositive p t)
        (trans (C.fromFactorsGrade p t) (C.splitSum n i hi)))
      (firstGrade p)

  -- Construct the original factor keys at the prescribed grade.
  factorAt : (r a k : Nat) (pr : zero < r) → zero < a →
    r ≡ suc k * a → (a , suc k) ∈ factorKeys r pr
  factorAt r a k pr pa e with C.productPair r a k pr pa e
  ... | p , m , d , z =
    subst (λ v → v ∈ factorKeys r pr)
      (pairCong d (cong suc z)) (M.∈-map⁺ m)
    where
    pairCong : ∀ {a b c d : Nat} → a ≡ c → b ≡ d → (a , b) ≡ (c , d)
    pairCong refl refl = refl

  backward : ∀ {q} → q ∈ fibre → q ∈ product
  backward {q = S.quad a b zero y} m with G.omegaRead (proj₁ (M.∈-filter⁻ (λ q → C.i q N.≟ i) m))
  ... | (pa , pb , () , py) , e
  backward {q = S.quad a b (suc x) zero} m with G.omegaRead (proj₁ (M.∈-filter⁻ (λ q → C.i q N.≟ i) m))
  ... | (pa , pb , px , ()) , e
  backward {q = S.quad a b (suc x) (suc y)} m =
    let o , e = M.∈-filter⁻ (λ q → C.i q N.≟ i) m
        (pa , pb , px , py) , gr = G.omegaRead o
        ej : j ≡ b * suc y
        ej = trans (cong (λ v → n ∸ v) (sym e))
          (trans (cong (λ v → v ∸ (a * suc x)) (sym gr))
            (N.m+n∸m≡n (a * suc x) (b * suc y)))
        l = factorAt i a x pi pa (trans (sym e) (N.*-comm a (suc x)))
        r = factorAt j b y pj pb (trans ej (N.*-comm b (suc y)))
    in M.∈-cartesianProductWith⁺ keyQuad l r

  keyUnique : ∀ r pr → Unique (factorKeys r pr)
  keyUnique r pr = E.factorKeysFromUnique r pr (H.oneTo r)
    (One.oneToAllBounds r) (One.oneToUnique r)

  permutation : product Perm.↭ fibre
  permutation = W.uniqueMembershipEquivalenceToPermutation
    (U.cartesianProductWith⁺ keyQuad keyInjective (keyUnique i pi) (keyUnique j pj))
    (U.filter⁺ (λ q → C.i q N.≟ i) (G.omegaUnique n))
    forward backward

  foldFibre : (f : S.Quad → ℤ) →
    B.foldZ f fibre ≡ B.foldZ f product
  foldFibre f = sym (B.foldPerm f permutation)
