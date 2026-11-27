module DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionBoundaryRegroupExact where

-- Original factor scan, original strict split filter; source-written.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _<_; _∸_; s≤s)
import Data.Nat.Properties as N
open import Data.List.Base using (List; []; _∷_; _++_; map; filter; cartesianProductWith)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Integer.Base using (ℤ; +_; _+_; _*_; -_)
import Data.Integer.Properties as Z
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as H
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSignedBoundaryExact as B
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionEqualityPermutationExact as E
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionFactorChartExact as C
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearExact as S
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as P
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearPermutationExact as G

foldAppend : ∀ {A : Set} (f : A → ℤ) (xs ys : List A) →
  B.foldZ f (xs ++ ys) ≡ B.foldZ f xs + B.foldZ f ys
foldAppend f [] ys = sym (Z.+-identityˡ (B.foldZ f ys))
foldAppend f (x ∷ xs) ys =
  trans (cong (f x +_) (foldAppend f xs ys))
    (sym (Z.+-assoc (f x) (B.foldZ f xs) (B.foldZ f ys)))

filterAppend : ∀ {A : Set} {Q : A → Set} (q : ∀ x → Dec (Q x))
  (xs ys : List A) → filter q (xs ++ ys) ≡ filter q xs ++ filter q ys
filterAppend q [] ys = refl
filterAppend q (x ∷ xs) ys with q x
... | yes _ = cong (x ∷_) (filterAppend q xs ys)
... | no _ = filterAppend q xs ys

foldFilteredMap : ∀ {A D : Set} {Q : D → Set}
  (q : ∀ x → Dec (Q x)) (g : A → D) (f : D → ℤ) (xs : List A) →
  B.foldZ f (filter q (map g xs)) ≡
  B.foldZ (λ x → f (g x)) (filter (λ x → q (g x)) xs)
foldFilteredMap q g f [] = refl
foldFilteredMap q g f (x ∷ xs) with q (g x)
... | yes _ = cong (f (g x) +_) (foldFilteredMap q g f xs)
... | no _ = foldFilteredMap q g f xs

regroup : ∀ {A D : Set} {Q : A × D → Set}
  (q : ∀ x → Dec (Q x)) (f : A × D → ℤ) (xs : List A) (ys : List D) →
  B.foldZ f (filter q (cartesianProductWith _,_ xs ys)) ≡
  B.foldZ (λ x → B.foldZ (λ y → f (x , y))
    (filter (λ y → q (x , y)) ys)) xs
regroup q f [] ys = refl
regroup q f (x ∷ xs) ys =
  trans (cong (B.foldZ f) (filterAppend q (map (x ,_) ys)
      (cartesianProductWith _,_ xs ys)))
    (trans (foldAppend f (filter q (map (x ,_) ys))
      (filter q (cartesianProductWith _,_ xs ys)))
      (trans (cong (_+ B.foldZ f (filter q (cartesianProductWith _,_ xs ys)))
        (foldFilteredMap q (x ,_) f ys))
        (cong (B.foldZ (λ y → f (x , y)) (filter (λ y → q (x , y)) ys) +_)
          (regroup q f xs ys))))

xyRegroup : (f : S.Quad → ℤ) (n : Nat) (pn : zero < n) →
  B.foldZ f (B.eq S.x S.y (G.omega n)) ≡
  B.foldZ (λ (d , k) → B.foldZ (λ t → f (E.xyQuad ((d , k) , t)))
    (filter (λ t → t N.<? d) (H.oneTo n)))
    (map E.factorKey (P.positiveFactorPairs n pn))
xyRegroup f n pn = trans (E.xyFold f n pn)
  (regroup (λ ((d , k) , t) → t N.<? d) (λ z → f (E.xyQuad z))
    (map E.factorKey (P.positiveFactorPairs n pn)) (H.oneTo n))

abRegroup : (f : S.Quad → ℤ) (n : Nat) (pn : zero < n) →
  B.foldZ f (B.eq S.a S.b (G.omega n)) ≡
  B.foldZ (λ ((d , k)) → B.foldZ (λ t → f (E.abQuad ((d , k) , t)))
    (filter (λ t → t N.<? k) (H.oneTo n)))
    (map E.factorKey (P.positiveFactorPairs n pn))
abRegroup f n pn = trans (E.abFold f n pn)
  (regroup (λ ((d , k) , t) → t N.<? k) (λ z → f (E.abQuad z))
    (map E.factorKey (P.positiveFactorPairs n pn)) (H.oneTo n))

