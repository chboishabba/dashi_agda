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
  B.foldZ (λ (d , k) → B.foldZ (λ t → f (E.abQuad ((d , k) , t)))
    (filter (λ t → t N.<? k) (H.oneTo n)))
    (map E.factorKey (P.positiveFactorPairs n pn))
abRegroup f n pn = trans (E.abFold f n pn)
  (regroup (λ ((d , k) , t) → t N.<? k) (λ z → f (E.abQuad z))
    (map E.factorKey (P.positiveFactorPairs n pn)) (H.oneTo n))



-- Strict prefix transport by induction on the original upper bound.
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.Any as Any
import Data.List.Properties as LP
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as One
open import Data.Nat.Base using (z≤n)

keepAll : (d : Nat) (xs : List Nat) →
  (∀ {t} → t ∈ xs → t < d) → filter (λ t → t N.<? d) xs ≡ xs
keepAll d [] h = refl
keepAll d (t ∷ ts) h with t N.<? d
... | yes _ = cong (t ∷_) (keepAll d ts (λ m → h (Any.there m)))
... | no bad = ⊥-elim (bad (h (Any.here refl)))

dropLast : (d t : Nat) → d ≤ t →
  filter (λ u → u N.<? d) (t ∷ []) ≡ []
dropLast d t h with t N.<? d
... | yes lt = ⊥-elim (N.<-irrefl refl (N.<-≤-trans lt h))
... | no _ = refl

strictPrefix : (d n : Nat) → d ≤ suc n →
  filter (λ t → t N.<? d) (H.oneTo (suc n)) ≡ H.oneTo (d ∸ 1)
strictPrefix zero zero h = refl
strictPrefix (suc zero) zero h = refl
strictPrefix (suc (suc d)) zero (s≤s ())
strictPrefix d (suc n) h with d N.≤? suc n
... | yes le =
  trans (filterAppend (λ t → t N.<? d) (H.oneTo (suc n)) (suc (suc n) ∷ []))
    (trans (cong (λ xs → xs ++ filter (λ t → t N.<? d) (suc (suc n) ∷ []))
      (strictPrefix d n le))
      (trans (cong (H.oneTo (d ∸ 1) ++_) (dropLast d (suc (suc n)) h))
        (LP.++-identityʳ (H.oneTo (d ∸ 1)))))
... | no ne with N.≤-antisym h (N.≰⇒> ne)
...   | refl =
  trans (filterAppend (λ t → t N.<? suc (suc n)) (H.oneTo (suc n)) (suc (suc n) ∷ []))
    (trans (cong (λ xs → xs ++ filter (λ t → t N.<? suc (suc n)) (suc (suc n) ∷ []))
      (keepAll (suc (suc n)) (H.oneTo (suc n)) (λ m → s≤s (One.oneToUpperBound m))))
      (trans (cong (H.oneTo (suc n) ++_) (dropLast (suc (suc n)) (suc (suc n)) N.≤-refl))
        (LP.++-identityʳ (H.oneTo (suc n)))))

foldAscending : (f : Nat → ℤ) (n : Nat) →
  B.foldZ f (H.oneTo (suc n)) ≡ B.foldZ f (H.oneTo n) + f (suc n)
foldAscending f n = trans (foldAppend f (H.oneTo n) (suc n ∷ []))
  (cong (B.foldZ f (H.oneTo n) +_) (Z.+-identityʳ (f (suc n))))

prefixObservation : (f : B.Weight) (m d : ℤ) (n : Nat) →
  B.foldZ (λ t → m * f d (d + ((- (+ 1)) * (+ t)))) (H.oneTo n)
  ≡ S.scaledBoundaryPrefix f m d n
prefixObservation f m d zero = refl
prefixObservation f m d (suc n) =
  trans (foldAscending (λ t → m * f d (d + ((- (+ 1)) * (+ t)))) n)
    (cong (_+ (m * f d (d + ((- (+ 1)) * (+ (suc n)))))) (prefixObservation f m d n))

closedPrefix1 : (n : Nat) →
  B.foldZ (λ t → (+ 6) * S.weight1 (+ (suc n)) ((+ (suc n)) + ((- (+ 1)) * (+ t)))) (H.oneTo n)
  ≡ S.boundary1 (+ (suc n))
closedPrefix1 n = trans (prefixObservation S.weight1 (+ 6) (+ (suc n)) n) (S.boundaryClosed1 n)

closedPrefix2 : (n : Nat) →
  B.foldZ (λ t → (+ 30) * S.weight2 (+ (suc n)) ((+ (suc n)) + ((- (+ 1)) * (+ t)))) (H.oneTo n)
  ≡ S.boundary2 (+ (suc n))
closedPrefix2 n = trans (prefixObservation S.weight2 (+ 30) (+ (suc n)) n) (S.boundaryClosed2 n)

closedPrefix3 : (n : Nat) →
  B.foldZ (λ t → (+ 420) * S.weight3 (+ (suc n)) ((+ (suc n)) + ((- (+ 1)) * (+ t)))) (H.oneTo n)
  ≡ S.boundary3 (+ (suc n))
closedPrefix3 n = trans (prefixObservation S.weight3 (+ 420) (+ (suc n)) n) (S.boundaryClosed3 n)

closedPrefix4 : (n : Nat) →
  B.foldZ (λ t → (+ 30) * S.weight4 (+ (suc n)) ((+ (suc n)) + ((- (+ 1)) * (+ t)))) (H.oneTo n)
  ≡ S.boundary4 (+ (suc n))
closedPrefix4 n = trans (prefixObservation S.weight4 (+ 30) (+ (suc n)) n) (S.boundaryClosed4 n)
