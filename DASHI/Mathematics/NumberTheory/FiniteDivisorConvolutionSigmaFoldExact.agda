module DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSigmaFoldExact where

-- All-index source attempt: sum the actual grade fibres, then use the
-- original divisor-power scanner. No replacement convolution semantics.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_; _∸_)
import Data.Nat.Properties as N
open import Data.List.Base using (List; []; _∷_; _++_; map; filter; cartesianProductWith)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as M
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AP
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as U
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (ℤ; +_; _+_; _*_; -_)
import Data.Integer.Properties as Z
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as H
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as One
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSignedBoundaryExact as B
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionBoundaryRegroupExact as R
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionClosedBoundaryExact as L
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionInteriorFoldExact as I
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionGradeFibreExact as F
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionEqualityPermutationExact as E
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionFactorChartExact as C
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearExact as S
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as P
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionShearPermutationExact as G
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as W
import DASHI.Mathematics.NumberTheory.FiniteFactorPairPowerReadoutExact as Read
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Pow

foldZero : ∀ {A : Set} (xs : List A) → B.foldZ (λ _ → + 0) xs ≡ + 0
foldZero [] = refl
foldZero (x ∷ xs) = trans (cong ((+ 0) +_) (foldZero xs)) refl

swapFold : ∀ {A D : Set} (f : A → D → ℤ) (xs : List A) (ys : List D) →
  B.foldZ (λ x → B.foldZ (f x) ys) xs ≡
  B.foldZ (λ y → B.foldZ (λ x → f x y) xs) ys
swapFold f [] ys = sym (foldZero ys)
swapFold f (x ∷ xs) ys =
  trans (cong (B.foldZ (f x) ys +_) (swapFold f xs ys))
    (sym (I.foldAdd (f x) (λ y → B.foldZ (λ z → f z y) xs) ys))

mask : Nat → Nat → ℤ → ℤ
mask i j z with i N.≟ j
... | yes _ = z
... | no _ = + 0

maskDifferent : (i j : Nat) (z : ℤ) → (i ≡ j → ⊥) → mask i j z ≡ + 0
maskDifferent i j z h with i N.≟ j
... | yes e = ⊥-elim (h e)
... | no _ = refl

maskSame : (i : Nat) (z : ℤ) → mask i i z ≡ z
maskSame i z with i N.≟ i
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

maskNone : (i : Nat) (z : ℤ) (xs : List Nat) →
  (i ∈ xs → ⊥) → B.foldZ (λ j → mask i j z) xs ≡ + 0
maskNone i z [] h = refl
maskNone i z (j ∷ xs) h =
  trans (cong (_+ B.foldZ (λ j → mask i j z) xs)
    (maskDifferent i j z (λ e → h (Any.here e))))
    (trans (Z.+-identityˡ _) (maskNone i z xs (λ m → h (Any.there m))))

maskOnce : (i : Nat) (z : ℤ) (xs : List Nat) → Unique xs → i ∈ xs →
  B.foldZ (λ j → mask i j z) xs ≡ z
maskOnce i z (j ∷ xs) (AP._∷_ fresh rest) (Any.here refl) =
  trans (cong (_+ B.foldZ (λ j → mask i j z) xs) (maskSame i z))
    (trans (cong (z +_) (maskNone i z xs (λ m → All.lookup fresh m refl))) (Z.+-identityʳ z))
maskOnce i z (j ∷ xs) (AP._∷_ fresh rest) (Any.there m) =
  trans (cong (_+ B.foldZ (λ j → mask i j z) xs)
    (maskDifferent i j z (λ e → All.lookup fresh m (sym e))))
    (trans (Z.+-identityˡ _) (maskOnce i z xs rest m))

maskedFilter : ∀ {A : Set} (g : A → Nat) (f : A → ℤ) (j : Nat) (xs : List A) →
  B.foldZ (λ x → mask (g x) j (f x)) xs ≡
  B.foldZ f (filter (λ x → g x N.≟ j) xs)
maskedFilter g f j [] = refl
maskedFilter g f j (x ∷ xs) with g x N.≟ j
... | yes _ = cong (f x +_) (maskedFilter g f j xs)
... | no _ = trans (Z.+-identityˡ _) (maskedFilter g f j xs)

grades : Nat → List Nat
grades n = filter (λ i → i N.<? n) (H.oneTo n)

gradeMember : ∀ {n q} → q ∈ G.omega n → C.i q ∈ grades n
gradeMember {n} {q} m =
  let p , e = G.omegaRead m
      lt = subst (C.i q <_) e (C.iStrict q p)
  in M.∈-filter⁺ (λ i → i N.<? n)
       (One.oneToComplete (C.iPositive q p) (N.<⇒≤ lt)) lt

groupGrade : (f : S.Quad → ℤ) (n : Nat) →
  B.foldZ f (G.omega n) ≡
  B.foldZ (λ j → B.foldZ f (filter (λ q → C.i q N.≟ j) (G.omega n))) (grades n)
groupGrade f n =
  let o = G.omega n
      gs = grades n
      g = λ q j → mask (C.i q) j (f q)
  in trans (B.foldCongOn f (λ q → B.foldZ (g q) gs) o
        (λ {q} m → sym (maskOnce (C.i q) (f q) gs
          (U.filter⁺ (λ i → i N.<? n) (One.oneToUnique n)) (gradeMember m))))
       (trans (swapFold g o gs)
         (B.foldCongOn (λ j → B.foldZ (λ q → g q j) o)
           (λ j → B.foldZ f (filter (λ q → C.i q N.≟ j) o)) gs
           (λ {j} _ → maskedFilter C.i f j o)))

embedFold : ∀ {A : Set} (f : A → Nat) (xs : List A) →
  (+ W.foldNat f xs) ≡ B.foldZ (λ x → + f x) xs
embedFold f [] = refl
embedFold f (x ∷ xs) =
  trans (Z.pos-+ (f x) (W.foldNat f xs)) (cong ((+ f x) +_) (embedFold f xs))

sigma : Nat → Nat → ℤ
sigma k n = + Pow.sigmaPower k n

factorPower : (k n : Nat) (pn : zero < n) →
  B.foldZ (λ u → + Pow.powNat (proj₁ u) k) (F.factorKeys n pn) ≡ sigma k n
factorPower k n pn =
  let ps = P.positiveFactorPairs n pn
      f = λ p → Pow.powNat (P.divisor p) k
  in trans (B.foldMap (λ u → + Pow.powNat (proj₁ u) k) E.factorKey ps)
       (trans (sym (embedFold f ps)) (cong +_ (Read.positivePowerReadout k n pn)))

cartesianFold : ∀ {A D T : Set} (g : A → D → T) (f : T → ℤ)
  (xs : List A) (ys : List D) →
  B.foldZ f (cartesianProductWith g xs ys) ≡
  B.foldZ (λ x → B.foldZ (λ y → f (g x y)) ys) xs
cartesianFold g f [] ys = refl
cartesianFold g f (x ∷ xs) ys =
  trans (R.foldAppend f (map (g x) ys) (cartesianProductWith g xs ys))
    (trans (cong (_+ B.foldZ f (cartesianProductWith g xs ys)) (B.foldMap f (g x) ys))
      (cong (B.foldZ (λ y → f (g x y)) ys +_) (cartesianFold g f xs ys)))

weight : Nat → Nat → S.Quad → ℤ
weight k l q = (+ Pow.powNat (S.a q) k) * (+ Pow.powNat (S.b q) l)

conv : Nat → Nat → Nat → ℤ
conv k l n = B.foldZ (λ i → sigma k i * sigma l (n ∸ i)) (grades n)

fibrePower : (k l n i : Nat) (pi : zero < i) (hi : i < n) →
  B.foldZ (weight k l) (filter (λ q → C.i q N.≟ i) (G.omega n))
    ≡ sigma k i * sigma l (n ∸ i)
fibrePower k l n i pi hi =
  let module A = F.AtGrade n i pi hi
      f = λ u → + Pow.powNat (proj₁ u) k
      g = λ v → + Pow.powNat (proj₁ v) l
      ys = A.rightKeys
      xs = A.leftKeys
      z = sigma l A.j
      row = λ u → B.foldZ (λ v → f u * g v) ys
  in trans (A.foldFibre (weight k l))
    (trans (cartesianFold F.keyQuad (weight k l) xs ys)
      (trans (B.foldCongOn row (λ u → f u * z) xs
        (λ {u} _ → trans (sym (L.scaleFold (f u) g ys))
          (cong (f u *_) (factorPower l A.j A.pj))))
        (trans (B.foldCongOn (λ u → f u * z) (λ u → z * f u) xs
          (λ {u} _ → Z.*-comm (f u) z))
          (trans (sym (L.scaleFold z f xs))
            (trans (cong (z *_) (factorPower k i pi)) (Z.*-comm z (sigma k i)))))))

omegaPower : (k l n : Nat) →
  B.foldZ (weight k l) (G.omega n) ≡ conv k l n
omegaPower k l n = trans (groupGrade (weight k l) n)
  (B.foldCongOn (λ i → B.foldZ (weight k l) (filter (λ q → C.i q N.≟ i) (G.omega n)))
    (λ i → sigma k i * sigma l (n ∸ i)) (grades n)
    (λ {i} m → let p , h = M.∈-filter⁻ (λ j → j N.<? n) m in
      fibrePower k l n i (One.oneToPositive p) h))
