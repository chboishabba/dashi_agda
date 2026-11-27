module DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact where

-- Reflect the actual finite Cauchy row and its normalized zero mode.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_; _∸_)
import Data.Nat.Properties as N
open import Data.List.Base using (List; []; _∷_; _++_; map; filter)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as M
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (ℤ; +_; _+_; _*_; -_)
import Data.Integer.Properties as Z
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as H
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as One
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSignedBoundaryExact as B
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionBoundaryRegroupExact as R
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionClosedBoundaryExact as L
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSigmaFoldExact as V
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionFactorChartExact as C

SeriesZ : Set
SeriesZ = Nat → ℤ

rowZ : SeriesZ → SeriesZ → Nat → ℤ
rowZ f g n = f zero * g n + B.foldZ (λ i → f i * g (n ∸ i)) (H.oneTo n)

mapAppend : ∀ {A D : Set} (f : A → D) (xs ys : List A) →
  map f (xs ++ ys) ≡ map f xs ++ map f ys
mapAppend f [] ys = refl
mapAppend f (x ∷ xs) ys = cong (f x ∷_) (mapAppend f xs ys)

oneToShift : (n : Nat) → H.oneTo (suc n) ≡ map suc (zero ∷ H.oneTo n)
oneToShift zero = refl
oneToShift (suc n) =
  trans (cong (_++ (suc (suc n) ∷ [])) (oneToShift n))
    (sym (mapAppend suc (zero ∷ H.oneTo n) (suc n ∷ [])))

rowZero : (f g : SeriesZ) → rowZ f g zero ≡ f zero * g zero
rowZero f g = Z.+-identityʳ (f zero * g zero)

rowHead : (f g : SeriesZ) (n : Nat) →
  rowZ f g (suc n) ≡ f zero * g (suc n) + rowZ (λ i → f (suc i)) g n
rowHead f g n =
  cong (f zero * g (suc n) +_)
    (trans (cong (B.foldZ (λ i → f i * g (suc n ∸ i))) (oneToShift n))
      (B.foldMap (λ i → f i * g (suc n ∸ i)) suc (zero ∷ H.oneTo n)))

coefficient : Nat → ℤ → SeriesZ
coefficient k c zero = + 1
coefficient k c (suc n) = c * V.sigma k (suc n)

positiveCoefficient : (k : Nat) (c : ℤ) (i : Nat) → zero < i →
  coefficient k c i ≡ c * V.sigma k i
positiveCoefficient k c zero ()
positiveCoefficient k c (suc n) h = refl

interiorTerm : (k l : Nat) (c d : ℤ) (n i : Nat) → zero < i → i < n →
  coefficient k c i * coefficient l d (n ∸ i) ≡
  (c * d) * (V.sigma k i * V.sigma l (n ∸ i))
interiorTerm k l c d n i pi hi =
  trans (cong (_* coefficient l d (n ∸ i)) (positiveCoefficient k c i pi))
    (trans (cong ((c * V.sigma k i) *_) (positiveCoefficient l d (n ∸ i) (C.splitPositive n i hi)))
      (solve 4 (λ c d a b → (c :* a) :* (d :* b) := (c :* d) :* (a :* b))
        refl c d (V.sigma k i) (V.sigma l (n ∸ i))))

-- Explicit endpoints plus the positive interior convolution, no
-- assumption that the head of E2/E4/E6 is a divisor sum at zero.
open import Data.Nat.Base using (s≤s; z≤n)

rowPositive : (k l : Nat) (c d : ℤ) (n : Nat) →
  rowZ (coefficient k c) (coefficient l d) (suc n) ≡
  c * V.sigma k (suc n) + d * V.sigma l (suc n) + (c * d) * V.conv k l (suc n)
rowPositive k l c d n =
  let m = suc n
      f = coefficient k c
      g = coefficient l d
      h = λ i → f i * g (m ∸ i)
      gs = V.grades m
      prefix = R.strictPrefix m n N.≤-refl
      row = B.foldZ h (H.oneTo n)
      p = B.foldZ h gs
      a = c * V.sigma k m
      b = d * V.sigma l m
      end : h m ≡ a
      end = trans (cong (f m *_) (cong g (N.n∸n≡0 m))) (Z.*-identityʳ a)
      interior : p ≡ (c * d) * V.conv k l m
      interior = trans (B.foldCongOn h (λ i → (c * d) * (V.sigma k i * V.sigma l (m ∸ i))) gs
        (λ {i} mem → let q , lt = M.∈-filter⁻ (λ i → i N.<? m) mem in
          interiorTerm k l c d m i (One.oneToPositive q) lt))
        (sym (L.scaleFold (c * d) (λ i → V.sigma k i * V.sigma l (m ∸ i)) gs))
  in trans (cong (_+ B.foldZ h (H.oneTo m)) (Z.*-identityˡ b))
    (trans (cong (b +_) (R.foldAscending h n))
      (trans (cong (λ z → b + (row + z)) end)
        (trans (cong (λ z → b + (z + a)) (cong (B.foldZ h) (sym prefix)))
          (trans (cong (λ z → b + (z + a)) interior)
            (solve 3 (λ a b c → b :+ (c :+ a) := (a :+ b) :+ c)
              refl a b ((c * d) * V.conv k l m))))))

-- Reflect denominator-one integers into the existing Bishop real.
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Real as RR
import RealProperties as RP
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row

embed : ℤ → RR.ℝ
embed z = RR._⋆ (z / 1)

embedCong : ∀ {a b : ℤ} → a ≡ b → RR._≃_ (embed a) (embed b)
embedCong refl = RP.≃-refl

embedAdd : (a b : ℤ) → RR._≃_ (embed (a + b)) (RR._+_ (embed a) (embed b))
embedAdd a b = RP.≃-trans
  (RP.⋆-cong (Q.*≡* (solve 2 (λ a b →
    (a :+ b) :* con (+ 1) := (a :* con (+ 1) :+ b :* con (+ 1)) :* con (+ 1))
    refl a b)))
  (RP.⋆-distrib-+ (a / 1) (b / 1))

embedMul : (a b : ℤ) → RR._≃_ (embed (a * b)) (RR._*_ (embed a) (embed b))
embedMul a b = RP.≃-trans
  (RP.⋆-cong (Q.*≡* (solve 2 (λ a b →
    (a :* b) :* con (+ 1) := (a :* b) :* con (+ 1))
    refl a b)))
  (RP.⋆-distrib-* (a / 1) (b / 1))

rowEmbed : (f g : SeriesZ) (n : Nat) →
  RR._≃_ (embed (rowZ f g n)) (Row.cauchyCoefficient (λ i → embed (f i)) (λ i → embed (g i)) n)
rowEmbed f g zero = RP.≃-trans (embedCong (rowZero f g))
  (RP.≃-trans (embedMul (f zero) (g zero))
    (RP.≃-symm (Row.cauchyCoefficientZero (λ i → embed (f i)) (λ i → embed (g i)))))
rowEmbed f g (suc n) = RP.≃-trans (embedCong (rowHead f g n))
  (RP.≃-trans (embedAdd (f zero * g (suc n)) (rowZ (λ i → f (suc i)) g n))
    (RP.≃-trans (RP.+-cong (embedMul (f zero) (g (suc n))) (rowEmbed (λ i → f (suc i)) g n))
      (RP.≃-symm (Row.cauchyCoefficientSuccessor (λ i → embed (f i)) (λ i → embed (g i)) n))))
