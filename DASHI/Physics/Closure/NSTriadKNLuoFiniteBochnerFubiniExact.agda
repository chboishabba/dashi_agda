module DASHI.Physics.Closure.NSTriadKNLuoFiniteBochnerFubiniExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Tuomas Hytönen; Jan van Neerven; Mark Veraar; Lutz Weis.
-- Title: "Analysis in Banach Spaces, Volume I: Martingales and Littlewood--
-- Paley Theory".
-- Springer, 2016.
-- DOI: 10.1007/978-3-319-48520-1.
--
-- PURPOSE
-- Supply a concrete finite vector-valued integration layer for the terminal
-- time/Fourier development.  Scalar finite sums are proved additive and are
-- shown to commute over rectangular time-space carriers.  The result is then
-- lifted componentwise to the repository's literal rational three-vector
-- carrier, yielding a finite Bochner/Fubini theorem.
--
-- This is actual checked finite integration mathematics.  Countable
-- Lebesgue/Bochner completion and dominated convergence remain continuum
-- producers and are not represented by a Boolean receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (cong; sym)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V

sumBy :
  ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumBy [] value = 0ℚ
sumBy (x ∷ xs) value = value x + sumBy xs value

sumByZero :
  ∀ {A : Set} (xs : List A) →
  sumBy xs (λ x → 0ℚ) ≡ 0ℚ
sumByZero [] = refl
sumByZero (x ∷ xs)
  rewrite sumByZero xs = refl

sumByAdd :
  ∀ {A : Set}
    (xs : List A)
    (left right : A → ℚ) →
  sumBy xs (λ x → left x + right x)
  ≡ sumBy xs left + sumBy xs right
sumByAdd [] left right = refl
sumByAdd (x ∷ xs) left right
  rewrite sumByAdd xs left right =
  solve (left x ∷ right x ∷ sumBy xs left ∷ sumBy xs right ∷ [])

sumByScale :
  ∀ {A : Set}
    (scale : ℚ)
    (xs : List A)
    (value : A → ℚ) →
  sumBy xs (λ x → scale * value x)
  ≡ scale * sumBy xs value
sumByScale scale [] value = solve (scale ∷ [])
sumByScale scale (x ∷ xs) value
  rewrite sumByScale scale xs value =
  solve (scale ∷ value x ∷ sumBy xs value ∷ [])

finiteScalarFubini :
  ∀ {A B : Set}
    (xs : List A)
    (ys : List B)
    (value : A → B → ℚ) →
  sumBy xs (λ x → sumBy ys (value x))
  ≡ sumBy ys (λ y → sumBy xs (λ x → value x y))
finiteScalarFubini [] ys value =
  Eq.sym (sumByZero ys)
finiteScalarFubini (x ∷ xs) ys value =
  begin
    sumBy (x ∷ xs) (λ x′ → sumBy ys (value x′))
  ≡⟨ refl ⟩
    sumBy ys (value x)
      + sumBy xs (λ x′ → sumBy ys (value x′))
  ≡⟨ cong (sumBy ys (value x) +_)
       (finiteScalarFubini xs ys value) ⟩
    sumBy ys (value x)
      + sumBy ys (λ y → sumBy xs (λ x′ → value x′ y))
  ≡⟨ Eq.sym
       (sumByAdd ys
         (value x)
         (λ y → sumBy xs (λ x′ → value x′ y))) ⟩
    sumBy ys
      (λ y → value x y + sumBy xs (λ x′ → value x′ y))
  ≡⟨ refl ⟩
    sumBy ys (λ y → sumBy (x ∷ xs) (λ x′ → value x′ y))
  ∎

bochnerSum :
  ∀ {A : Set} → List A → (A → V.Vector3) → V.Vector3
bochnerSum xs value =
  V.v3
    (sumBy xs (λ x → V.x (value x)))
    (sumBy xs (λ x → V.y (value x)))
    (sumBy xs (λ x → V.z (value x)))

bochnerSumAdd :
  ∀ {A : Set}
    (xs : List A)
    (left right : A → V.Vector3) →
  bochnerSum xs (λ x → V.add (left x) (right x))
  ≡ V.add (bochnerSum xs left) (bochnerSum xs right)
bochnerSumAdd xs left right =
  V.vectorExt
    (sumByAdd xs (λ x → V.x (left x)) (λ x → V.x (right x)))
    (sumByAdd xs (λ x → V.y (left x)) (λ x → V.y (right x)))
    (sumByAdd xs (λ x → V.z (left x)) (λ x → V.z (right x)))

bochnerSumScale :
  ∀ {A : Set}
    (scale : ℚ)
    (xs : List A)
    (value : A → V.Vector3) →
  bochnerSum xs (λ x → V.scale scale (value x))
  ≡ V.scale scale (bochnerSum xs value)
bochnerSumScale scale xs value =
  V.vectorExt
    (sumByScale scale xs (λ x → V.x (value x)))
    (sumByScale scale xs (λ x → V.y (value x)))
    (sumByScale scale xs (λ x → V.z (value x)))

finiteBochnerFubini :
  ∀ {A B : Set}
    (xs : List A)
    (ys : List B)
    (value : A → B → V.Vector3) →
  bochnerSum xs (λ x → bochnerSum ys (value x))
  ≡ bochnerSum ys (λ y → bochnerSum xs (λ x → value x y))
finiteBochnerFubini xs ys value =
  V.vectorExt
    (finiteScalarFubini xs ys (λ x y → V.x (value x y)))
    (finiteScalarFubini xs ys (λ x y → V.y (value x y)))
    (finiteScalarFubini xs ys (λ x y → V.z (value x y)))

weightedBochnerSum :
  ∀ {A : Set} →
  List A → (A → ℚ) → (A → V.Vector3) → V.Vector3
weightedBochnerSum xs weight value =
  bochnerSum xs (λ x → V.scale (weight x) (value x))
