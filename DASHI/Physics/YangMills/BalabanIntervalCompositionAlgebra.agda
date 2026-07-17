module DASHI.Physics.YangMills.BalabanIntervalCompositionAlgebra where

-- Concatenation law for arbitrary scale intervals.
--
-- An interval of length `n` from `k`, followed by an interval of length `m`
-- from `n + k`, is the interval of length `m + n` from `k`.  This module proves
-- the corresponding sum identity and transports lower/upper estimates across
-- the concatenation.  It is needed for subinterval continuation and history
-- control; no analytic bound is asserted here.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _+ℝ_
  ; _≤ℝ_
  ; +-identityʳ
  ; +-assoc
  ; +-mono-≤
  ; cong
  ; trans
  )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum )

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

natAddAssoc :
  ∀ a b c →
  (a + b) + c ≡ a + (b + c)
natAddAssoc zero b c = refl
natAddAssoc (suc a) b c =
  cong suc (natAddAssoc a b c)

intervalSumAppend :
  (f : ℕ → ℝ) →
  ∀ k n m →
  intervalSum f k (m + n)
    ≡ intervalSum f k n
        +ℝ intervalSum f (n + k) m
intervalSumAppend f k n zero =
  sym (+-identityʳ (intervalSum f k n))
intervalSumAppend f k n (suc m) =
  let
    leftPrefix = intervalSum f k n
    rightPrefix = intervalSum f (n + k) m
    leftIndex = (m + n) + k
    rightIndex = m + (n + k)
    leftShell = f (suc leftIndex)
    rightShell = f (suc rightIndex)
    ih = intervalSumAppend f k n m
    indexEquality = natAddAssoc m n k
    shellEquality = cong (λ index → f (suc index)) indexEquality
    p1 = cong (λ x → x +ℝ leftShell) ih
    p2 = +-assoc leftPrefix rightPrefix leftShell
    p3 = cong
      (λ shell → leftPrefix +ℝ (rightPrefix +ℝ shell))
      shellEquality
  in
    trans p1 (trans p2 p3)

replaceLeft :
  ∀ {a b c : ℝ} →
  a ≡ b →
  b ≤ℝ c →
  a ≤ℝ c
replaceLeft refl b≤c = b≤c

replaceRight :
  ∀ {a b c : ℝ} →
  a ≤ℝ b →
  b ≡ c →
  a ≤ℝ c
replaceRight a≤b refl = a≤b

intervalUpperBoundAppend :
  (f : ℕ → ℝ) →
  (upper : ℕ → ℕ → ℝ) →
  (firstBound :
    ∀ k n →
    intervalSum f k n ≤ℝ upper k n) →
  ∀ k n m →
  intervalSum f k (m + n)
    ≤ℝ upper k n +ℝ upper (n + k) m
intervalUpperBoundAppend f upper firstBound k n m =
  replaceLeft
    (intervalSumAppend f k n m)
    (+-mono-≤
      (firstBound k n)
      (firstBound (n + k) m))

intervalLowerBoundAppend :
  (f : ℕ → ℝ) →
  (lower : ℕ → ℕ → ℝ) →
  (firstBound :
    ∀ k n →
    lower k n ≤ℝ intervalSum f k n) →
  ∀ k n m →
  lower k n +ℝ lower (n + k) m
    ≤ℝ intervalSum f k (m + n)
intervalLowerBoundAppend f lower firstBound k n m =
  replaceRight
    (+-mono-≤
      (firstBound k n)
      (firstBound (n + k) m))
    (sym (intervalSumAppend f k n m))
