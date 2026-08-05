module DASHI.Physics.Closure.NSTriadKNLuoFiniteTerminalFarNearSplitExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Darko Mitrović.
-- Title: "A High-Frequency Tail Condition and a Diagnostic Iteration for
-- the Navier--Stokes Equations".
-- arXiv:2411.02568.
-- DOI: none assigned in the cited preprint version.
--
-- PURPOSE
-- Prove the finite combinatorics behind the terminal Duhamel split.  The first
-- `cutoff` samples form the far history and the remaining samples form the
-- near history.  The original list and every additive fold reconstruct
-- exactly from those two parts.  No heat-kernel estimate or tail condition is
-- hidden in this structural theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong)

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ right = right
(x ∷ xs) ++ right = x ∷ (xs ++ right)

farPart : ∀ {A : Set} → Nat → List A → List A
farPart zero samples = []
farPart (suc cutoff) [] = []
farPart (suc cutoff) (sample ∷ samples) =
  sample ∷ farPart cutoff samples

nearPart : ∀ {A : Set} → Nat → List A → List A
nearPart zero samples = samples
nearPart (suc cutoff) [] = []
nearPart (suc cutoff) (sample ∷ samples) =
  nearPart cutoff samples

farNearReconstruct :
  ∀ {A : Set}
    (cutoff : Nat)
    (samples : List A) →
  farPart cutoff samples ++ nearPart cutoff samples ≡ samples
farNearReconstruct zero samples = refl
farNearReconstruct (suc cutoff) [] = refl
farNearReconstruct (suc cutoff) (sample ∷ samples)
  rewrite farNearReconstruct cutoff samples = refl

sumBy :
  ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumBy [] value = 0ℚ
sumBy (sample ∷ samples) value =
  value sample + sumBy samples value

sumAppend :
  ∀ {A : Set}
    (left right : List A)
    (value : A → ℚ) →
  sumBy (left ++ right) value
  ≡ sumBy left value + sumBy right value
sumAppend [] right value = refl
sumAppend (sample ∷ samples) right value
  rewrite sumAppend samples right value =
  cong (value sample +_) refl

farNearFoldIdentity :
  ∀ {A : Set}
    (cutoff : Nat)
    (samples : List A)
    (value : A → ℚ) →
  sumBy samples value
  ≡ sumBy (farPart cutoff samples) value
    + sumBy (nearPart cutoff samples) value
farNearFoldIdentity cutoff samples value =
  let
    reconstructed = farNearReconstruct cutoff samples
    appended = sumAppend
      (farPart cutoff samples)
      (nearPart cutoff samples)
      value
  in
  trans
    (sym (cong (λ xs → sumBy xs value) reconstructed))
    appended
  where
  open import Relation.Binary.PropositionalEquality using (sym; trans)
