module DASHI.Statistics.ZipfFullHeapsCurveIdentityNoGoExact where

-- H15 precise finite information-loss theorem, 2026-10-28.
-- Two sequences have EXACTLY the same multiset histogram and their entire
-- (not merely fitted) prefix vocabulary-size curves are identical, while
-- the identity of a repeated third token differs. Therefore no function
-- of the full Heaps curve alone can reconstruct repeated-token identity.
--
-- Reuses the original ZipfFamilyFiniteExact.countIf; no new probability
-- owner, no original empirical novelty law claim. Original Heaps/Herdan,
-- Zimmerlin et al. and Santoro/Petri/Tria authors retain independent work.
-- Johl Brown-directed source formalization with ChatGPT assistance.
-- No Agda kernel typecheck claimed. No Monster/NS/RH same-object claim.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import DASHI.Statistics.ZipfFamilyFiniteExact as Zipf

data Letter : Set where
  A B C : Letter

isA : Letter → Bool
isA A = true
isA _ = false

isB : Letter → Bool
isB B = true
isB _ = false

isC : Letter → Bool
isC C = true
isC _ = false

record ThreeTypeHistogram : Set where
  constructor frequencies
  field
    aCount bCount cCount : Nat

observedHistogram : List Letter → ThreeTypeHistogram
observedHistogram xs =
  frequencies (Zipf.countIf isA xs) (Zipf.countIf isB xs)
              (Zipf.countIf isC xs)

indicator : Bool → Nat
indicator true = suc zero
indicator false = zero

seenA : List Letter → Bool
seenA [] = false
seenA (A ∷ xs) = true
seenA (_ ∷ xs) = seenA xs

seenB : List Letter → Bool
seenB [] = false
seenB (B ∷ xs) = true
seenB (_ ∷ xs) = seenB xs

seenC : List Letter → Bool
seenC [] = false
seenC (C ∷ xs) = true
seenC (_ ∷ xs) = seenC xs

distinctCount : List Letter → Nat
distinctCount xs =
  indicator (seenA xs) + indicator (seenB xs) +
  indicator (seenC xs)

-- The accumulator reverses the seen prefix, which does not alter which
-- types have appeared. The output includes t=0 and every t up to length.
prefixCurveAcc : List Letter → List Letter → List Nat
prefixCurveAcc seen [] = distinctCount seen ∷ []
prefixCurveAcc seen (x ∷ xs) =
  distinctCount seen ∷ prefixCurveAcc (x ∷ seen) xs

fullHeapsCurve : List Letter → List Nat
fullHeapsCurve = prefixCurveAcc []

-- First repeated identity differs at the third token.
leftWord : List Letter
leftWord = A ∷ B ∷ A ∷ C ∷ B ∷ []

rightWord : List Letter
rightWord = A ∷ B ∷ B ∷ C ∷ A ∷ []

sameTerminalHistogram :
  observedHistogram leftWord ≡ observedHistogram rightWord
sameTerminalHistogram = refl

sameFullHeapsCurve :
  fullHeapsCurve leftWord ≡ fullHeapsCurve rightWord
sameFullHeapsCurve = refl

sameConcreteCurve :
  fullHeapsCurve leftWord ≡
  (zero ∷ suc zero ∷ suc (suc zero) ∷ suc (suc zero) ∷
   suc (suc (suc zero)) ∷ suc (suc (suc zero)) ∷ [])
sameConcreteCurve = refl

thirdToken : List Letter → Letter
thirdToken (_ ∷ _ ∷ x ∷ xs) = x
thirdToken _ = A

data ⊥ : Set where

A≢B : A ≡ B → ⊥
A≢B ()

-- A universal inverse from the complete vocabulary curve to the identity
-- of the third token is impossible. This is a genuine negative theorem,
-- not a statement about corpus-specific Zipf exponents.
fullCurveCannotRecoverRepeatedIdentity :
  (recover : List Nat → Letter) →
  ((xs : List Letter) →
     recover (fullHeapsCurve xs) ≡ thirdToken xs) →
  ⊥
fullCurveCannotRecoverRepeatedIdentity recover correct =
  A≢B
    (trans
      (sym (correct leftWord))
      (trans
        (cong recover sameFullHeapsCurve)
        (correct rightWord)))
