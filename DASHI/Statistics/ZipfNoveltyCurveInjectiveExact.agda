module DASHI.Statistics.ZipfNoveltyCurveInjectiveExact where

-- H14 finite logical completion. The entire (unfitted) prefix vocabulary
-- curve of a valid novelty-flag sequence identifies that sequence.
-- This statement is about FIRST-DISCOVERY BOOL EVENTS, not the identity
-- of a previously seen token. H15 gives a sharp counterexample to that
-- latter promotion. No assumption about IID/permutation chronology.
--
-- Mathematical predecessor: elementary finite prefix-sum injectivity.
-- Source adaptation by Johl Brown with OpenAI ChatGPT assistance,
-- 2026-10-28. Kernel typecheck not executed. No external proof ownership
-- of Heaps/Herdan, Zimmerlin et al. or Santoro et al. is transferred.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym)
open import Data.Empty using (⊥; ⊥-elim)

-- Flags are interpreted as +1 on first discovery, +0 otherwise.
-- The starting count is included. The resulting curve is length n+1.
-- No empirical power law is inferred from this construction.
curveFromFlags : Nat → List Bool → List Nat
curveFromFlags n [] = n ∷ []
curveFromFlags n (true ∷ xs) =
  n ∷ curveFromFlags (suc n) xs
curveFromFlags n (false ∷ xs) =
  n ∷ curveFromFlags n xs

curveFromZero : List Bool → List Nat
curveFromZero = curveFromFlags zero

tailInjective : ∀ {A : Set} {x y : A} {xs ys : List A} →
  x ∷ xs ≡ y ∷ ys → xs ≡ ys
tailInjective refl = refl

listHeadOrZero : List Nat → Nat
listHeadOrZero [] = zero
listHeadOrZero (n ∷ ns) = n

sucInjective : ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
sucInjective refl = refl

sucNotSelf : ∀ n → suc n ≡ n → ⊥
sucNotSelf zero ()
sucNotSelf (suc n) proof =
  sucNotSelf n (sucInjective proof)

-- Equality of complete, valid curves forces equality of each binary
-- novelty event. A fitted exponent or only the final V_n cannot do this.
curveFromFlagsInjective :
  ∀ n xs ys → curveFromFlags n xs ≡ curveFromFlags n ys →
  xs ≡ ys
curveFromFlagsInjective n [] [] proof = refl
curveFromFlagsInjective n [] (true ∷ ys) ()
curveFromFlagsInjective n [] (false ∷ ys) ()
curveFromFlagsInjective n (true ∷ xs) [] ()
curveFromFlagsInjective n (false ∷ xs) [] ()
curveFromFlagsInjective n (true ∷ xs) (true ∷ ys) proof =
  cong (true ∷_)
    (curveFromFlagsInjective (suc n) xs ys
      (tailInjective proof))
curveFromFlagsInjective n (false ∷ xs) (false ∷ ys) proof =
  cong (false ∷_)
    (curveFromFlagsInjective n xs ys
      (tailInjective proof))
curveFromFlagsInjective n (true ∷ xs) (false ∷ ys) proof =
  ⊥-elim (sucNotSelf n
    (cong listHeadOrZero (tailInjective proof)))
curveFromFlagsInjective n (false ∷ xs) (true ∷ ys) proof =
  ⊥-elim (sucNotSelf n
    (sym (cong listHeadOrZero (tailInjective proof))))

zeroBasedFlagsInjective :
  ∀ xs ys → curveFromZero xs ≡ curveFromZero ys → xs ≡ ys
zeroBasedFlagsInjective xs ys proof =
  curveFromFlagsInjective zero xs ys proof

-- This does not contradict H15: equal novelty flags may correspond to
-- different repeated-token labels when at least two types are present.
