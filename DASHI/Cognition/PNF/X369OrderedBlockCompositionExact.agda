module DASHI.Cognition.PNF.X369OrderedBlockCompositionExact where

-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Exact semantic action and ordered history are separate carriers.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as F

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
infixr 5 _++_

appendAssoc : ∀ {A : Set} (xs ys zs : List A) →
  (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
appendAssoc [] ys zs = refl
appendAssoc (x ∷ xs) ys zs = F.cong (λ w → x ∷ w) (appendAssoc xs ys zs)

extent : ∀ {A : Set} → List A → Nat
extent [] = zero
extent (_ ∷ xs) = suc (extent xs)

extentAppend : ∀ {A : Set} (xs ys : List A) →
  extent (xs ++ ys) ≡ extent xs + extent ys
extentAppend [] ys = refl
extentAppend (x ∷ xs) ys = F.cong suc (extentAppend xs ys)

first : ∀ {A : Set} → List A → Maybe A
first [] = nothing
first (x ∷ xs) = just x

choose : ∀ {A : Set} → Maybe A → Maybe A → Maybe A
choose nothing b = b
choose (just a) b = just a

firstAppend : ∀ {A : Set} (xs ys : List A) →
  first (xs ++ ys) ≡ choose (first xs) (first ys)
firstAppend [] ys = refl
firstAppend (x ∷ xs) ys = refl

module Action {Input State : Set} (step : Input → State → State) where
  run : List Input → State → State
  run [] z = z
  run (u ∷ us) z = run us (step u z)

  blockComposition : (xs ys : List Input) (z : State) →
    run (xs ++ ys) z ≡ run ys (run xs z)
  blockComposition [] ys z = refl
  blockComposition (u ∷ us) ys z = blockComposition us ys (step u z)

  blockAssociativity : (xs ys zs : List Input) (z : State) →
    run ((xs ++ ys) ++ zs) z ≡ run (xs ++ (ys ++ zs)) z
  blockAssociativity xs ys zs z =
    F.cong (λ w → run w z) (appendAssoc xs ys zs)

  -- Repetition by doubling is justified by blockComposition. This is
  -- an extensional law, not a physical bit-complexity certificate.
  doubleBlock : (xs : List Input) (z : State) →
    run (xs ++ xs) z ≡ run xs (run xs z)
  doubleBlock xs z = blockComposition xs xs z
