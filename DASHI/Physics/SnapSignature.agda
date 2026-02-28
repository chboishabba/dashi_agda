module DASHI.Physics.SnapSignature where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_≤_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)

¬_ : Set → Set
¬ P = P → ⊥

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

-- Count coordinates that snap from nonzero to zero in a single step.
countZeroSnaps : ∀ {n : Nat} → Vec Trit n → Vec Trit n → Nat
countZeroSnaps [] [] = zero
countZeroSnaps (x ∷ xs) (y ∷ ys) =
  snap x y + countZeroSnaps xs ys
  where
    snap : Trit → Trit → Nat
    snap neg zer = suc zero
    snap pos zer = suc zero
    snap _   _   = zero

-- Predicate: at least k zero-snaps.
SnapAtLeast : ∀ {n : Nat} → Nat → Vec Trit n → Vec Trit n → Set
SnapAtLeast k x y = k ≤ countZeroSnaps x y

-- Abstract diagnostic bundle for a step x -> y.
record SnapSignature {S : Set} : Set₁ where
  field
    -- concrete state
    step : S → S → Set

    -- trigger 1: multi-coordinate zeroing (sheet elimination)
    snapZero : S → S → Set

    -- trigger 2: chi2 spike (boundary blow-up)
    chi2Spike : S → S → Set

    -- trigger 3: MDL proxy descent (valid IR movement)
    mdlDescent : S → S → Set

-- Canonical combined predicate for a snap event.
record IsSnap {S : Set} (Sig : SnapSignature {S}) : Set₁ where
  field
    snap : ∀ x y →
      SnapSignature.step Sig x y →
      SnapSignature.snapZero Sig x y →
      SnapSignature.chi2Spike Sig x y →
      SnapSignature.mdlDescent Sig x y →
      Set

-- Cone monotonicity except snaps: if not a snap, interior is preserved.
record ConeMonotoneExceptSnaps {S : Set} : Set₁ where
  field
    InInterior : S → Set
    Boundary   : S → Set
    T          : S → S
    Sig        : SnapSignature {S}

    monotoneExceptSnap : ∀ x →
      InInterior x →
      (¬ (SnapSignature.step Sig x (T x) ×
          SnapSignature.snapZero Sig x (T x) ×
          SnapSignature.chi2Spike Sig x (T x) ×
          SnapSignature.mdlDescent Sig x (T x))) →
      InInterior (T x) ⊎ Boundary (T x)
