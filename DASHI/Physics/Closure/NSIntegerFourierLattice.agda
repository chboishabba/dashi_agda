module DASHI.Physics.Closure.NSIntegerFourierLattice where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (ℤ; _+_; -_)

------------------------------------------------------------------------
-- Exact Fourier lattice Z^3.
------------------------------------------------------------------------

record FourierMode : Set where
  constructor mode
  field
    kx ky kz : ℤ

open FourierMode public

zeroMode : FourierMode
zeroMode = mode (+ 0) (+ 0) (+ 0)

addMode : FourierMode → FourierMode → FourierMode
addMode p q = mode
  (kx p + kx q)
  (ky p + ky q)
  (kz p + kz q)

negateMode : FourierMode → FourierMode
negateMode p = mode (- (kx p)) (- (ky p)) (- (kz p))

record NonZeroMode (k : FourierMode) : Set where
  field
    notZero : k ≡ zeroMode → ⊥

record Resonance (p q k : FourierMode) : Set where
  field
    closes : addMode p q ≡ k

record ShellPredicate : Set₁ where
  field
    InShell : FourierMode → Set

open ShellPredicate public

record ShellSeparated
    (low high : ShellPredicate) : Set₁ where
  field
    disjoint : ∀ k → InShell low k → InShell high k → ⊥

record ExactModeEquality : Set₁ where
  field
    modeEqual : FourierMode → FourierMode → Set
    modeEqualRefl : ∀ k → modeEqual k k

open ExactModeEquality public
