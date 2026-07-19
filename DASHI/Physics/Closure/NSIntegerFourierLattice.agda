module DASHI.Physics.Closure.NSIntegerFourierLattice where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Int using (Int; _+_; -_)
open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- Exact Fourier lattice Z^3.
------------------------------------------------------------------------

record FourierMode : Set where
  constructor mode
  field
    kx ky kz : Int

open FourierMode public

zeroMode : FourierMode
zeroMode = mode (+ 0) (+ 0) (+ 0)

addMode : FourierMode → FourierMode → FourierMode
addMode p q = mode
  (kx p + kx q)
  (ky p + ky q)
  (kz p + kz q)

negateMode : FourierMode → FourierMode
negateMode p = mode (- kx p) (- ky p) (- kz p)

record NonZeroMode (k : FourierMode) : Set where
  field
    notZero : k ≡ zeroMode → Set

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
    disjoint : ∀ k → InShell low k → InShell high k → Set

record ExactModeEquality : Set₁ where
  field
    modeEqual : FourierMode → FourierMode → Set
    modeEqualRefl : ∀ k → modeEqual k k

open ExactModeEquality public
