module DASHI.Physics.Closure.NSTriadKNCanonicalRealityOrbitHalfLatticeRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- ROUND 63 / A0
--
-- Repair the Round62 reconstructed-state count growth with an actual canonical
-- half of the Fourier reality lattice.  For k in Z^3, inspect coordinates in
-- order x,y,z and choose k exactly when the first nonzero coordinate is
-- positive.  Thus every nonzero orbit {k,-k} has one and only one selected
-- representative.  No quotient type or arbitrary choice principle is needed.
--
-- This is the finite coordinate predicate required before building the fixed-
-- cutoff Picard carrier.  The opposite RHS coordinate can then be reconstructed
-- by the already-proved Fourier-reality theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base using (ℤ; +_; -[1+_])

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3

leadingPositive : Z3.FourierMode → Bool
leadingPositive (Z3.mode (+ zero) (+ zero) (+ zero)) = false
leadingPositive (Z3.mode (+ zero) (+ zero) (+ (suc z))) = true
leadingPositive (Z3.mode (+ zero) (+ zero) -[1+ z ]) = false
leadingPositive (Z3.mode (+ zero) (+ (suc y)) z) = true
leadingPositive (Z3.mode (+ zero) -[1+ y ] z) = false
leadingPositive (Z3.mode (+ (suc x)) y z) = true
leadingPositive (Z3.mode -[1+ x ] y z) = false

data RealityOrbitChoice (k : Z3.FourierMode) : Set where
  chooseK :
    leadingPositive k ≡ true →
    leadingPositive (Z3.negateMode k) ≡ false →
    RealityOrbitChoice k
  chooseNegK :
    leadingPositive k ≡ false →
    leadingPositive (Z3.negateMode k) ≡ true →
    RealityOrbitChoice k

canonicalNonzeroOrbitChoice :
  (k : Z3.FourierMode) →
  Z3.NonZeroMode k →
  RealityOrbitChoice k
canonicalNonzeroOrbitChoice
    (Z3.mode (+ zero) (+ zero) (+ zero)) nonzero =
  ⊥-elim (Z3.NonZeroMode.notZero nonzero refl)
canonicalNonzeroOrbitChoice
    (Z3.mode (+ zero) (+ zero) (+ (suc z))) nonzero =
  chooseK refl refl
canonicalNonzeroOrbitChoice
    (Z3.mode (+ zero) (+ zero) -[1+ z ]) nonzero =
  chooseNegK refl refl
canonicalNonzeroOrbitChoice
    (Z3.mode (+ zero) (+ (suc y)) z) nonzero =
  chooseK refl refl
canonicalNonzeroOrbitChoice
    (Z3.mode (+ zero) -[1+ y ] z) nonzero =
  chooseNegK refl refl
canonicalNonzeroOrbitChoice
    (Z3.mode (+ (suc x)) y z) nonzero =
  chooseK refl refl
canonicalNonzeroOrbitChoice
    (Z3.mode -[1+ x ] y z) nonzero =
  chooseNegK refl refl

zeroModeNotSelected : leadingPositive Z3.zeroMode ≡ false
zeroModeNotSelected = refl

selectedModeOppositeNotSelected :
  (k : Z3.FourierMode) →
  Z3.NonZeroMode k →
  leadingPositive k ≡ true →
  leadingPositive (Z3.negateMode k) ≡ false
selectedModeOppositeNotSelected k nonzero selected
  with canonicalNonzeroOrbitChoice k nonzero
... | chooseK kTrue negFalse = negFalse
... | chooseNegK kFalse negTrue with selected
... | ()

unselectedNonzeroModeOppositeSelected :
  (k : Z3.FourierMode) →
  Z3.NonZeroMode k →
  leadingPositive k ≡ false →
  leadingPositive (Z3.negateMode k) ≡ true
unselectedNonzeroModeOppositeSelected k nonzero unselected
  with canonicalNonzeroOrbitChoice k nonzero
... | chooseK kTrue negFalse with unselected
... | ()
... | chooseNegK kFalse negTrue = negTrue

canonicalRealityOrbitHalfLatticeConstructed : Bool
canonicalRealityOrbitHalfLatticeConstructed = true

canonicalRealityOrbitHalfLatticeConstructedIsTrue :
  canonicalRealityOrbitHalfLatticeConstructed ≡ true
canonicalRealityOrbitHalfLatticeConstructedIsTrue = refl
