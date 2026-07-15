module DASHI.Physics.Closure.NSTriadKNExactLatticeTriadZeroSum where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Bool.Base using (_∧_)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice

------------------------------------------------------------------------
-- Propositional content of the exact Boolean zero-sum predicate.
--
-- The Fourier cancellation proof needs the coordinate equations carried by
-- `zeroSum? τ ≡ true`, not just the Boolean filter used by enumeration.
------------------------------------------------------------------------

andTrueLeft : (a b : Bool) → a ∧ b ≡ true → a ≡ true
andTrueLeft true b h = refl
andTrueLeft false b ()

andTrueRight : (a b : Bool) → a ∧ b ≡ true → b ≡ true
andTrueRight true b h = h
andTrueRight false b ()

isZeroTrueImpliesZero :
  (z : ℤ) → Lattice.isZero z ≡ true → z ≡ (+ 0)
isZeroTrueImpliesZero (+ zero) refl = refl
isZeroTrueImpliesZero (+ (suc n)) ()
isZeroTrueImpliesZero -[1+ n ] ()

triadZeroSumCoordinates :
  (τ : Lattice.LatticeTriad) → Lattice.zeroSum? τ ≡ true →
  ((Lattice.k₁ (Lattice.triadSum τ) ≡ (+ 0)) ×
   ((Lattice.k₂ (Lattice.triadSum τ) ≡ (+ 0)) ×
    (Lattice.k₃ (Lattice.triadSum τ) ≡ (+ 0))))
triadZeroSumCoordinates τ h =
  isZeroTrueImpliesZero first firstZero ,
  (isZeroTrueImpliesZero second secondZero ,
   isZeroTrueImpliesZero third thirdZero)
  where
  s = Lattice.triadSum τ
  first = Lattice.k₁ s
  second = Lattice.k₂ s
  third = Lattice.k₃ s
  firstZero : Lattice.isZero first ≡ true
  firstZero = andTrueLeft (Lattice.isZero first)
    (Lattice.isZero second ∧ Lattice.isZero third) h
  restZero : Lattice.isZero second ∧ Lattice.isZero third ≡ true
  restZero = andTrueRight (Lattice.isZero first)
    (Lattice.isZero second ∧ Lattice.isZero third) h
  secondZero : Lattice.isZero second ≡ true
  secondZero = andTrueLeft (Lattice.isZero second)
    (Lattice.isZero third) restZero
  thirdZero : Lattice.isZero third ≡ true
  thirdZero = andTrueRight (Lattice.isZero second)
    (Lattice.isZero third) restZero

-- The Boolean filter used by the finite enumeration has an extensional
-- geometric consequence: the three labelled modes add to the literal zero
-- lattice mode.  This is the form needed by a later linear wave-dot theorem;
-- it avoids treating `zeroSum?` merely as an opaque membership flag.
triadSumIsZeroMode :
  (τ : Lattice.LatticeTriad) → Lattice.zeroSum? τ ≡ true →
  Lattice.triadSum τ ≡ Lattice.mkLatticeMode3 (+ 0) (+ 0) (+ 0)
triadSumIsZeroMode τ h with triadZeroSumCoordinates τ h
... | firstZero , secondZero , thirdZero
  rewrite firstZero | secondZero | thirdZero = refl
