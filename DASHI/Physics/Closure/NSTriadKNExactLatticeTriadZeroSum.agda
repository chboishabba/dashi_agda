module DASHI.Physics.Closure.NSTriadKNExactLatticeTriadZeroSum where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Bool.Base using (_∧_)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.Integer.Properties as ℤP using (+-assoc; +-comm)
import Data.Integer.Base as ℤ
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym)

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

-- Cyclic relabelling preserves the exact Boolean zero-sum predicate.  The
-- Fourier cancellation route uses this to apply one wave-dot reversal lemma
-- in each output orientation, rather than maintaining three independent
-- geometric assumptions.
zeroSumCycleInvariant :
  (τ : Lattice.LatticeTriad) →
  Lattice.zeroSum? (Lattice.triadCycle τ) ≡ Lattice.zeroSum? τ
zeroSumCycleInvariant (Lattice.mkLatticeTriad p q r)
  rewrite ℤP.+-assoc (Lattice.k₁ q) (Lattice.k₁ r) (Lattice.k₁ p)
        | ℤP.+-assoc (Lattice.k₂ q) (Lattice.k₂ r) (Lattice.k₂ p)
        | ℤP.+-assoc (Lattice.k₃ q) (Lattice.k₃ r) (Lattice.k₃ p)
        | ℤP.+-comm (Lattice.k₁ r) (Lattice.k₁ p)
        | ℤP.+-comm (Lattice.k₂ r) (Lattice.k₂ p)
        | ℤP.+-comm (Lattice.k₃ r) (Lattice.k₃ p)
        | sym (ℤP.+-assoc (Lattice.k₁ q) (Lattice.k₁ p) (Lattice.k₁ r))
        | sym (ℤP.+-assoc (Lattice.k₂ q) (Lattice.k₂ p) (Lattice.k₂ r))
        | sym (ℤP.+-assoc (Lattice.k₃ q) (Lattice.k₃ p) (Lattice.k₃ r))
        | ℤP.+-comm (Lattice.k₁ q) (Lattice.k₁ p)
        | ℤP.+-comm (Lattice.k₂ q) (Lattice.k₂ p)
        | ℤP.+-comm (Lattice.k₃ q) (Lattice.k₃ p) = refl

zeroSumCycle :
  (τ : Lattice.LatticeTriad) → Lattice.zeroSum? τ ≡ true →
  Lattice.zeroSum? (Lattice.triadCycle τ) ≡ true
zeroSumCycle τ zeroSum rewrite zeroSumCycleInvariant τ = zeroSum

zeroSumSwapInvariant :
  (τ : Lattice.LatticeTriad) →
  Lattice.zeroSum? (Lattice.triadSwap τ) ≡ Lattice.zeroSum? τ
zeroSumSwapInvariant (Lattice.mkLatticeTriad p q r)
  rewrite ℤP.+-comm (Lattice.k₁ q) (Lattice.k₁ p)
        | ℤP.+-comm (Lattice.k₂ q) (Lattice.k₂ p)
        | ℤP.+-comm (Lattice.k₃ q) (Lattice.k₃ p) = refl

zeroSumSwap :
  (τ : Lattice.LatticeTriad) → Lattice.zeroSum? τ ≡ true →
  Lattice.zeroSum? (Lattice.triadSwap τ) ≡ true
zeroSumSwap τ zeroSum rewrite zeroSumSwapInvariant τ = zeroSum

------------------------------------------------------------------------
-- Reality negation preserves the exact Boolean zero-sum predicate.
-- Together with cycle and swap, this supplies the zero-sum component of all
-- twelve permutation/reality actions used by the canonical triad orbit.
------------------------------------------------------------------------

isZeroNegInvariant :
  (z : ℤ) → Lattice.isZero (ℤ.- z) ≡ Lattice.isZero z
isZeroNegInvariant (+ zero) = refl
isZeroNegInvariant (+ suc n) = refl
isZeroNegInvariant -[1+ n ] = refl

zeroSumNegInvariant :
  (τ : Lattice.LatticeTriad) →
  Lattice.zeroSum? (Lattice.triadNeg τ) ≡ Lattice.zeroSum? τ
zeroSumNegInvariant (Lattice.mkLatticeTriad p q r)
  rewrite sym (ℤP.neg-distrib-+ (Lattice.k₁ p) (Lattice.k₁ q))
        | sym (ℤP.neg-distrib-+ ((Lattice.k₁ p) ℤ.+ (Lattice.k₁ q)) (Lattice.k₁ r))
        | sym (ℤP.neg-distrib-+ (Lattice.k₂ p) (Lattice.k₂ q))
        | sym (ℤP.neg-distrib-+ ((Lattice.k₂ p) ℤ.+ (Lattice.k₂ q)) (Lattice.k₂ r))
        | sym (ℤP.neg-distrib-+ (Lattice.k₃ p) (Lattice.k₃ q))
        | sym (ℤP.neg-distrib-+ ((Lattice.k₃ p) ℤ.+ (Lattice.k₃ q)) (Lattice.k₃ r))
        | isZeroNegInvariant (((Lattice.k₁ p) ℤ.+ (Lattice.k₁ q)) ℤ.+ Lattice.k₁ r)
        | isZeroNegInvariant (((Lattice.k₂ p) ℤ.+ (Lattice.k₂ q)) ℤ.+ Lattice.k₂ r)
        | isZeroNegInvariant (((Lattice.k₃ p) ℤ.+ (Lattice.k₃ q)) ℤ.+ Lattice.k₃ r) = refl

zeroSumNeg :
  (τ : Lattice.LatticeTriad) → Lattice.zeroSum? τ ≡ true →
  Lattice.zeroSum? (Lattice.triadNeg τ) ≡ true
zeroSumNeg τ zeroSum rewrite zeroSumNegInvariant τ = zeroSum
