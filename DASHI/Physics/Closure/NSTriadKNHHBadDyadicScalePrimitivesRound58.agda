module DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 where

------------------------------------------------------------------------
-- Lightweight A-leaf.
--
-- This module contains only the rational dyadic scale and its reciprocal.
-- It deliberately does not import the sharp-gain, Holder, or Duhamel
-- development.  Physical HH-bad leaves can depend on this module without
-- pulling the old obstruction graph into memory.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _*_; _≤_; nonNegative)
import Data.Integer.Base as Int
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

half two : ℚ
half = Int.+ 1 / 2
two = Int.+ 2 / 1

dyadicScale : Nat → ℚ
dyadicScale zero = 1ℚ
dyadicScale (suc shell) = two * dyadicScale shell

inverseDyadicScale : Nat → ℚ
inverseDyadicScale zero = 1ℚ
inverseDyadicScale (suc shell) = half * inverseDyadicScale shell

twoNonnegative : 0ℚ ≤ two
twoNonnegative = toWitness {a? = 0ℚ ≤? two} _

dyadicScaleNonnegative : ∀ shell → 0ℚ ≤ dyadicScale shell
dyadicScaleNonnegative zero = toWitness {a? = 0ℚ ≤? 1ℚ} _
dyadicScaleNonnegative (suc shell) =
  let instance
    twoNN = nonNegative twoNonnegative
    shellNN = nonNegative (dyadicScaleNonnegative shell)
    productNN =
      ℚP.nonNeg*nonNeg⇒nonNeg two (dyadicScale shell)
  in ℚP.nonNegative⁻¹ (two * dyadicScale shell)
