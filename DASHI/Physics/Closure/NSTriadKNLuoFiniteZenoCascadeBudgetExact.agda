module DASHI.Physics.Closure.NSTriadKNLuoFiniteZenoCascadeBudgetExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Terence Tao.
-- Title: "Finite Time Blowup for an Averaged Three-Dimensional
-- Navier--Stokes Equation".
-- Journal of the American Mathematical Society 29 (2016), 601--674.
-- DOI: 10.1090/jams/838.
--
-- PURPOSE
-- Formalise the finite arithmetic behind the warning that bounded energy and
-- bounded elapsed time do not by themselves bound the number of cascade
-- generations.  Give generation n both energy payment (1/2)^n and time
-- payment (1/2)^n.  Every finite prefix is bounded by 2, while the terminal
-- frequency scale still doubles at every generation.
--
-- This is not a blowup construction for the genuine equations.  It proves
-- only that the scalar budget objection to a Zeno cascade is insufficient.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _*_; _-_; _≤_; _<_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_; _<?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

half two : ℚ
half = Int.+ 1 / 2
two = Int.+ 2 / 1

halfNonnegative : 0ℚ ≤ half
halfNonnegative = toWitness {a? = 0ℚ ≤? half} _

oneMinusHalfPositive : 0ℚ < 1ℚ - half
oneMinusHalfPositive = toWitness {a? = 0ℚ <? 1ℚ - half} _

halfBoundIdentity :
  (1ℚ - half) * two ≡ 1ℚ
halfBoundIdentity = refl

generationPayment : Nat → ℚ
generationPayment = Geo.pow half

finiteCascadePayment : Nat → ℚ
finiteCascadePayment = Geo.partialSum half

finiteEnergyBudget :
  (lastGeneration : Nat) →
  finiteCascadePayment lastGeneration ≤ two
finiteEnergyBudget lastGeneration =
  Geo.geometricPartialSumBound
    half two lastGeneration
    halfNonnegative oneMinusHalfPositive halfBoundIdentity

finiteTimeBudget :
  (lastGeneration : Nat) →
  finiteCascadePayment lastGeneration ≤ two
finiteTimeBudget = finiteEnergyBudget

dyadicFrequency : Nat → ℚ
dyadicFrequency = Geo.pow two

frequencyDoubles :
  (generation : Nat) →
  dyadicFrequency (suc generation)
  ≡ two * dyadicFrequency generation
frequencyDoubles generation = refl

paymentHalves :
  (generation : Nat) →
  generationPayment (suc generation)
  ≡ half * generationPayment generation
paymentHalves generation = refl
