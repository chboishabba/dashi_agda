module DASHI.Physics.Closure.NSTriadKNLuoFiniteCharacterMultiplierBridgeExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions
-- of Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- PURPOSE
-- Connect the proved finite weighted-character identity to the repository's
-- canonical increment multiplier.  This removes the finite coefficient
-- equality, symmetry and zero-mode cancellation from the primitive physical
-- leaf set: on a finite character system they are theorems.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteCharacterWeightedIncrementExact as Finite
import DASHI.Physics.Closure.NSTriadKNLuoIncrementKernelFourierMultiplierExact as Multiplier

finitePeriodicIncrementMultiplierData :
  (system : Finite.FiniteCharacterSystem) →
  Multiplier.PeriodicIncrementMultiplierData (Finite.Mode system)
finitePeriodicIncrementMultiplierData system = record
  { zeroMode = Finite.zeroMode system
  ; addMode = Finite.addMode system
  ; kernelTransform = Finite.finiteKernelTransform system
  ; addZeroLeft = Finite.addZeroLeft system
  ; addZeroRight = Finite.addZeroRight system
  ; addCommutative = Finite.addCommutative system
  }

finiteWeightedIncrementEqualsPairMultiplier :
  (system : Finite.FiniteCharacterSystem) →
  (left right : Finite.Mode system) →
  Finite.finiteWeightedIncrement system left right
  ≡ Multiplier.pairMultiplier
      (finitePeriodicIncrementMultiplierData system)
      left
      right
finiteWeightedIncrementEqualsPairMultiplier system left right =
  Finite.finiteWeightedIncrementFourierIdentity system left right

finiteWeightedIncrementSymmetric :
  (system : Finite.FiniteCharacterSystem) →
  (left right : Finite.Mode system) →
  Finite.finiteWeightedIncrement system left right
  ≡ Finite.finiteWeightedIncrement system right left
finiteWeightedIncrementSymmetric system left right =
  trans
    (finiteWeightedIncrementEqualsPairMultiplier system left right)
    (trans
      (Multiplier.pairMultiplierSymmetric
        (finitePeriodicIncrementMultiplierData system)
        left
        right)
      (sym
        (finiteWeightedIncrementEqualsPairMultiplier system right left)))

finiteWeightedIncrementLeftZero :
  (system : Finite.FiniteCharacterSystem) →
  (mode : Finite.Mode system) →
  Finite.finiteWeightedIncrement system (Finite.zeroMode system) mode
  ≡ 0ℚ
finiteWeightedIncrementLeftZero system mode =
  trans
    (finiteWeightedIncrementEqualsPairMultiplier
      system (Finite.zeroMode system) mode)
    (Multiplier.pairMultiplierLeftZero
      (finitePeriodicIncrementMultiplierData system)
      mode)

finiteWeightedIncrementRightZero :
  (system : Finite.FiniteCharacterSystem) →
  (mode : Finite.Mode system) →
  Finite.finiteWeightedIncrement system mode (Finite.zeroMode system)
  ≡ 0ℚ
finiteWeightedIncrementRightZero system mode =
  trans
    (finiteWeightedIncrementEqualsPairMultiplier
      system mode (Finite.zeroMode system))
    (Multiplier.pairMultiplierRightZero
      (finitePeriodicIncrementMultiplierData system)
      mode)

finiteCharacterMultiplierBridgeClosed : Bool
finiteCharacterMultiplierBridgeClosed = true

finiteCharacterZeroModeCancellationClosed : Bool
finiteCharacterZeroModeCancellationClosed = true

finiteCharacterMultiplierBridgeClosedIsTrue :
  finiteCharacterMultiplierBridgeClosed ≡ true
finiteCharacterMultiplierBridgeClosedIsTrue = refl

finiteCharacterZeroModeCancellationClosedIsTrue :
  finiteCharacterZeroModeCancellationClosed ≡ true
finiteCharacterZeroModeCancellationClosedIsTrue = refl
