module DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedDefectTransferExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42014.
--
-- Author: Zoran Grujić.
-- Title: "A Geometric Measure-Type Regularity Criterion for Solutions to the
-- 3D Navier-Stokes Equations".
-- DOI: 10.1088/0951-7715/26/1/289.
-- arXiv DOI: 10.48550/arXiv.1111.0217.
--
-- PURPOSE
-- Compose the finite weighted Markov theorem with a shellwise normalized
-- defect estimate. The only producer retained is
--
--   weightedDefectMass_q
--     <= delta_q * rarityEnvelope_q.
--
-- Markov gives
--
--   delta_q * badMass_q <= weightedDefectMass_q,
--
-- positivity cancels delta_q, and rarityEnvelope_q -> 0 implies badMass_q ->
-- zero. Thus the geometric frontier is sharpened from a direct bad-set rarity
-- assertion to a normalized weighted directional-defect estimate.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Markov
import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Limit

record DynamicBadCellFamily : Set₁ where
  constructor dynamic-bad-cell-family
  field
    parameter : Nat → Markov.PositiveThreshold
    cells :
      (shell : Nat) →
      List (Markov.BadCoherenceCell (parameter shell))
    rarityEnvelope : Nat → ℚ

    weightedDefectByEnvelope :
      (shell : Nat) →
      Markov.weightedDefectMass
          (parameter shell)
          (cells shell)
      ≤ Markov.threshold (parameter shell) * rarityEnvelope shell

open DynamicBadCellFamily public

badMass : DynamicBadCellFamily → Nat → ℚ
badMass dataSet shell =
  Markov.badWeightMass
    (parameter dataSet shell)
    (cells dataSet shell)

scaledBadMassByEnvelope :
  (dataSet : DynamicBadCellFamily) →
  (shell : Nat) →
  Markov.threshold (parameter dataSet shell) * badMass dataSet shell
  ≤ Markov.threshold (parameter dataSet shell)
    * rarityEnvelope dataSet shell
scaledBadMassByEnvelope dataSet shell =
  ℚₚ.≤-trans
    (Markov.thresholdTimesBadWeightBelowDefect
      (parameter dataSet shell)
      (cells dataSet shell))
    (weightedDefectByEnvelope dataSet shell)

badMassBelowNormalizedWeightedDefect :
  (dataSet : DynamicBadCellFamily) →
  (shell : Nat) →
  badMass dataSet shell ≤ rarityEnvelope dataSet shell
badMassBelowNormalizedWeightedDefect dataSet shell =
  Markov.positiveThresholdCancellation
    (parameter dataSet shell)
    (badMass dataSet shell)
    (rarityEnvelope dataSet shell)
    (scaledBadMassByEnvelope dataSet shell)

badMassVanishingFromWeightedDefectEnvelope :
  (dataSet : DynamicBadCellFamily) →
  Limit.TendsToZero (rarityEnvelope dataSet) →
  Limit.TendsToZero (badMass dataSet)
badMassVanishingFromWeightedDefectEnvelope dataSet rarityVanishing =
  Limit.interactionDepletionFromCriticalDepletion
    (Limit.critical-to-interaction-data
      (badMass dataSet)
      (rarityEnvelope dataSet)
      (badMassBelowNormalizedWeightedDefect dataSet))
    rarityVanishing
