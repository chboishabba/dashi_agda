module DASHI.Physics.Closure.NSTriadKNHHPhysicalDefectRarityTransferRound40Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Zoran Grujic.
-- Title: "A Geometric Measure-Type Regularity Criterion for Solutions to the
-- 3D Navier--Stokes Equations".
-- DOI: 10.1088/0951-7715/26/1/289.
-- arXiv DOI: 10.48550/arXiv.1111.0217.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- The repository already contains the exact shellwise transfer
--
--   weightedDefectMass_q <= delta_q rarity_q
--      -> badMass_q <= rarity_q
--      -> rarity_q -> 0 implies badMass_q -> 0.
--
-- Round 40's new HH cells use the actual physical vorticity-direction carrier.
-- This module connects them directly to that mature transfer.  Therefore the
-- new `E*Theta` unification does not need a duplicate abstract rarity/evolution
-- layer: the only remaining physical producer is the normalized weighted-
-- defect envelope itself.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Markov
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedDefectTransferExact as Transfer
import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Limit
import DASHI.Physics.Closure.NSTriadKNHHUnifiedDirectionalDefectRound40Exact as HH

record PhysicalDirectionalDefectRarityFamily : Set₁ where
  field
    parameter : Nat → Markov.PositiveThreshold
    physicalCells :
      (shell : Nat) →
      List (HH.PhysicalBadDirectionalEnergyCell (parameter shell))
    rarityEnvelope : Nat → ℚ

    physicalWeightedDefectByEnvelope :
      (shell : Nat) →
      HH.weightedDirectionalDefectMass (physicalCells shell)
      ≤ Markov.threshold (parameter shell) * rarityEnvelope shell

open PhysicalDirectionalDefectRarityFamily public

asDynamicBadCellFamily :
  PhysicalDirectionalDefectRarityFamily → Transfer.DynamicBadCellFamily
asDynamicBadCellFamily family = Transfer.dynamic-bad-cell-family
  (parameter family)
  (λ shell → HH.mapBadCells (physicalCells family shell))
  (rarityEnvelope family)
  (physicalWeightedDefectByEnvelope family)

physicalBadEnergyMass :
  PhysicalDirectionalDefectRarityFamily → Nat → ℚ
physicalBadEnergyMass family shell =
  HH.badEnergyMass (physicalCells family shell)

physicalBadMassMeaning :
  (family : PhysicalDirectionalDefectRarityFamily) →
  (shell : Nat) →
  Transfer.badMass (asDynamicBadCellFamily family) shell
  ≡ physicalBadEnergyMass family shell
physicalBadMassMeaning family shell = refl

physicalBadMassBelowRarityEnvelope :
  (family : PhysicalDirectionalDefectRarityFamily) →
  (shell : Nat) →
  physicalBadEnergyMass family shell ≤ rarityEnvelope family shell
physicalBadMassBelowRarityEnvelope family shell =
  Transfer.badMassBelowNormalizedWeightedDefect
    (asDynamicBadCellFamily family) shell

physicalBadMassVanishingFromWeightedDefectEnvelope :
  (family : PhysicalDirectionalDefectRarityFamily) →
  Limit.TendsToZero (rarityEnvelope family) →
  Limit.TendsToZero (physicalBadEnergyMass family)
physicalBadMassVanishingFromWeightedDefectEnvelope family rarityVanishing =
  Transfer.badMassVanishingFromWeightedDefectEnvelope
    (asDynamicBadCellFamily family) rarityVanishing

hhPhysicalDefectRarityTransferClosed : Agda.Builtin.Bool.Bool
hhPhysicalDefectRarityTransferClosed = Agda.Builtin.Bool.true

physicalNormalizedWeightedDefectEnvelopeConstructed : Agda.Builtin.Bool.Bool
physicalNormalizedWeightedDefectEnvelopeConstructed = Agda.Builtin.Bool.false

hhPhysicalDefectRarityTransferClosedIsTrue :
  hhPhysicalDefectRarityTransferClosed ≡ Agda.Builtin.Bool.true
hhPhysicalDefectRarityTransferClosedIsTrue = Agda.Builtin.Equality.refl
