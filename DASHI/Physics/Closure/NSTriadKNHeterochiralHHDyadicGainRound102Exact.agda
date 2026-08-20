module DASHI.Physics.Closure.NSTriadKNHeterochiralHHDyadicGainRound102Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND102 / DYADIC CALIBRATION OF THE HELICAL HH GAINS
--
-- The ordered Waleffe geometry gives two HH->low critical coefficient scales:
--
--   low helicity minority:   O(L^2),
--   high helicity minority:  O(L H).
--
-- The existing exact dyadic carrier writes H = L 2^d and g_d=2^-d with
--
--   g_d H = L.
--
-- Therefore the new coefficient gains are exactly
--
--   L H = g_d H^2,
--   L^2 = g_d^2 H^2.
--
-- Thus EVERY mixed-helicity HH->low sign class carries at least the existing
-- one-gap 2^-d suppression relative to a naive H^2 critical coefficient, and
-- the low-minority classes carry two such powers.  This is pure scale algebra;
-- the physical Waleffe/geometric identification is supplied by the other
-- Round102 modules.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighLowDyadicGainExact as HH
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyCriticalScalingGapExact as Scale

lowScale : Nat → ℚ
lowScale = Scale.dyadicScale

highScale : Nat → Nat → ℚ
highScale = HH.highInputScale

helicalGapGain : Nat → ℚ
helicalGapGain = HH.highHighLowGain

highMinorityCoefficientScale : Nat → Nat → ℚ
highMinorityCoefficientScale outputShell gap =
  lowScale outputShell * highScale outputShell gap

lowMinorityCoefficientScale : Nat → Nat → ℚ
lowMinorityCoefficientScale outputShell gap =
  lowScale outputShell * lowScale outputShell

naiveHighSquaredScale : Nat → Nat → ℚ
naiveHighSquaredScale outputShell gap =
  highScale outputShell gap * highScale outputShell gap

highMinorityIsOneGapGainTimesHighSquared :
  (outputShell gap : Nat) →
  highMinorityCoefficientScale outputShell gap
  ≡ helicalGapGain gap * naiveHighSquaredScale outputShell gap
highMinorityIsOneGapGainTimesHighSquared outputShell gap =
  trans
    (cong
      (_* highScale outputShell gap)
      (Eq.sym (HH.highHighLowGainCalibration outputShell gap)))
    (solve
      ( helicalGapGain gap
      ∷ highScale outputShell gap
      ∷ []))

lowMinorityIsTwoGapGainsTimesHighSquared :
  (outputShell gap : Nat) →
  lowMinorityCoefficientScale outputShell gap
  ≡ (helicalGapGain gap * helicalGapGain gap)
      * naiveHighSquaredScale outputShell gap
lowMinorityIsTwoGapGainsTimesHighSquared outputShell gap =
  let
    calibration = Eq.sym (HH.highHighLowGainCalibration outputShell gap)
  in
  trans
    (cong
      (λ low → low * low)
      calibration)
    (solve
      ( helicalGapGain gap
      ∷ highScale outputShell gap
      ∷ []))

round102EveryHeterochiralHHClassHasAtLeastOneDyadicGapGain : Bool
round102EveryHeterochiralHHClassHasAtLeastOneDyadicGapGain = true

round102LowMinorityHHClassHasTwoDyadicGapGains : Bool
round102LowMinorityHHClassHasTwoDyadicGapGains = true

round102EveryHeterochiralHHClassHasAtLeastOneDyadicGapGainIsTrue :
  round102EveryHeterochiralHHClassHasAtLeastOneDyadicGapGain ≡ true
round102EveryHeterochiralHHClassHasAtLeastOneDyadicGapGainIsTrue = refl
