module DASHI.Physics.Closure.NSTriadKNHHBadDuhamelDefectReductionRound49Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- Interpret Round 48's inherited/generated/leakage split as the exact consumer
-- shape of a shell-localized Duhamel decomposition. Generic heat contraction
-- of vorticity is deliberately insufficient. The load-bearing physical theorem
-- is the contraction of the directional-defect functional itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNHHBadHeatSemigroupHalfRound48Exact as HeatHalf
import DASHI.Physics.Closure.NSTriadKNHHBadInheritedGeneratedLeakageRound48Exact as Three
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHeatDampingExact as Heat
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp

record PhysicalDirectionalDefectDuhamelInput : Set where
  field
    decomposition : Three.PhysicalSelectedThresholdDefectDecomposition

    physicalDirectionalDefectHeatContraction : ∀ q →
      Three.inherited decomposition q
      ≤ Three.alpha decomposition * Three.defectRate decomposition q
        * Heat.heatDamping (suc zero)

open PhysicalDirectionalDefectDuhamelInput public

inheritedHalfFromDirectionalDefectHeatContraction :
  (physical : PhysicalDirectionalDefectDuhamelInput) →
  ∀ q →
  Three.inherited (decomposition physical) q
  ≤ Three.alpha (decomposition physical)
    * Sharp.half
    * Three.defectRate (decomposition physical) q
inheritedHalfFromDirectionalDefectHeatContraction physical q =
  HeatHalf.oneHeatUnitInheritanceGivesRequiredHalf record
    { previousDefect = Three.defectRate (decomposition physical) q
    ; inheritedDefect = Three.inherited (decomposition physical) q
    ; alpha = Three.alpha (decomposition physical)
    ; inheritedFromOneHeatUnit = physicalDirectionalDefectHeatContraction physical q
    }

hhBadDuhamelConsumerShapeClosed : Bool
hhBadDuhamelConsumerShapeClosed = true

physicalDirectionalDefectHeatContractionConstructed : Bool
physicalDirectionalDefectHeatContractionConstructed = false

hhBadDuhamelConsumerShapeClosedIsTrue : hhBadDuhamelConsumerShapeClosed ≡ true
hhBadDuhamelConsumerShapeClosedIsTrue = refl

physicalDirectionalDefectHeatContractionConstructedIsFalse :
  physicalDirectionalDefectHeatContractionConstructed ≡ false
physicalDirectionalDefectHeatContractionConstructedIsFalse = refl
