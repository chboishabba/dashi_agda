module DASHI.Physics.Closure.NSTriadKNGlobalEffectiveSoftFloorGateRound51Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- DOI: 10.1098/rspa.1912.0086.
--
-- Author: Gyula Farkas.
-- Title: "Theorie der einfachen Ungleichungen".
-- Journal fuer die reine und angewandte Mathematik 124 (1902), 1--27.
-- DOI: no DOI assigned to the historical article.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Local Young-softness proves that an owner estimate itself has no positive
-- viscosity floor.  A later fixed-shift/block-recursion compatibility theorem
-- may nevertheless impose a minimum usable split.  Round 51 therefore records
-- the post-continuation scalar gate in terms of GLOBAL effective floors:
--
--   2 C_* + tau_Com^g + tau_kernel^g + tau_HHg^g + 1/16 < 1.
--
-- The corresponding live HH-bad target is exactly the existing allowable
-- ceiling with `tau_kernel + tau_HHg` grouped as the second surviving floor:
--
--   T_global = 15/32
--            - (tau_Com^g + tau_kernel^g + tau_HHg^g)/2.
--
-- A ceiling below T_global therefore implies the global strict gate.  Setting
-- all three global soft floors to zero recovers 2 C_* + 1/16 < 1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _<_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalFourClassClosureExact as Critical
import DASHI.Physics.Closure.NSTriadKNHardGateHierarchyRound47Exact as Gate
import DASHI.Physics.Closure.NSTriadKNHHBadLiveBudgetTargetRound48Exact as Live

globalEffectiveEtaTotal : ℚ → ℚ → ℚ → ℚ → ℚ
globalEffectiveEtaTotal hhBadCeiling comGlobal kernelGlobal hhGoodGlobal =
  Sharp.two * hhBadCeiling
  + comGlobal
  + kernelGlobal
  + hhGoodGlobal
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth

globalEffectiveGate : ℚ → ℚ → ℚ → ℚ → Set
globalEffectiveGate hhBadCeiling comGlobal kernelGlobal hhGoodGlobal =
  globalEffectiveEtaTotal
    hhBadCeiling comGlobal kernelGlobal hhGoodGlobal < 1ℚ

globalAllowableHHBadCeiling : ℚ → ℚ → ℚ → ℚ
globalAllowableHHBadCeiling comGlobal kernelGlobal hhGoodGlobal =
  Live.allowableHHBadCeiling
    comGlobal (kernelGlobal + hhGoodGlobal)

globalEtaIsGroupedH2 :
  ∀ ceiling comGlobal kernelGlobal hhGoodGlobal →
  globalEffectiveEtaTotal ceiling comGlobal kernelGlobal hhGoodGlobal
  ≡ Gate.hardGateH2 ceiling comGlobal (kernelGlobal + hhGoodGlobal)
globalEtaIsGroupedH2 ceiling comGlobal kernelGlobal hhGoodGlobal =
  solve
    ( ceiling
    ∷ comGlobal
    ∷ kernelGlobal
    ∷ hhGoodGlobal
    ∷ Critical.oneSixtyFourth
    ∷ [])

globalCeilingBelowTargetImpliesGate :
  ∀ ceiling comGlobal kernelGlobal hhGoodGlobal →
  ceiling < globalAllowableHHBadCeiling comGlobal kernelGlobal hhGoodGlobal →
  globalEffectiveGate ceiling comGlobal kernelGlobal hhGoodGlobal
globalCeilingBelowTargetImpliesGate
    ceiling comGlobal kernelGlobal hhGoodGlobal below =
  subst
    (_< 1ℚ)
    (sym (globalEtaIsGroupedH2
      ceiling comGlobal kernelGlobal hhGoodGlobal))
    (Live.liveCeilingTargetImpliesH2Strict
      ceiling comGlobal (kernelGlobal + hhGoodGlobal) below)

globalGateWithZeroHHGoodEqualsH2 :
  ∀ ceiling comFloor kernelFloor →
  globalEffectiveEtaTotal ceiling comFloor kernelFloor 0ℚ
  ≡ Gate.hardGateH2 ceiling comFloor kernelFloor
globalGateWithZeroHHGoodEqualsH2 ceiling comFloor kernelFloor =
  solve
    ( ceiling
    ∷ comFloor
    ∷ kernelFloor
    ∷ Critical.oneSixtyFourth
    ∷ [])

allGlobalSoftFloorsZeroRecoversH0 :
  ∀ ceiling →
  globalEffectiveEtaTotal ceiling 0ℚ 0ℚ 0ℚ
  ≡ Gate.hardGateH0 ceiling
allGlobalSoftFloorsZeroRecoversH0 ceiling =
  solve (ceiling ∷ Critical.oneSixtyFourth ∷ [])

localSoftnessAndGlobalFloorAreDistinct : Bool
localSoftnessAndGlobalFloorAreDistinct = true

postRecursionGateMustUseGlobalEffectiveFloors : Bool
postRecursionGateMustUseGlobalEffectiveFloors = true

localSoftnessAndGlobalFloorAreDistinctIsTrue :
  localSoftnessAndGlobalFloorAreDistinct ≡ true
localSoftnessAndGlobalFloorAreDistinctIsTrue = refl

postRecursionGateMustUseGlobalEffectiveFloorsIsTrue :
  postRecursionGateMustUseGlobalEffectiveFloors ≡ true
postRecursionGateMustUseGlobalEffectiveFloorsIsTrue = refl
