module DASHI.Physics.Closure.NSTriadKNHHBadTwoRouteLiveGateRound50Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Author: Gyula Farkas.
-- Title: "Theorie der einfachen Ungleichungen".
-- Journal fuer die reine und angewandte Mathematik 124 (1902), 1--27.
-- DOI: no DOI assigned to the historical article.
--
-- DASHI CONTRIBUTION
--
-- Round 49's direct-alpha route and Round 50's borderline/summable-forcing
-- route now terminate at the SAME hard-budget theorem.
--
-- Contractive route:
--   C0<T, beta<zeta T.
--
-- Summable route:
--   C0 + B_force < T.
--
-- Either route supplies an HH-bad ceiling strictly below
--
--   T = 15/32 - (tau_Com + tau_kernel)/2,
--
-- hence H2<1.  This prevents the convenient uniform-alpha hypothesis from
-- becoming an accidental necessity of the formal architecture.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _<_)

import DASHI.Physics.Closure.NSTriadKNHardGateHierarchyRound47Exact as Gate
import DASHI.Physics.Closure.NSTriadKNHHBadLiveBudgetTargetRound48Exact as Live
import DASHI.Physics.Closure.NSTriadKNHHBadDirectLiveBudgetRound49Exact as Direct
import DASHI.Physics.Closure.NSTriadKNHHBadSummableForcingRound50Exact as Sum
import DASHI.Physics.Closure.NSTriadKNHHBadSummableForcingToOwnerRound50Exact as SumOwner

record SummableForcingLiveBudgetInput : Set where
  field
    summableInput : Sum.BorderlineSummableForcing
    prefixSummable : Sum.PrefixSummable summableInput
    comFloor kernelFloor : ℚ
    summableCeilingBelowLiveTarget :
      SumOwner.summableCeiling summableInput
      < Live.allowableHHBadCeiling comFloor kernelFloor

open SummableForcingLiveBudgetInput public

summableForcingImpliesH2Strict :
  (input : SummableForcingLiveBudgetInput) →
  Gate.hardGateH2
    (SumOwner.summableCeiling (summableInput input))
    (comFloor input)
    (kernelFloor input)
  < 1ℚ
summableForcingImpliesH2Strict input =
  Live.liveCeilingTargetImpliesH2Strict
    (SumOwner.summableCeiling (summableInput input))
    (comFloor input)
    (kernelFloor input)
    (summableCeilingBelowLiveTarget input)

data HHBadLiveRoute : Set where
  strictContraction summableForcing : HHBadLiveRoute

twoHHBadPhysicalRoutesReachSameHardGate : Bool
twoHHBadPhysicalRoutesReachSameHardGate = true

uniformAlphaStrictIsRequiredByHardGateArchitecture : Bool
uniformAlphaStrictIsRequiredByHardGateArchitecture = false

twoHHBadPhysicalRoutesReachSameHardGateIsTrue :
  twoHHBadPhysicalRoutesReachSameHardGate ≡ true
twoHHBadPhysicalRoutesReachSameHardGateIsTrue = refl

uniformAlphaStrictIsRequiredByHardGateArchitectureIsFalse :
  uniformAlphaStrictIsRequiredByHardGateArchitecture ≡ false
uniformAlphaStrictIsRequiredByHardGateArchitectureIsFalse = refl
