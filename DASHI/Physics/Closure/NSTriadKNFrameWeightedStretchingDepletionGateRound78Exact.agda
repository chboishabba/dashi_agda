module DASHI.Physics.Closure.NSTriadKNFrameWeightedStretchingDepletionGateRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Thomas Y. Hou; Ruo Li.
-- Title: "Dynamic Depletion of Vortex Stretching and Non-Blowup of the 3-D
-- Incompressible Euler Equations".
-- DOI: 10.1007/s00332-006-0800-3.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- ROUND78 / B2 NECESSARY SURPLUS GATE
--
-- Round77's exact physical threshold is frame weighted:
--
--   sum_i rho_i r_i^2 = rho_parent + epsilon, epsilon > 0.
--
-- Round78 now asks where epsilon can physically come from.  If a selected row
-- admits a source-native decomposition
--
--   epsilon = crossModeEnable - depletionCost,
--
-- then strict supercriticality forces the enabling side to beat depletion.
-- In particular, any Constantin--Fefferman/Hou-style coherent-depletion theorem
-- strong enough to establish
--
--   crossModeEnable <= depletionCost
--
-- on the SAME selected event immediately kills B2 there.
--
-- Conversely the theorem does not manufacture positive excess from Waleffe,
-- restricted Euler, DNS, or an alignment label.  The outstanding PDE producer
-- is now the exact same-carrier decomposition and a strict cross-mode/nonlocal
-- surplus on the events chosen by the critical propagation construction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; -_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNFrameWeightedSupercriticalPropagationRound77Exact as Propagation

record PhysicalExcessDecomposition
    (row : Propagation.FrameWeightedSupercriticalRow) : Set where
  field
    crossModeNonlocalEnable : ℚ
    pressureGeometryAndAllocationDepletion : ℚ
    enableNonnegative : 0ℚ ≤ crossModeNonlocalEnable
    depletionNonnegative : 0ℚ ≤ pressureGeometryAndAllocationDepletion
    excessMeaning :
      Propagation.excess row
      ≡ crossModeNonlocalEnable - pressureGeometryAndAllocationDepletion

open PhysicalExcessDecomposition public

differenceNonpositiveFromDominance :
  ∀ enabling depleting →
  enabling ≤ depleting →
  enabling - depleting ≤ 0ℚ
differenceNonpositiveFromDominance enabling depleting dominance =
  let
    shifted :
      enabling + (- depleting) ≤ depleting + (- depleting)
    shifted = ℚP.+-monoʳ-≤ (- depleting) dominance
    rightZero : depleting + (- depleting) ≡ 0ℚ
    rightZero = solve (depleting ∷ [])
  in
  subst (λ right → enabling - depleting ≤ right) rightZero shifted

physicalSupercriticalRowRefutesDepletionDominance :
  ∀ {row} (decomposition : PhysicalExcessDecomposition row) →
  crossModeNonlocalEnable decomposition
    ≤ pressureGeometryAndAllocationDepletion decomposition →
  0ℚ < 0ℚ
physicalSupercriticalRowRefutesDepletionDominance {row} decomposition dominance =
  let
    surplusPositive :
      0ℚ < crossModeNonlocalEnable decomposition
        - pressureGeometryAndAllocationDepletion decomposition
    surplusPositive =
      subst
        (0ℚ <_)
        (excessMeaning decomposition)
        (Propagation.excessPositive row)

    surplusNonpositive :
      crossModeNonlocalEnable decomposition
        - pressureGeometryAndAllocationDepletion decomposition
      ≤ 0ℚ
    surplusNonpositive =
      differenceNonpositiveFromDominance
        (crossModeNonlocalEnable decomposition)
        (pressureGeometryAndAllocationDepletion decomposition)
        dominance
  in
  ℚP.<-≤-trans surplusPositive surplusNonpositive

round78B2CanBeObtainedFromBranchingMultiplicityAlone : Bool
round78B2CanBeObtainedFromBranchingMultiplicityAlone = false

round78B2CanBeObtainedFromSameModeSelfStretching : Bool
round78B2CanBeObtainedFromSameModeSelfStretching = false

round78B2RequiresCrossModeNonlocalSurplusAfterDepletion : Bool
round78B2RequiresCrossModeNonlocalSurplusAfterDepletion = true

round78CFMCoherenceLabelAloneProvesB2Failure : Bool
round78CFMCoherenceLabelAloneProvesB2Failure = false

round78RestrictedEulerBlowupAloneProvesNSB2 : Bool
round78RestrictedEulerBlowupAloneProvesNSB2 = false

round78B2RequiresCrossModeNonlocalSurplusAfterDepletionIsTrue :
  round78B2RequiresCrossModeNonlocalSurplusAfterDepletion ≡ true
round78B2RequiresCrossModeNonlocalSurplusAfterDepletionIsTrue = refl
