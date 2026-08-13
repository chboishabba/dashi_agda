module DASHI.Physics.Closure.NSTriadKNGlobalGateIffRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
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
-- Round 51 proved only the forward-use direction needed by the owner.  Here we
-- record the exact biconditional for all three global soft floors.  Thus the
-- famous 15/32 number is neither heuristic nor merely sufficient at this scalar
-- gate: it is exactly the zero-soft-floor endpoint of
--
--   2 C_* + tau_Com^g + tau_kernel^g + tau_HHg^g + 1/16 < 1
--
-- iff
--
--   C_* < 15/32 - (tau_Com^g + tau_kernel^g + tau_HHg^g)/2.
--
-- This theorem does NOT assert that the fixed-shift recursion permits the soft
-- floors to be zero; that remains a physical coefficient-identification issue.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _<_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNGlobalEffectiveSoftFloorGateRound51Exact as Global
import DASHI.Physics.Closure.NSTriadKNHHBadLiveBudgetTargetRound48Exact as Live
import DASHI.Physics.Closure.NSTriadKNHardGateHierarchyRound47Exact as Gate

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A

open _↔_ public
infix 2 _↔_

globalGateStrictIffLiveCeilingTarget :
  ∀ ceiling comGlobal kernelGlobal hhGoodGlobal →
  Global.globalEffectiveGate
      ceiling comGlobal kernelGlobal hhGoodGlobal
  ↔
  (ceiling <
    Global.globalAllowableHHBadCeiling
      comGlobal kernelGlobal hhGoodGlobal)
globalGateStrictIffLiveCeilingTarget
    ceiling comGlobal kernelGlobal hhGoodGlobal =
  let
    grouped = kernelGlobal + hhGoodGlobal

    toH2 :
      Global.globalEffectiveGate
        ceiling comGlobal kernelGlobal hhGoodGlobal →
      Gate.hardGateH2 ceiling comGlobal grouped < 1ℚ
    toH2 gate
      rewrite Global.globalEtaIsGroupedH2
        ceiling comGlobal kernelGlobal hhGoodGlobal = gate

    fromH2 :
      Gate.hardGateH2 ceiling comGlobal grouped < 1ℚ →
      Global.globalEffectiveGate
        ceiling comGlobal kernelGlobal hhGoodGlobal
    fromH2 h2
      rewrite Global.globalEtaIsGroupedH2
        ceiling comGlobal kernelGlobal hhGoodGlobal = h2

    h2Iff =
      Live.h2StrictIffLiveHHBadCeilingTarget
        ceiling comGlobal grouped
  in
  iff
    (λ gate → _↔_.forward h2Iff (toH2 gate))
    (λ target → fromH2 (_↔_.backward h2Iff target))

globalZeroSoftTargetIsFifteenThirtySeconds :
  Global.globalAllowableHHBadCeiling 0ℚ 0ℚ 0ℚ
  ≡ Live.fifteenThirtySeconds
globalZeroSoftTargetIsFifteenThirtySeconds = solve []

zeroSoftGlobalGateStrictIffFifteenThirtySeconds :
  ∀ ceiling →
  Global.globalEffectiveGate ceiling 0ℚ 0ℚ 0ℚ
  ↔ (ceiling < Live.fifteenThirtySeconds)
zeroSoftGlobalGateStrictIffFifteenThirtySeconds ceiling =
  subst
    (λ target →
      Global.globalEffectiveGate ceiling 0ℚ 0ℚ 0ℚ
      ↔ (ceiling < target))
    globalZeroSoftTargetIsFifteenThirtySeconds
    (globalGateStrictIffLiveCeilingTarget ceiling 0ℚ 0ℚ 0ℚ)

globalGateTargetIsExactNotMerelySufficient : Bool
globalGateTargetIsExactNotMerelySufficient = true

globalGateTargetIsExactNotMerelySufficientIsTrue :
  globalGateTargetIsExactNotMerelySufficient ≡ true
globalGateTargetIsExactNotMerelySufficientIsTrue = refl
