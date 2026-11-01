module DASHI.Physics.Closure.NSTriadKNHHBadBarrierLiveGateRound52Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Once a physical shell barrier gives a uniform HH-bad ceiling C_*, the
-- recurrence mechanism disappears from the Clay-facing gate.  The only scalar
-- requirement is
--
--   C_* < 15/32
--          - (tau_Com^g + tau_kernel^g + tau_HHg^g)/2.
--
-- This module sends that exact ceiling to the Round-51 global effective gate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _<_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadShellBarrierRound52Exact as Barrier
import DASHI.Physics.Closure.NSTriadKNHHBadBarrierToOwnerRound52Exact as BarrierOwner
import DASHI.Physics.Closure.NSTriadKNGlobalEffectiveSoftFloorGateRound51Exact as Global

record PhysicalBarrierLiveGateInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ)
    (input : Barrier.GeneralHHBadRecurrence) : Set where
  field
    physicalOwnerInput :
      BarrierOwner.PhysicalBarrierHHBadOwnerInput
        environment effectiveViscosity input

    comGlobalFloor kernelGlobalFloor hhGoodGlobalFloor : ℚ

    ceilingBelowGlobalLiveTarget :
      BarrierOwner.ceiling
        (BarrierOwner.uniformBarrier physicalOwnerInput)
      < Global.globalAllowableHHBadCeiling
          comGlobalFloor kernelGlobalFloor hhGoodGlobalFloor

open PhysicalBarrierLiveGateInput public

physicalBarrierGlobalGateStrict :
  ∀ {environment effectiveViscosity input}
    (physical : PhysicalBarrierLiveGateInput
      environment effectiveViscosity input) →
  Global.globalEffectiveGate
    (BarrierOwner.ceiling
      (BarrierOwner.uniformBarrier (physicalOwnerInput physical)))
    (comGlobalFloor physical)
    (kernelGlobalFloor physical)
    (hhGoodGlobalFloor physical)
physicalBarrierGlobalGateStrict physical =
  Global.globalCeilingBelowTargetImpliesGate
    (BarrierOwner.ceiling
      (BarrierOwner.uniformBarrier (physicalOwnerInput physical)))
    (comGlobalFloor physical)
    (kernelGlobalFloor physical)
    (hhGoodGlobalFloor physical)
    (ceilingBelowGlobalLiveTarget physical)

barrierIsDirectGlobalHHBadGateConsumer : Bool
barrierIsDirectGlobalHHBadGateConsumer = true

barrierIsDirectGlobalHHBadGateConsumerIsTrue :
  barrierIsDirectGlobalHHBadGateConsumer ≡ true
barrierIsDirectGlobalHHBadGateConsumerIsTrue = refl
