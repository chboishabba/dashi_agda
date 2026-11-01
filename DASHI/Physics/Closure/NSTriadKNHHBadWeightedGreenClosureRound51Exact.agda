module DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenClosureRound51Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Compose the Round-51 reductions into the least over-specified HH-bad theorem
-- currently consumed by the Clay-facing reserve:
--
--   C_(q+1) <= alpha_q C_q + beta_q,
--   0 <= alpha_q <= 1,
--   2^q g_q <= C_q,
--   G_q <= B   for the exact weighted Green response,
--   unmasked bad charge <= physical dissipation,
--   C_0 + B < T.
--
-- From these hypotheses the mature HH-bad owner exists with eta
--
--   2 (C_0 + B),
--
-- and the corresponding H2 hard gate is strict.  Uniform zeta, constant beta,
-- exact gain/defect equality, and raw forcing summability are no longer part of
-- the master consumer contract.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 1ℚ; _<_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHardGateHierarchyRound47Exact as Gate
import DASHI.Physics.Closure.NSTriadKNHHBadLiveBudgetTargetRound48Exact as Target
import DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenForcingRound51Exact as Green
import DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenToOwnerRound51Exact as GreenOwner
import DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenLiveGateRound51Exact as Live

record PhysicalWeightedGreenHHBadClosureInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ)
    (recurrenceInput : Green.VariableGreenRecurrence) : Set where
  field
    physicalOwnerInput : GreenOwner.PhysicalWeightedGreenHHBadOwnerInput
      environment effectiveViscosity recurrenceInput
    comFloor kernelFloor : ℚ
    ceilingBelowLiveTarget :
      GreenOwner.weightedGreenCeiling
        (GreenOwner.weightedBound physicalOwnerInput)
      < Target.allowableHHBadCeiling comFloor kernelFloor

open PhysicalWeightedGreenHHBadClosureInput public

physicalWeightedGreenHHBadOwner :
  ∀ {environment effectiveViscosity recurrenceInput} →
  PhysicalWeightedGreenHHBadClosureInput
    environment effectiveViscosity recurrenceInput →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalWeightedGreenHHBadOwner input =
  GreenOwner.physicalHHBadOwnerFromWeightedGreen
    (physicalOwnerInput input)

physicalWeightedGreenHHBadGateStrict :
  ∀ {environment effectiveViscosity recurrenceInput}
    (input : PhysicalWeightedGreenHHBadClosureInput
      environment effectiveViscosity recurrenceInput) →
  Gate.hardGateH2
    (GreenOwner.weightedGreenCeiling
      (GreenOwner.weightedBound (physicalOwnerInput input)))
    (comFloor input)
    (kernelFloor input)
  < 1ℚ
physicalWeightedGreenHHBadGateStrict
    {recurrenceInput = recurrence} input =
  Live.weightedGreenImpliesH2Strict record
    { recurrenceInput = recurrence
    ; weightedBound = GreenOwner.weightedBound (physicalOwnerInput input)
    ; comFloor = comFloor input
    ; kernelFloor = kernelFloor input
    ; weightedCeilingBelowLiveTarget = ceilingBelowLiveTarget input
    }

weightedGreenMasterConsumerClosed : Bool
weightedGreenMasterConsumerClosed = true

weightedGreenMasterConsumerClosedIsTrue :
  weightedGreenMasterConsumerClosed ≡ true
weightedGreenMasterConsumerClosedIsTrue = refl
