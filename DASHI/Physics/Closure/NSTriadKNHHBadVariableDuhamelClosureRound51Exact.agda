module DASHI.Physics.Closure.NSTriadKNHHBadVariableDuhamelClosureRound51Exact where

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
-- The shortest HH-bad path now begins at the shell-localized physical Duhamel
-- pieces themselves.  Given one `PhysicalVariableDefectDuhamel`, a cutoff-
-- uniform weighted Green bound for the normalized recurrence, literal gain
-- domination by that profile, and the existing charge domination, construct the
-- mature HH-bad owner and strict live H2 gate.  No intermediate uniform-alpha
-- or raw-summability theorem is required.
--
-- The owner and gate are forced to use the SAME weighted ceiling, so a caller
-- cannot prove the live inequality with one Green budget while taxing a larger
-- or unrelated one.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_; _<_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHardGateHierarchyRound47Exact as Gate
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadLiveBudgetTargetRound48Exact as Target
import DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenForcingRound51Exact as Green
import DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenToOwnerRound51Exact as GreenOwner
import DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenLiveGateRound51Exact as Live
import DASHI.Physics.Closure.NSTriadKNHHBadVariableDuhamelToWeightedGreenRound51Exact as Duhamel

record PhysicalVariableDuhamelClosureInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ) : Set where
  field
    physicalDuhamel : Duhamel.PhysicalVariableDefectDuhamel
    weightedBound : Green.UniformWeightedGreenBound
      (Duhamel.asWeightedGreenRecurrence physicalDuhamel)

    physicalOwnerInput : GreenOwner.PhysicalWeightedGreenHHBadOwnerInput
      environment effectiveViscosity
      (Duhamel.asWeightedGreenRecurrence physicalDuhamel)

    ownerUsesSameWeightedBound :
      GreenOwner.weightedBound physicalOwnerInput ≡ weightedBound

    comFloor kernelFloor : ℚ
    ceilingBelowLiveTarget :
      GreenOwner.weightedGreenCeiling weightedBound
      < Target.allowableHHBadCeiling comFloor kernelFloor

open PhysicalVariableDuhamelClosureInput public

physicalVariableDuhamelHHBadOwner :
  ∀ {environment effectiveViscosity} →
  PhysicalVariableDuhamelClosureInput environment effectiveViscosity →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalVariableDuhamelHHBadOwner input =
  GreenOwner.physicalHHBadOwnerFromWeightedGreen
    (physicalOwnerInput input)

physicalVariableDuhamelHHBadEtaUsesLiveCeiling :
  ∀ {environment effectiveViscosity}
    (input : PhysicalVariableDuhamelClosureInput
      environment effectiveViscosity) shell →
  Owner.eta (physicalVariableDuhamelHHBadOwner input shell)
  ≡ Sharp.two * GreenOwner.weightedGreenCeiling (weightedBound input)
physicalVariableDuhamelHHBadEtaUsesLiveCeiling input shell =
  trans
    (GreenOwner.physicalHHBadWeightedGreenOwnerEtaExact
      (physicalOwnerInput input) shell)
    (cong (Sharp.two *_)
      (cong GreenOwner.weightedGreenCeiling
        (ownerUsesSameWeightedBound input)))

physicalVariableDuhamelGateStrict :
  ∀ {environment effectiveViscosity}
    (input : PhysicalVariableDuhamelClosureInput
      environment effectiveViscosity) →
  Gate.hardGateH2
    (GreenOwner.weightedGreenCeiling (weightedBound input))
    (comFloor input)
    (kernelFloor input)
  < 1ℚ
physicalVariableDuhamelGateStrict input =
  Live.weightedGreenImpliesH2Strict record
    { recurrenceInput = Duhamel.asWeightedGreenRecurrence
        (physicalDuhamel input)
    ; weightedBound = weightedBound input
    ; comFloor = comFloor input
    ; kernelFloor = kernelFloor input
    ; weightedCeilingBelowLiveTarget = ceilingBelowLiveTarget input
    }

variableDuhamelIsDirectClayFacingHHBadInput : Bool
variableDuhamelIsDirectClayFacingHHBadInput = true

variableDuhamelIsDirectClayFacingHHBadInputIsTrue :
  variableDuhamelIsDirectClayFacingHHBadInput ≡ true
variableDuhamelIsDirectClayFacingHHBadInputIsTrue = refl
