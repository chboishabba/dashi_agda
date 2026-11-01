module DASHI.Physics.Closure.NSTriadKNHHBadMinimalCapacityToOwnerRound54Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Make the canonical least capacity from Round 54 the final HH-bad producer
-- surface.  The owner no longer needs an arbitrary user-chosen M_q.  It needs
-- only a uniform bound on the explicitly generated minimal sequence together
-- with the two literal same-object inequalities:
--
--   normalized bad gain <= normalized defect profile,
--   unmasked bad viscous charge <= physical dissipation.
--
-- The resulting owner has eta_HHb = 2 C_* exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadRawVariableCapacityRound53Exact as Raw
import DASHI.Physics.Closure.NSTriadKNHHBadRawCapacityToOwnerRound53Exact as Round53
import DASHI.Physics.Closure.NSTriadKNHHBadMinimalCapacityRound54Exact as Minimal
import DASHI.Physics.Closure.NSTriadKNHHBadBarrierToOwnerRound52Exact as ToOwner
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedChargeSubchargeRound44Exact as Subcharge
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadNormalizedProfileRound45Exact as Profile
import DASHI.Physics.Closure.NSTriadKNHHBadSingleThresholdSufficesRound47Exact as Selected
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp

record PhysicalMinimalCapacityHHBadOwnerInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ)
    (physical : Raw.PhysicalGeneralVariableDefectDuhamel) : Set where
  field
    uniformMinimalCapacity : Minimal.UniformMinimalCapacity physical

    literalGainBridge :
      ToOwner.BarrierLiteralGainBridge
        effectiveViscosity
        (Raw.asGeneralBarrierRecurrence physical)

    viscosityNonnegative : 0ℚ ≤ effectiveViscosity

    unmaskedChargeBelowPhysicalDissipation : ∀ shell →
      Subcharge.sumCellUnmaskedViscousCharge
        effectiveViscosity shell
        (Gain.cells
          (Factor.asRound39InverseShellCertificate
            (Profile.canonicalOneDerivativeDensityAtShell
              (Selected.selectedThresholdToRound45Profile
                (ToOwner.barrierToSelectedProfile
                  literalGainBridge
                  (Round53.rawCapacityAsUniformShellBarrier
                    (Minimal.uniformMinimalToUniformRawCapacity
                      uniformMinimalCapacity))))
              shell)))
      ≤ Owner.dissipation environment

open PhysicalMinimalCapacityHHBadOwnerInput public

asRound53RawCapacityOwnerInput :
  ∀ {environment effectiveViscosity physical} →
  PhysicalMinimalCapacityHHBadOwnerInput
    environment effectiveViscosity physical →
  Round53.PhysicalRawCapacityHHBadOwnerInput
    environment effectiveViscosity physical
asRound53RawCapacityOwnerInput input = record
  { uniformCapacity =
      Minimal.uniformMinimalToUniformRawCapacity
        (uniformMinimalCapacity input)
  ; literalGainBridge = literalGainBridge input
  ; viscosityNonnegative = viscosityNonnegative input
  ; unmaskedChargeBelowPhysicalDissipation =
      unmaskedChargeBelowPhysicalDissipation input
  }

physicalHHBadOwnerFromMinimalCapacity :
  ∀ {environment effectiveViscosity physical} →
  PhysicalMinimalCapacityHHBadOwnerInput
    environment effectiveViscosity physical →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalHHBadOwnerFromMinimalCapacity input =
  Round53.physicalHHBadOwnerFromRawVariableCapacity
    (asRound53RawCapacityOwnerInput input)

physicalMinimalCapacityOwnerEtaExact :
  ∀ {environment effectiveViscosity physical}
    (input : PhysicalMinimalCapacityHHBadOwnerInput
      environment effectiveViscosity physical) →
  ∀ shell →
  Owner.eta (physicalHHBadOwnerFromMinimalCapacity input shell)
  ≡ Sharp.two * Minimal.ceiling (uniformMinimalCapacity input)
physicalMinimalCapacityOwnerEtaExact input shell =
  Round53.physicalRawCapacityOwnerEtaExact
    (asRound53RawCapacityOwnerInput input)
    shell

canonicalMinimalCapacityIsClayFacingHHBadProducer : Bool
canonicalMinimalCapacityIsClayFacingHHBadProducer = true

canonicalMinimalCapacityIsClayFacingHHBadProducerIsTrue :
  canonicalMinimalCapacityIsClayFacingHHBadProducer ≡ true
canonicalMinimalCapacityIsClayFacingHHBadProducerIsTrue = refl
