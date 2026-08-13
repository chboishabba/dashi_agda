module DASHI.Physics.Closure.NSTriadKNHHBadRawCapacityToOwnerRound53Exact where

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
-- Eliminate the final adapter gap between the Round-53 literal Duhamel
-- variable-capacity theorem and Round-52's mature HH-bad owner.  A physical
-- capacity M_q with M_q <= C_* is already exactly a UniformShellBarrier for the
-- normalized defect recurrence, even when alpha_q > 1 transiently.
--
-- Thus the physical HH-bad owner consumes directly:
--
--   literal Duhamel component transfers,
--   raw variable capacity,
--   uniform ceiling,
--   literal gain <= normalized defect profile,
--   unmasked shell charge <= physical dissipation.
--
-- There is no additional recurrence or contraction layer between these facts
-- and eta_HHb = 2 C_*.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadRawVariableCapacityRound53Exact as Raw
import DASHI.Physics.Closure.NSTriadKNHHBadBarrierToOwnerRound52Exact as ToOwner
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedChargeSubchargeRound44Exact as Subcharge
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadNormalizedProfileRound45Exact as Profile
import DASHI.Physics.Closure.NSTriadKNHHBadSingleThresholdSufficesRound47Exact as Selected
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp

record UniformRawVariableCapacity
    (physical : Raw.PhysicalGeneralVariableDefectDuhamel) : Set where
  field
    capacityData : Raw.RawVariableCapacity physical
    ceiling : ℚ
    ceilingNonnegative : 0ℚ ≤ ceiling
    capacityBelowCeiling : ∀ q →
      Raw.capacity capacityData q ≤ ceiling

open UniformRawVariableCapacity public

rawCapacityAsUniformShellBarrier :
  ∀ {physical} →
  UniformRawVariableCapacity physical →
  ToOwner.UniformShellBarrier (Raw.asGeneralBarrierRecurrence physical)
rawCapacityAsUniformShellBarrier uniform = record
  { supersolution = Raw.rawVariableCapacityAsShellSupersolution
      (capacityData uniform)
  ; ceiling = ceiling uniform
  ; ceilingNonnegative = ceilingNonnegative uniform
  ; everyBarrierBelowCeiling = capacityBelowCeiling uniform
  }

record PhysicalRawCapacityHHBadOwnerInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ)
    (physical : Raw.PhysicalGeneralVariableDefectDuhamel) : Set where
  field
    uniformCapacity : UniformRawVariableCapacity physical
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
                  (rawCapacityAsUniformShellBarrier uniformCapacity)))
              shell)))
      ≤ Owner.dissipation environment

open PhysicalRawCapacityHHBadOwnerInput public

asRound52PhysicalBarrierOwnerInput :
  ∀ {environment effectiveViscosity physical} →
  PhysicalRawCapacityHHBadOwnerInput environment effectiveViscosity physical →
  ToOwner.PhysicalBarrierHHBadOwnerInput
    environment effectiveViscosity (Raw.asGeneralBarrierRecurrence physical)
asRound52PhysicalBarrierOwnerInput input = record
  { bridge = literalGainBridge input
  ; uniformBarrier = rawCapacityAsUniformShellBarrier (uniformCapacity input)
  ; viscosityNonnegative = viscosityNonnegative input
  ; unmaskedChargeBelowPhysicalDissipation =
      unmaskedChargeBelowPhysicalDissipation input
  }

physicalHHBadOwnerFromRawVariableCapacity :
  ∀ {environment effectiveViscosity physical} →
  PhysicalRawCapacityHHBadOwnerInput environment effectiveViscosity physical →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalHHBadOwnerFromRawVariableCapacity input =
  ToOwner.physicalHHBadOwnerFromBarrier
    (asRound52PhysicalBarrierOwnerInput input)

physicalRawCapacityOwnerEtaExact :
  ∀ {environment effectiveViscosity physical}
    (input : PhysicalRawCapacityHHBadOwnerInput
      environment effectiveViscosity physical) →
  ∀ shell →
  Owner.eta (physicalHHBadOwnerFromRawVariableCapacity input shell)
  ≡ Sharp.two * ceiling (uniformCapacity input)
physicalRawCapacityOwnerEtaExact input shell =
  ToOwner.physicalBarrierOwnerEtaExact
    (asRound52PhysicalBarrierOwnerInput input)
    shell

rawVariableCapacityFeedsHHBadOwnerDirectly : Bool
rawVariableCapacityFeedsHHBadOwnerDirectly = true

rawVariableCapacityFeedsHHBadOwnerDirectlyIsTrue :
  rawVariableCapacityFeedsHHBadOwnerDirectly ≡ true
rawVariableCapacityFeedsHHBadOwnerDirectlyIsTrue = refl
