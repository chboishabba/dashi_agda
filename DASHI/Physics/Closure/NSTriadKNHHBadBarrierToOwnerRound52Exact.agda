module DASHI.Physics.Closure.NSTriadKNHHBadBarrierToOwnerRound52Exact where

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
-- Make the Round-52 shell barrier, rather than any preferred recurrence
-- mechanism, the direct HH-bad producer consumed by the mature selected-
-- threshold owner.  The physical normalized gain only needs
--
--   2^q g_q <= C_q,
--
-- while a nonnegative supersolution M gives C_q <= M_q <= C_*.
-- The owner therefore has exact eta_HHb = 2 C_*.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedChargeSubchargeRound44Exact as Subcharge
import DASHI.Physics.Closure.NSTriadKNHHBadNormalizedProfileRound45Exact as Profile
import DASHI.Physics.Closure.NSTriadKNHHBadSingleThresholdSufficesRound47Exact as Selected
import DASHI.Physics.Closure.NSTriadKNHHBadShellBarrierRound52Exact as Barrier

record UniformShellBarrier
    (input : Barrier.GeneralHHBadRecurrence) : Set where
  field
    supersolution : Barrier.ShellSupersolution input
    ceiling : ℚ
    ceilingNonnegative : 0ℚ ≤ ceiling
    everyBarrierBelowCeiling : ∀ q →
      Barrier.barrier supersolution q ≤ ceiling

open UniformShellBarrier public

profileBelowUniformBarrierCeiling :
  ∀ {input}
    (uniform : UniformShellBarrier input) q →
  Barrier.profile input q ≤ ceiling uniform
profileBelowUniformBarrierCeiling {input} uniform q =
  ℚP.≤-trans
    (Barrier.profileBelowAnyShellBarrier input
      (supersolution uniform) q)
    (everyBarrierBelowCeiling uniform q)

record BarrierLiteralGainBridge
    (effectiveViscosity : ℚ)
    (input : Barrier.GeneralHHBadRecurrence) : Set where
  field
    selectedThreshold : Threshold.PositiveThreshold
    density : Nat → ℚ
    densityNonnegative : ∀ shell → 0ℚ ≤ density shell
    cells : ∀ shell →
      List (Gain.RestrictedGainDensityCell
        effectiveViscosity (density shell) shell)

    normalizedGainBelowDefectProfile : ∀ shell →
      Factor.scaleFreeDensityCoefficient (density shell) shell
      ≤ Barrier.profile input shell

open BarrierLiteralGainBridge public

barrierToSelectedProfile :
  ∀ {effectiveViscosity input} →
  (bridge : BarrierLiteralGainBridge effectiveViscosity input) →
  (uniform : UniformShellBarrier input) →
  Selected.SelectedThresholdHHBadNormalizedProfile effectiveViscosity
barrierToSelectedProfile bridge uniform = record
  { selectedThreshold = selectedThreshold bridge
  ; density = density bridge
  ; densityNonnegative = densityNonnegative bridge
  ; cells = cells bridge
  ; selectedProfileCeiling = ceiling uniform
  ; selectedProfileCeilingNonnegative = ceilingNonnegative uniform
  ; normalizedCoefficientBelowSelectedCeiling = λ shell →
      ℚP.≤-trans
        (normalizedGainBelowDefectProfile bridge shell)
        (profileBelowUniformBarrierCeiling uniform shell)
  }

record PhysicalBarrierHHBadOwnerInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ)
    (input : Barrier.GeneralHHBadRecurrence) : Set where
  field
    bridge : BarrierLiteralGainBridge effectiveViscosity input
    uniformBarrier : UniformShellBarrier input
    viscosityNonnegative : 0ℚ ≤ effectiveViscosity

    unmaskedChargeBelowPhysicalDissipation : ∀ shell →
      Subcharge.sumCellUnmaskedViscousCharge
        effectiveViscosity shell
        (Gain.cells
          (Factor.asRound39InverseShellCertificate
            (Profile.canonicalOneDerivativeDensityAtShell
              (Selected.selectedThresholdToRound45Profile
                (barrierToSelectedProfile bridge uniformBarrier))
              shell)))
      ≤ Owner.dissipation environment

open PhysicalBarrierHHBadOwnerInput public

asPhysicalSelectedThresholdProfile :
  ∀ {environment effectiveViscosity input} →
  PhysicalBarrierHHBadOwnerInput environment effectiveViscosity input →
  Selected.PhysicalSelectedThresholdHHBadOwnerProfile
    environment effectiveViscosity
asPhysicalSelectedThresholdProfile physical = record
  { selectedProfile =
      barrierToSelectedProfile
        (bridge physical)
        (uniformBarrier physical)
  ; viscosityNonnegative = viscosityNonnegative physical
  ; selectedUnmaskedChargeBelowPhysicalDissipation =
      unmaskedChargeBelowPhysicalDissipation physical
  }

physicalHHBadOwnerFromBarrier :
  ∀ {environment effectiveViscosity input} →
  PhysicalBarrierHHBadOwnerInput environment effectiveViscosity input →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalHHBadOwnerFromBarrier physical =
  Selected.physicalHHBadOwnerFromOneSelectedThreshold
    (asPhysicalSelectedThresholdProfile physical)

physicalBarrierOwnerEtaExact :
  ∀ {environment effectiveViscosity input}
    (physical : PhysicalBarrierHHBadOwnerInput
      environment effectiveViscosity input) →
  ∀ shell →
  Owner.eta (physicalHHBadOwnerFromBarrier physical shell)
  ≡ Sharp.two * ceiling (uniformBarrier physical)
physicalBarrierOwnerEtaExact physical shell =
  Profile.physicalHHBadOwnerEtaIsTwiceProfileCeiling
    (Selected.selectedThresholdToPhysicalRound45Profile
      (asPhysicalSelectedThresholdProfile physical))
    shell

shellBarrierFeedsMatureHHBadOwner : Bool
shellBarrierFeedsMatureHHBadOwner = true

physicalShellBarrierConstructed : Bool
physicalShellBarrierConstructed = false

shellBarrierFeedsMatureHHBadOwnerIsTrue :
  shellBarrierFeedsMatureHHBadOwner ≡ true
shellBarrierFeedsMatureHHBadOwnerIsTrue = refl
