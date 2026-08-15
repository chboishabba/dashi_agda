module DASHI.Physics.Closure.NSTriadKNHHBadPhysicalDuhamelSourceRound59 where

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
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 59/60 CONTRIBUTION
--
-- Bind HH-bad shell quantities to one time-dependent physical shell balance.
-- Round 60 removes the duplicated `transfer + source equality` boundary: once
-- analytic estimates are proved for THIS source, the complete physical transfer
-- record is constructed definitionally.  Thus A now has one fail-closed source
-- and one analytic witness, rather than two independently supplied objects.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_)

import DASHI.Physics.Closure.NSTriadKNGlobalBilinearShellPairingRound29Exact as Shell
import DASHI.Physics.Closure.NSTriadKNPhysicalTimeDependentShellBalanceRound30Exact as Time
import DASHI.Physics.Closure.NSTriadKNHHBadPhysicalTransferSurfaceRound58 as Transfer
import DASHI.Physics.Closure.NSTriadKNHHBadPositiveThresholdRound58 as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 as Scale

record PhysicalLocalizedDuhamelSource : Set₁ where
  field
    physicalShellData : Time.PhysicalTimeDependentShellBalance Nat
    shellAt : Nat → Nat

    -- Selectors act on the sampled balance belonging to ONE trajectory.
    defectSelector inheritedSelector generatedSelector leakageSelector :
      Shell.DynamicPhysicalShellBalance → ℚ

    parameter : Threshold.PositiveThreshold
    ceiling alpha beta : ℚ

    -- This is the literal PDE authority; it cannot be reconstructed from toy
    -- rational shell sequences.
    literalTrajectoryAuthority :
      Time.LiteralTrajectoryShellAuthority physicalShellData

open PhysicalLocalizedDuhamelSource public

defectAt : PhysicalLocalizedDuhamelSource → Nat → ℚ
defectAt source q =
  defectSelector source
    (Time.balanceAt (physicalShellData source) (shellAt source q))

inheritedAt : PhysicalLocalizedDuhamelSource → Nat → ℚ
inheritedAt source q =
  inheritedSelector source
    (Time.balanceAt (physicalShellData source) (shellAt source q))

generatedAt : PhysicalLocalizedDuhamelSource → Nat → ℚ
generatedAt source q =
  generatedSelector source
    (Time.balanceAt (physicalShellData source) (shellAt source q))

leakageAt : PhysicalLocalizedDuhamelSource → Nat → ℚ
leakageAt source q =
  leakageSelector source
    (Time.balanceAt (physicalShellData source) (shellAt source q))

asLocalizedSource :
  PhysicalLocalizedDuhamelSource → Transfer.LocalizedDuhamelSource
asLocalizedSource source = record
  { parameter = parameter source
  ; defectRate = defectAt source
  ; inheritedCoefficient = inheritedAt source
  ; generated = generatedAt source
  ; leakage = leakageAt source
  ; ceiling = ceiling source
  ; alpha = alpha source
  ; beta = beta source
  }

------------------------------------------------------------------------
-- The actual A analytic cutset on the canonical source.
--
-- No equality below can refer to a different shell sequence: every term is a
-- projection of the PhysicalLocalizedDuhamelSource supplied as the index.
------------------------------------------------------------------------

record PhysicalLocalizedDuhamelEstimates
    (source : PhysicalLocalizedDuhamelSource) : Set where
  field
    defectNonnegative : ∀ q → 0ℚ ≤ defectAt source q
    inheritedNonnegative : ∀ q → 0ℚ ≤ inheritedAt source q
    generatedNonnegative : ∀ q → 0ℚ ≤ generatedAt source q
    leakageNonnegative : ∀ q → 0ℚ ≤ leakageAt source q

    ceilingNonnegative : 0ℚ ≤ ceiling source
    alphaNonnegative : 0ℚ ≤ alpha source
    betaNonnegative : 0ℚ ≤ beta source
    alphaStrict : alpha source < 1ℚ

    baseLinearInSelectedThreshold :
      defectAt source zero
      ≤ Threshold.threshold (parameter source) * ceiling source

    inheritedTransfer : ∀ q →
      inheritedAt source (suc q)
      ≤ alpha source * inheritedAt source q

    successorDecomposition : ∀ q →
      defectAt source (suc q)
      ≡ Threshold.threshold (parameter source)
          * Scale.inverseDyadicScale (suc q)
          * inheritedAt source (suc q)
        + generatedAt source q + leakageAt source q

    generatedAndLeakageForcing : ∀ q →
      generatedAt source q + leakageAt source q
      ≤ Threshold.threshold (parameter source)
        * Scale.inverseDyadicScale (suc q) * beta source

    forcingFitsCeiling :
      beta source ≤ (1ℚ - alpha source) * ceiling source

open PhysicalLocalizedDuhamelEstimates public

physicalTransferFromSource :
  (source : PhysicalLocalizedDuhamelSource) →
  PhysicalLocalizedDuhamelEstimates source →
  Transfer.PhysicalDyadicThreeMechanismTransfer
physicalTransferFromSource source estimates = record
  { source = asLocalizedSource source
  ; parameter = parameter source
  ; defectRate = defectAt source
  ; inheritedCoefficient = inheritedAt source
  ; generated = generatedAt source
  ; leakage = leakageAt source
  ; ceiling = ceiling source
  ; alpha = alpha source
  ; beta = beta source
  ; sourceParameter = refl
  ; sourceDefectRate = refl
  ; sourceInheritedCoefficient = refl
  ; sourceGenerated = refl
  ; sourceLeakage = refl
  ; sourceCeiling = refl
  ; sourceAlpha = refl
  ; sourceBeta = refl
  ; defectRateNonnegative = defectNonnegative estimates
  ; inheritedCoefficientNonnegative = inheritedNonnegative estimates
  ; generatedNonnegative = generatedNonnegative estimates
  ; leakageNonnegative = leakageNonnegative estimates
  ; ceilingNonnegative = ceilingNonnegative estimates
  ; alphaNonnegative = alphaNonnegative estimates
  ; betaNonnegative = betaNonnegative estimates
  ; alphaStrict = alphaStrict estimates
  ; baseLinearInSelectedThreshold = baseLinearInSelectedThreshold estimates
  ; coefficientTransfer = inheritedTransfer estimates
  ; successorDecomposition = successorDecomposition estimates
  ; generatedAndLeakageForcing = generatedAndLeakageForcing estimates
  ; forcingFitsCeiling = forcingFitsCeiling estimates
  }

physicalSourceUsesOneShellTrajectory : Bool
physicalSourceUsesOneShellTrajectory = true

physicalTransferDerivedFromCanonicalSource : Bool
physicalTransferDerivedFromCanonicalSource = true

physicalSourceUsesOneShellTrajectoryIsTrue :
  physicalSourceUsesOneShellTrajectory ≡ true
physicalSourceUsesOneShellTrajectoryIsTrue = refl

physicalTransferDerivedFromCanonicalSourceIsTrue :
  physicalTransferDerivedFromCanonicalSource ≡ true
physicalTransferDerivedFromCanonicalSourceIsTrue = refl

-- Fail closed: neither the literal trajectory authority nor the estimates above
-- are claimed to be physically inhabited merely because the constructor exists.
physicalLocalizedDuhamelSourceConstructed : Bool
physicalLocalizedDuhamelSourceConstructed = false

physicalLocalizedDuhamelEstimatesConstructed : Bool
physicalLocalizedDuhamelEstimatesConstructed = false

physicalLocalizedDuhamelSourceConstructedIsFalse :
  physicalLocalizedDuhamelSourceConstructed ≡ false
physicalLocalizedDuhamelSourceConstructedIsFalse = refl

physicalLocalizedDuhamelEstimatesConstructedIsFalse :
  physicalLocalizedDuhamelEstimatesConstructed ≡ false
physicalLocalizedDuhamelEstimatesConstructedIsFalse = refl
