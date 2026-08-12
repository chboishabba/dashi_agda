module DASHI.Physics.Closure.NSTriadKNHHGoodAmplitudeAllocatedOwnerRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Connect Round 42's literal amplitude allocation directly to the already
-- proved Round-41 periodized Young owner.  Once the physical shell samples
-- have been identified with the annular strain kernel, the only HH-good data
-- required here are:
--
--   one selected quadratic amplitude leg <= E0,
--   weighted residual quartic core <= X D.
--
-- Round 42 then proves W <= E0 X D and this module consumes that theorem
-- without adding another independent local-mass assumption.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHGoodFiniteKernelCauchyRound40Exact as Good
import DASHI.Physics.Closure.NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact as Periodized
import DASHI.Physics.Closure.NSTriadKNHHGoodSquaredYoungOwnerRound41Exact as Young
import DASHI.Physics.Closure.NSTriadKNHHGoodAmplitudeAllocationRound42Exact as Allocation

periodizedHHGoodOwnerFromLiteralAmplitudeAllocation :
  ∀ {st : Level} {TorusPoint : Set st}
    {environment : Owner.TaxEnvironment}
    {kernelTheorem : Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell : Nat}
    {parameter : Threshold.PositiveThreshold}
    {samples : List (Good.HHGoodKernelSample parameter)} →
  Periodized.PhysicalStrainShellKernelMassIdentification
    kernelTheorem shell parameter samples →
  (allocation : Allocation.HHGoodCriticalDissipationAllocation
    environment parameter samples) →
  Threshold.PositiveThreshold →
  Owner.AdmissibleOwnerEstimate environment
periodizedHHGoodOwnerFromLiteralAmplitudeAllocation
    {environment = environment}
    {kernelTheorem = kernelTheorem}
    {shell = shell}
    {parameter = parameter}
    {samples = samples}
    identification allocation viscositySplit =
  Young.periodizedHHGoodOwnerFromDataEnergyFactorization record
    { identification = identification
    ; dataEnergyFactor =
        Allocation.dataEnergyFactor
          (Allocation.amplitudeAllocation allocation)
    ; dataEnergyFactorNonnegative =
        Allocation.dataEnergyFactorNonnegative
          (Allocation.amplitudeAllocation allocation)
    ; viscositySplit = viscositySplit
    ; criticalNonnegative = Allocation.criticalNonnegative allocation
    ; dissipationNonnegative = Allocation.dissipationNonnegative allocation
    ; localMassBelowDataCriticalDissipation =
        Allocation.physicalHHGoodDataEnergyFactorization allocation
    }

hhGoodAmplitudeAllocationToOwnerClosed : Bool
hhGoodAmplitudeAllocationToOwnerClosed = true

physicalHHGoodOwnerNowReducedToKernelAndTwoAmplitudeBounds : Bool
physicalHHGoodOwnerNowReducedToKernelAndTwoAmplitudeBounds = true

hhGoodAmplitudeAllocationToOwnerClosedIsTrue :
  hhGoodAmplitudeAllocationToOwnerClosed ≡ true
hhGoodAmplitudeAllocationToOwnerClosedIsTrue = refl
