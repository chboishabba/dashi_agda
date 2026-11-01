module DASHI.Physics.Closure.NSTriadKNHHBadDyadicThreeMechanismRecurrenceRound48Exact where

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
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Combine the Round-48 three-mechanism decomposition with the exact inverse
-- dyadic inheritance theorem.  The physical recurrence no longer needs an
-- opaque `inherited <= alpha/2 * B_q` field.  It is enough to prove:
--
--   inherited_q = delta_* 2^-q A_q,
--   A_(q+1) <= alpha A_q,
--   generated_q + leakage_q
--     <= delta_* 2^(-(q+1)) beta,
--
-- together with the exact successor decomposition.  The half factor is then
-- machine-derived from 2^(-(q+1)) = (1/2) 2^-q.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadDyadicInheritedHalfRound48Exact as Half
import DASHI.Physics.Closure.NSTriadKNHHBadInheritedGeneratedLeakageRound48Exact as Split
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedThresholdRecurrenceRound47Exact as Selected

record PhysicalDyadicThreeMechanismTransfer : Set where
  field
    parameter : Threshold.PositiveThreshold

    defectRate : Nat → ℚ
    defectRateNonnegative : ∀ q → 0ℚ ≤ defectRate q

    inheritedCoefficient generated leakage : Nat → ℚ
    inheritedCoefficientNonnegative : ∀ q → 0ℚ ≤ inheritedCoefficient q
    generatedNonnegative : ∀ q → 0ℚ ≤ generated q
    leakageNonnegative : ∀ q → 0ℚ ≤ leakage q

    ceiling alpha beta : ℚ
    ceilingNonnegative : 0ℚ ≤ ceiling
    alphaNonnegative : 0ℚ ≤ alpha
    betaNonnegative : 0ℚ ≤ beta
    alphaStrict : alpha < 1ℚ

    baseLinearInSelectedThreshold :
      defectRate zero ≤ Threshold.threshold parameter * ceiling

    coefficientTransfer : ∀ q →
      inheritedCoefficient (suc q) ≤ alpha * inheritedCoefficient q

    successorDecomposition : ∀ q →
      defectRate (suc q)
      ≡ Threshold.threshold parameter
          * Sharp.inverseDyadicScale (suc q)
          * inheritedCoefficient (suc q)
        + generated q + leakage q

    generatedAndLeakageForcing : ∀ q →
      generated q + leakage q
      ≤ Threshold.threshold parameter
        * Sharp.inverseDyadicScale (suc q) * beta

    forcingFitsCeiling : beta ≤ (1ℚ - alpha) * ceiling

open PhysicalDyadicThreeMechanismTransfer public

inheritedData :
  (physical : PhysicalDyadicThreeMechanismTransfer) →
  Half.InverseShellInheritedDefect (parameter physical)
inheritedData physical = record
  { coefficient = inheritedCoefficient physical
  ; coefficientNonnegative = inheritedCoefficientNonnegative physical
  ; alpha = alpha physical
  ; alphaNonnegative = alphaNonnegative physical
  ; coefficientTransfer = coefficientTransfer physical
  }

inheritedAt :
  PhysicalDyadicThreeMechanismTransfer → Nat → ℚ
inheritedAt physical q = Half.inheritedDefect (inheritedData physical) q

asThreeMechanismDecomposition :
  PhysicalDyadicThreeMechanismTransfer →
  Split.PhysicalSelectedThresholdDefectDecomposition
asThreeMechanismDecomposition physical = record
  { parameter = parameter physical
  ; defectRate = defectRate physical
  ; inherited = inheritedAt physical
  ; generated = generated physical
  ; leakage = leakage physical
  ; defectRateNonnegative = defectRateNonnegative physical
  ; inheritedNonnegative = Half.inheritedDefectNonnegative (inheritedData physical)
  ; generatedNonnegative = generatedNonnegative physical
  ; leakageNonnegative = leakageNonnegative physical
  ; ceiling = ceiling physical
  ; alpha = alpha physical
  ; beta = beta physical
  ; ceilingNonnegative = ceilingNonnegative physical
  ; alphaNonnegative = alphaNonnegative physical
  ; betaNonnegative = betaNonnegative physical
  ; alphaStrict = alphaStrict physical
  ; baseLinearInSelectedThreshold = baseLinearInSelectedThreshold physical
  ; successorDecomposition = λ q →
      successorDecomposition physical q
  ; inheritedContraction = λ q →
      Half.inverseShellInheritedDefectHalvesModuloCoefficient
        (inheritedData physical) q
  ; generatedAndLeakageForcing = generatedAndLeakageForcing physical
  ; forcingFitsCeiling = forcingFitsCeiling physical
  }

asSelectedThresholdDefectRecurrence :
  PhysicalDyadicThreeMechanismTransfer →
  Selected.SelectedThresholdDefectRecurrence
asSelectedThresholdDefectRecurrence physical =
  Split.asSelectedThresholdDefectRecurrence
    (asThreeMechanismDecomposition physical)

physicalDyadicThreeMechanismUniformCeiling :
  (physical : PhysicalDyadicThreeMechanismTransfer) →
  ∀ q →
  DASHI.Physics.Closure.NSTriadKNHHBadDefectRecurrenceNormalizationRound46Exact.normalizedDefectProfile
    (Selected.asPhysicalDefectRecurrence
      (asSelectedThresholdDefectRecurrence physical)) q
  ≤ ceiling physical
physicalDyadicThreeMechanismUniformCeiling physical q =
  Selected.selectedThresholdUniformShellCeiling
    (asSelectedThresholdDefectRecurrence physical) q

hhBadDyadicThreeMechanismRecurrenceClosed : Bool
hhBadDyadicThreeMechanismRecurrenceClosed = true

physicalDyadicThreeMechanismTransferConstructed : Bool
physicalDyadicThreeMechanismTransferConstructed = false

hhBadDyadicThreeMechanismRecurrenceClosedIsTrue :
  hhBadDyadicThreeMechanismRecurrenceClosed ≡ true
hhBadDyadicThreeMechanismRecurrenceClosedIsTrue = refl

physicalDyadicThreeMechanismTransferConstructedIsFalse :
  physicalDyadicThreeMechanismTransferConstructed ≡ false
physicalDyadicThreeMechanismTransferConstructedIsFalse = refl
