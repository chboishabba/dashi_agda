module DASHI.Physics.Closure.NSTriadKNHHBadInheritedGeneratedLeakageRound48Exact where

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
-- Round 47 reduced HH-bad to one selected-threshold recurrence.  This module
-- makes the physical content of one shell explicit instead of hiding it in a
-- single transfer inequality:
--
--   B_(q+1) = inherited_q + generated_q + leakage_q.
--
-- The recurrence follows from two genuinely interpretable estimates:
--
--   inherited_q <= (alpha/2) B_q,
--   generated_q + leakage_q
--     <= delta_* 2^(-(q+1)) beta.
--
-- Thus future PDE work can attack inherited transport and new/leaking defect
-- separately.  No estimate on any component is manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedThresholdRecurrenceRound47Exact as Selected

record PhysicalSelectedThresholdDefectDecomposition : Set where
  field
    parameter : Threshold.PositiveThreshold

    defectRate : Nat → ℚ
    inherited generated leakage : Nat → ℚ

    defectRateNonnegative : ∀ q → 0ℚ ≤ defectRate q
    inheritedNonnegative : ∀ q → 0ℚ ≤ inherited q
    generatedNonnegative : ∀ q → 0ℚ ≤ generated q
    leakageNonnegative : ∀ q → 0ℚ ≤ leakage q

    ceiling alpha beta : ℚ
    ceilingNonnegative : 0ℚ ≤ ceiling
    alphaNonnegative : 0ℚ ≤ alpha
    betaNonnegative : 0ℚ ≤ beta
    alphaStrict : alpha < 1ℚ

    baseLinearInSelectedThreshold :
      defectRate zero ≤ Threshold.threshold parameter * ceiling

    successorDecomposition : ∀ q →
      defectRate (suc q)
      ≡ inherited q + generated q + leakage q

    inheritedContraction : ∀ q →
      inherited q ≤ alpha * Sharp.half * defectRate q

    generatedAndLeakageForcing : ∀ q →
      generated q + leakage q
      ≤ Threshold.threshold parameter
        * Sharp.inverseDyadicScale (suc q) * beta

    forcingFitsCeiling : beta ≤ (1ℚ - alpha) * ceiling

open PhysicalSelectedThresholdDefectDecomposition public

componentBoundsGiveOneShellTransfer :
  (physical : PhysicalSelectedThresholdDefectDecomposition) →
  ∀ q →
  defectRate physical (suc q)
  ≤ alpha physical * Sharp.half * defectRate physical q
    + Threshold.threshold (parameter physical)
      * Sharp.inverseDyadicScale (suc q) * beta physical
componentBoundsGiveOneShellTransfer physical q =
  let
    summed :
      inherited physical q
        + (generated physical q + leakage physical q)
      ≤ alpha physical * Sharp.half * defectRate physical q
        + Threshold.threshold (parameter physical)
          * Sharp.inverseDyadicScale (suc q) * beta physical
    summed =
      ℚP.+-mono-≤
        (inheritedContraction physical q)
        (generatedAndLeakageForcing physical q)

    sourceMeaning :
      defectRate physical (suc q)
      ≡ inherited physical q
        + (generated physical q + leakage physical q)
    sourceMeaning =
      let open import Data.Rational.Tactic.RingSolver using (solve)
      in
      Relation.Binary.PropositionalEquality.trans
        (successorDecomposition physical q)
        (solve
          ( inherited physical q
          ∷ generated physical q
          ∷ leakage physical q
          ∷ []))
      where
      open import Agda.Builtin.List using ([]; _∷_)
      open import Relation.Binary.PropositionalEquality using (trans)
  in
  subst
    (λ source →
      source
      ≤ alpha physical * Sharp.half * defectRate physical q
        + Threshold.threshold (parameter physical)
          * Sharp.inverseDyadicScale (suc q) * beta physical)
    (sym sourceMeaning)
    summed

asSelectedThresholdDefectRecurrence :
  PhysicalSelectedThresholdDefectDecomposition →
  Selected.SelectedThresholdDefectRecurrence
asSelectedThresholdDefectRecurrence physical = record
  { parameter = parameter physical
  ; defectRate = defectRate physical
  ; defectRateNonnegative = defectRateNonnegative physical
  ; ceiling = ceiling physical
  ; alpha = alpha physical
  ; beta = beta physical
  ; ceilingNonnegative = ceilingNonnegative physical
  ; alphaNonnegative = alphaNonnegative physical
  ; betaNonnegative = betaNonnegative physical
  ; alphaStrict = alphaStrict physical
  ; baseLinearInSelectedThreshold =
      baseLinearInSelectedThreshold physical
  ; oneShellTransfer = componentBoundsGiveOneShellTransfer physical
  ; forcingFitsCeiling = forcingFitsCeiling physical
  }

selectedThresholdShellCeilingFromPhysicalDecomposition :
  (physical : PhysicalSelectedThresholdDefectDecomposition) →
  ∀ q →
  DASHI.Physics.Closure.NSTriadKNHHBadDefectRecurrenceNormalizationRound46Exact.normalizedDefectProfile
    (Selected.asPhysicalDefectRecurrence
      (asSelectedThresholdDefectRecurrence physical)) q
  ≤ ceiling physical
selectedThresholdShellCeilingFromPhysicalDecomposition physical q =
  Selected.selectedThresholdUniformShellCeiling
    (asSelectedThresholdDefectRecurrence physical) q

hhBadThreeMechanismTransferReductionClosed : Bool
hhBadThreeMechanismTransferReductionClosed = true

physicalInheritedGeneratedLeakageBoundsConstructed : Bool
physicalInheritedGeneratedLeakageBoundsConstructed = false

hhBadThreeMechanismTransferReductionClosedIsTrue :
  hhBadThreeMechanismTransferReductionClosed ≡ true
hhBadThreeMechanismTransferReductionClosedIsTrue = refl

physicalInheritedGeneratedLeakageBoundsConstructedIsFalse :
  physicalInheritedGeneratedLeakageBoundsConstructed ≡ false
physicalInheritedGeneratedLeakageBoundsConstructedIsFalse = refl
