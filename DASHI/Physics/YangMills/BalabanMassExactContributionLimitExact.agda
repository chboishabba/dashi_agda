{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanMassExactContributionLimitExact where

------------------------------------------------------------------------
-- VANISHING MASS-EXACT CONTRIBUTION ERROR -> LITERAL HAAR INTEGRAL LIMIT
--
-- This closes the generic analytic step needed for both
--
--   numerator(O) = integral rho O dHaar
--   Z            = integral rho   dHaar.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ; _-ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCompactHaarMassExactContributionApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

record MassExactContributionLimit
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError) : Set₂ where
  field
    Cell : Nat → Set

    approximationAt :
      ∀ refinement →
      Approx.MassExactContributionApproximation
        (Cell refinement)

    literalIntegral : ℝ

    sourceIntegralIsLiteral :
      ∀ refinement →
      Approx.sourceIntegral (approximationAt refinement)
      ≡ literalIntegral

    combinedModulusVanishes :
      Seq.Vanishes sequenceLimit
        (λ refinement →
          Approx.combinedModulus
            (approximationAt refinement))

open MassExactContributionLimit public

executableContributionErrorBound :
  ∀ {sequenceLimit}
    (dataSet : MassExactContributionLimit sequenceLimit)
    refinement →
  absℝ
    (literalIntegral dataSet
      -ℝ
      Approx.executableSum
        (approximationAt dataSet refinement))
  ≤ℝ
  Approx.combinedModulus
    (approximationAt dataSet refinement)
executableContributionErrorBound dataSet refinement =
  subst
    (λ source →
      absℝ
        (source
          -ℝ
          Approx.executableSum
            (approximationAt dataSet refinement))
      ≤ℝ
      Approx.combinedModulus
        (approximationAt dataSet refinement))
    (sourceIntegralIsLiteral dataSet refinement)
    (Approx.massExactContributionApproximationError
      (approximationAt dataSet refinement))

literalIntegralIsExecutableLimit :
  ∀ {sequenceLimit}
    (dataSet : MassExactContributionLimit sequenceLimit) →
  literalIntegral dataSet
  ≡
  Seq.limit sequenceLimit
    (λ refinement →
      Approx.executableSum
        (approximationAt dataSet refinement))
literalIntegralIsExecutableLimit
    {sequenceLimit = sequenceLimit} dataSet =
  sym
    (Seq.limitFromVanishingError sequenceLimit
      (λ refinement →
        Approx.executableSum
          (approximationAt dataSet refinement))
      (literalIntegral dataSet)
      (λ refinement →
        Approx.combinedModulus
          (approximationAt dataSet refinement))
      (executableContributionErrorBound dataSet)
      (combinedModulusVanishes dataSet))

massExactContributionLimitCompilerLevel : ProofLevel
massExactContributionLimitCompilerLevel = machineChecked

-- Literal YM work remaining at this layer is the concrete construction of the
-- approximation family and vanishing of its two explicit moduli.
literalHaarCellOscillationVanishesLevel : ProofLevel
literalHaarCellOscillationVanishesLevel = conditional

literalGate4ContributionApproximationVanishesLevel : ProofLevel
literalGate4ContributionApproximationVanishesLevel = conditional
