{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119FiniteEuclideanSourceExact where

------------------------------------------------------------------------
-- A / CMP119 WHOLE-LATTICE EUCLIDEAN COVARIANCE -> FINITE EXPECTATION
--
-- Source calibration:
--   T. Balaban, CMP 119 (1988), Section 3, especially (3.39):
--   the whole-lattice regular expressions are Euclidean covariant under
--   Euclidean transformations preserving the lattice.
--
-- This owner keeps the exact application seam explicit: source action on
-- configurations/observables must be the same action used by the literal
-- normalized CMP119 expectation.  Once numerator and normalization are
-- invariant under that change of variables, normalized expectation invariance
-- is the source-facing result consumed by ConcreteA.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsFiniteNormalizedExpectationSymmetryExact as Symmetry
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119WholeLatticeEuclideanCovariance
    (Configuration EuclideanAction : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    : Set₂ where
  field
    actConfiguration : EuclideanAction → Configuration → Configuration
    actObservable :
      EuclideanAction →
      (Configuration → ℝ) →
      (Configuration → ℝ)

    -- Same observable action as pullback by the literal configuration action.
    observableActionIsPullback :
      ∀ action observable configuration →
      actObservable action observable configuration
      ≡ observable (actConfiguration action configuration)

    -- Source-exact finite normalized expectation statement obtained from the
    -- whole-lattice covariance/change-of-variables theorem.
    finiteNormalizedExpectationEuclideanInvariant :
      ∀ cutoff action observable →
      Limit.finiteExpectation family cutoff
        (actObservable action observable)
      ≡ Limit.finiteExpectation family cutoff observable

open CMP119WholeLatticeEuclideanCovariance public

finiteEuclideanInvariant =
  CMP119WholeLatticeEuclideanCovariance.finiteNormalizedExpectationEuclideanInvariant

cmp119WholeLatticeEuclideanCovarianceSourceLevel : ProofLevel
cmp119WholeLatticeEuclideanCovarianceSourceLevel = standardImported

-- Repository payment: identify the actual finite CMP119 family/action with the
-- source whole-lattice objects to which (3.39) and the associated
-- change-of-variables covariance apply.
literalCMP119WholeLatticeEuclideanAttachmentLevel : ProofLevel
literalCMP119WholeLatticeEuclideanAttachmentLevel = conditional

cmp119FiniteEuclideanExpectationAdapterLevel : ProofLevel
cmp119FiniteEuclideanExpectationAdapterLevel = machineChecked


euclideanFromNumeratorChangeOfVariables :
  ∀ {Configuration EuclideanAction sequenceLimit limitLaws quotient division}
    {family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration {sequenceLimit = sequenceLimit}
        limitLaws quotient division}
    (actConfiguration : EuclideanAction → Configuration → Configuration)
    (actObservable :
      EuclideanAction → (Configuration → ℝ) → Configuration → ℝ)
    (pullback :
      ∀ action observable configuration →
      actObservable action observable configuration
      ≡ observable (actConfiguration action configuration))
    (numerator :
      Symmetry.FiniteNumeratorActionInvariant family actObservable) →
  CMP119WholeLatticeEuclideanCovariance
    Configuration EuclideanAction family
euclideanFromNumeratorChangeOfVariables
    actConfiguration actObservable pullback numerator = record
  { CMP119WholeLatticeEuclideanCovariance.actConfiguration =
      actConfiguration
  ; CMP119WholeLatticeEuclideanCovariance.actObservable =
      actObservable
  ; CMP119WholeLatticeEuclideanCovariance.observableActionIsPullback =
      pullback
  ; CMP119WholeLatticeEuclideanCovariance.finiteNormalizedExpectationEuclideanInvariant =
      Symmetry.finiteNormalizedExpectationInvariantFromNumerator
        _ actObservable numerator
  }

cmp119NumeratorEuclideanAdapterLevel : ProofLevel
cmp119NumeratorEuclideanAdapterLevel =
  Symmetry.finiteNumeratorToNormalizedSymmetryCompilerLevel
