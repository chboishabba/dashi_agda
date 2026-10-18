{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CylinderEuclideanCovarianceExact where

------------------------------------------------------------------------
-- LITERAL A / NORMALIZED CMP119 CYLINDER LIMIT PRESERVES EUCLIDEAN ACTION
--
-- Reflection positivity already has a finite->continuum cylinder compiler.
-- Euclidean covariance needs even less: if the exact normalized finite
-- expectation is invariant under the selected Euclidean action at every cutoff,
-- scalar-limit uniqueness makes the SAME continuum expectation invariant.
--
-- Thus OS1's finite-to-continuum passage is compiler algebra.  The physical
-- leaf is the literal finite CMP119 action on cylinder observables and its
-- finite expectation invariance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Normalized
import DASHI.Physics.YangMills.BalabanCylinderLimitActionInvariantExact as ActionLimit
import DASHI.Physics.YangMills.YangMillsLiteralRealCylinderLimitPhysicalMeasureExact as PhysicalLimit
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

record PinnedCMP119CylinderActionInputs
    {Observable Action : Set}
    {sequenceLimit}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Normalized.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    (source :
      Normalized.NormalizedCylinderSourceData
        Observable
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient division) : Set₁ where
  field
    act : Action → Observable → Observable

    finiteNormalizedActionInvariant :
      ∀ cutoff action observable →
      Normalized.finiteNormalized source cutoff
        (act action observable)
      ≡
      Normalized.finiteNormalized source cutoff observable

open PinnedCMP119CylinderActionInputs public

asCylinderActionInvariantInputs :
  ∀ {Observable Action sequenceLimit}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Normalized.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {source :
      Normalized.NormalizedCylinderSourceData
        Observable
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient division} →
  PinnedCMP119CylinderActionInputs limitLaws source →
  ActionLimit.CylinderActionInvariantInputs
    (Normalized.asScalarCylinderExpectationLimitData source)
    Action
asCylinderActionInvariantInputs inputs = record
  { ActionLimit.CylinderActionInvariantInputs.act =
      act inputs
  ; ActionLimit.CylinderActionInvariantInputs.finiteActionInvariant =
      finiteNormalizedActionInvariant inputs
  }

continuumNormalizedActionInvariant :
  ∀ {Observable Action sequenceLimit}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Normalized.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {source :
      Normalized.NormalizedCylinderSourceData
        Observable
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient division}
    (inputs : PinnedCMP119CylinderActionInputs limitLaws source)
    action observable →
  Normalized.continuumNormalized source
    (act inputs action observable)
  ≡
  Normalized.continuumNormalized source observable
continuumNormalizedActionInvariant
    {source = source} inputs action observable =
  ActionLimit.continuumActionInvariant
    (asCylinderActionInvariantInputs inputs)
    action observable

literalPhysicalContinuumMeasureActionInvariant :
  ∀ {Observable Action sequenceLimit}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Normalized.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {source :
      Normalized.NormalizedCylinderSourceData
        Observable
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient division}
    (inputs : PinnedCMP119CylinderActionInputs limitLaws source)
    action observable →
  Physical.expectation
    (PhysicalLimit.literalRealContinuumMeasure source)
    (act inputs action observable)
  ≡
  Physical.expectation
    (PhysicalLimit.literalRealContinuumMeasure source)
    observable
literalPhysicalContinuumMeasureActionInvariant inputs =
  continuumNormalizedActionInvariant inputs

pinnedCMP119CylinderActionLimitCompilerLevel : ProofLevel
pinnedCMP119CylinderActionLimitCompilerLevel = machineChecked

-- Actual A/OS1 source payment after this compiler:
-- instantiate Action by the Euclidean transformations admitted by the selected
-- cylinder algebra and prove the normalized finite CMP119 expectations are
-- invariant under that literal action.
literalCMP119FiniteEuclideanActionInvarianceLevel : ProofLevel
literalCMP119FiniteEuclideanActionInvarianceLevel = conditional

clayPromotion : Bool
clayPromotion = false
