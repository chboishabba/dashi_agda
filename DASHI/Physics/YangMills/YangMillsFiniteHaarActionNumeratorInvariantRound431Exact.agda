{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsFiniteHaarActionNumeratorInvariantRound431Exact where

------------------------------------------------------------------------
-- A / ROUND431: HAAR + DENSITY ACTION INVARIANCE -> NUMERATOR INVARIANCE
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsFiniteNormalizedExpectationSymmetryExact as Sym
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record FiniteHaarMeasurePreservingAction
    {Configuration Action : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ)
    (laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure)
    : Set₁ where
  field
    actConfiguration : Action → Configuration → Configuration

    actObservable : Action →
      (Configuration → ℝ) → Configuration → ℝ

    observableActionIsPullback :
      ∀ action observable configuration →
      actObservable action observable configuration
      ≡ observable (actConfiguration action configuration)

    densityInvariant :
      ∀ action configuration →
      Physical.density measure (actConfiguration action configuration)
      ≡ Physical.density measure configuration

    haarIntegralPullbackInvariant :
      ∀ action integrand →
      Physical.haarIntegral measure
        (λ configuration →
          integrand (actConfiguration action configuration))
      ≡
      Physical.haarIntegral measure integrand

open FiniteHaarMeasurePreservingAction public

numeratorInvariantFromHaarAndDensity :
  ∀ {Configuration Action measure laws}
    (actionData :
      FiniteHaarMeasurePreservingAction
        {Configuration = Configuration} {Action = Action}
        measure laws)
    action observable →
  Finite.unnormalizedNumerator measure
    (actObservable actionData action observable)
  ≡
  Finite.unnormalizedNumerator measure observable
numeratorInvariantFromHaarAndDensity {measure = measure} {laws = laws}
    actionData action observable =
  trans
    (Finite.haarIntegralCongruent laws
      (λ configuration →
        Physical.density measure configuration *ℝ
        actObservable actionData action observable configuration)
      (λ configuration →
        Physical.density measure
          (actConfiguration actionData action configuration)
        *ℝ
        observable
          (actConfiguration actionData action configuration))
      (λ configuration →
        trans
          (cong
            (λ value →
              Physical.density measure configuration *ℝ value)
            (observableActionIsPullback
              actionData action observable configuration))
          (cong
            (λ density →
              density *ℝ
              observable
                (actConfiguration actionData action configuration))
            (sym (densityInvariant actionData action configuration)))))
    (haarIntegralPullbackInvariant actionData action
      (λ configuration →
        Physical.density measure configuration *ℝ observable configuration))

familyNumeratorActionInvariant :
  ∀ {Configuration Action sequenceLimit limitLaws quotient division}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    (actionData :
      ∀ cutoff →
      FiniteHaarMeasurePreservingAction
        {Configuration = Configuration} {Action = Action}
        (Limit.finiteMeasure family cutoff)
        (Limit.integrationLaws family cutoff)) →
  Sym.FiniteNumeratorActionInvariant family
    (λ action observable configuration →
      actObservable (actionData _) action observable configuration)
familyNumeratorActionInvariant family actionData = record
  { Sym.FiniteNumeratorActionInvariant.numeratorInvariant =
      λ cutoff action observable →
        numeratorInvariantFromHaarAndDensity
          (actionData cutoff) action observable
  }

round431FiniteHaarNumeratorCompilerLevel : ProofLevel
round431FiniteHaarNumeratorCompilerLevel = machineChecked

-- Remaining A1/A3 source facts are now literal pullback, Wilson/Gibbs density
-- invariance, and finite product-Haar invariance for the selected actions.
literalRound431FiniteHaarActionAttachmentLevel : ProofLevel
literalRound431FiniteHaarActionAttachmentLevel = conditional
