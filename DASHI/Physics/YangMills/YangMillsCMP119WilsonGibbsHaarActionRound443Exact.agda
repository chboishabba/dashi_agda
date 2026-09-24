{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact where

------------------------------------------------------------------------
-- A / ROUND443: WILSON-ACTION INVARIANCE -> GIBBS-DENSITY INVARIANCE
--
-- Round431 correctly requires density invariance and product-Haar pullback
-- invariance.  The density half should not be a second physical theorem:
-- the finite CMP119 density is a scalar weight of the Wilson/Gibbs action.
-- Therefore an action preserving that action preserves the density by congruence.
--
-- This owner makes the factorization explicit and constructs the exact R431
-- FiniteHaarMeasurePreservingAction.  The remaining source mathematics is:
--
--   * literal Wilson/Gibbs action invariance for the selected finite symmetry;
--   * product/constrained-Haar pullback invariance.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsFiniteHaarActionNumeratorInvariantRound431Exact as R431

record WilsonGibbsHaarAction
    {Configuration Action : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ)
    (laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure)
    : Set₁ where
  field
    actConfiguration : Action → Configuration → Configuration

    actObservable :
      Action → (Configuration → ℝ) → Configuration → ℝ

    observableActionIsPullback :
      ∀ action observable configuration →
      actObservable action observable configuration
      ≡ observable (actConfiguration action configuration)

    -- Literal finite Wilson/Gibbs action and its scalar density map.
    finiteAction : Configuration → ℝ
    gibbsWeight : ℝ → ℝ

    densityIsGibbsWeight :
      ∀ configuration →
      Physical.density measure configuration
      ≡ gibbsWeight (finiteAction configuration)

    finiteActionInvariant :
      ∀ action configuration →
      finiteAction (actConfiguration action configuration)
      ≡ finiteAction configuration

    haarIntegralPullbackInvariant :
      ∀ action integrand →
      Physical.haarIntegral measure
        (λ configuration →
          integrand (actConfiguration action configuration))
      ≡ Physical.haarIntegral measure integrand

open WilsonGibbsHaarAction public

gibbsDensityInvariant :
  ∀ {Configuration Action measure laws}
    (dataSet :
      WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws)
    action configuration →
  Physical.density measure
      (actConfiguration dataSet action configuration)
  ≡ Physical.density measure configuration
gibbsDensityInvariant {measure = measure} dataSet action configuration =
  trans
    (densityIsGibbsWeight dataSet
      (actConfiguration dataSet action configuration))
    (trans
      (cong
        (gibbsWeight dataSet)
        (finiteActionInvariant dataSet action configuration))
      (sym (densityIsGibbsWeight dataSet configuration)))

asFiniteHaarMeasurePreservingAction :
  ∀ {Configuration Action measure laws} →
  WilsonGibbsHaarAction
    {Configuration = Configuration} {Action = Action}
    measure laws →
  R431.FiniteHaarMeasurePreservingAction
    {Configuration = Configuration} {Action = Action}
    measure laws
asFiniteHaarMeasurePreservingAction dataSet = record
  { R431.FiniteHaarMeasurePreservingAction.actConfiguration =
      actConfiguration dataSet
  ; R431.FiniteHaarMeasurePreservingAction.actObservable =
      actObservable dataSet
  ; R431.FiniteHaarMeasurePreservingAction.observableActionIsPullback =
      observableActionIsPullback dataSet
  ; R431.FiniteHaarMeasurePreservingAction.densityInvariant =
      gibbsDensityInvariant dataSet
  ; R431.FiniteHaarMeasurePreservingAction.haarIntegralPullbackInvariant =
      haarIntegralPullbackInvariant dataSet
  }

round443WilsonActionToDensityInvariantCompilerLevel : ProofLevel
round443WilsonActionToDensityInvariantCompilerLevel = machineChecked

round443R431ActionCompilerLevel : ProofLevel
round443R431ActionCompilerLevel = machineChecked

-- The density-invariance leaf has been removed.  A1 now asks directly for the
-- source Wilson-action symmetry and the product-Haar change-of-variables law.
literalRound443FiniteWilsonActionInvarianceLevel : ProofLevel
literalRound443FiniteWilsonActionInvarianceLevel = conditional

literalRound443FiniteProductHaarInvarianceLevel : ProofLevel
literalRound443FiniteProductHaarInvarianceLevel = conditional
