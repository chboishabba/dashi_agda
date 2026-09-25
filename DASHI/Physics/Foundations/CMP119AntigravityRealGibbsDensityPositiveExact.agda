{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; -ℝ_; _<ℝ_)

import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as Gibbs

------------------------------------------------------------------------
-- LITERAL REAL WILSON/GIBBS DENSITY IS A POSITIVE EXPONENTIAL
--
-- Round443 already pins the physical density to gibbsWeight(finiteAction U).
-- The remaining same-object statement is the expected Euclidean Gibbs law
--
--   gibbsWeight(S) = exp(-S).
--
-- Strict positivity of the real exponential is standard analysis.  Keeping
-- those two inputs separate prevents Gibbs terminology from silently
-- supplying the actual exponential density.
------------------------------------------------------------------------

record StrictPositiveRealExponential : Set₁ where
  field
    expReal : ℝ → ℝ
    expPositive :
      ∀ value →
      0ℝ <ℝ expReal value

open StrictPositiveRealExponential public

record WilsonGibbsExponentialDensityAttachment
    {Configuration Action : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    {laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure}
    (gibbs :
      Gibbs.WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws)
    (exponential : StrictPositiveRealExponential) : Set₁ where
  field
    gibbsWeightIsNegativeActionExponential :
      ∀ actionValue →
      Gibbs.gibbsWeight gibbs actionValue
      ≡
      expReal exponential (-ℝ actionValue)

open WilsonGibbsExponentialDensityAttachment public

densityIsNegativeActionExponential :
  ∀ {Configuration Action measure laws}
    {gibbs :
      Gibbs.WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws}
    {exponential : StrictPositiveRealExponential}
    (attachment :
      WilsonGibbsExponentialDensityAttachment gibbs exponential) →
  ∀ configuration →
  Physical.density measure configuration
  ≡
  expReal exponential
    (-ℝ Gibbs.finiteAction gibbs configuration)
densityIsNegativeActionExponential
    {gibbs = gibbs} {exponential = exponential}
    attachment configuration =
  trans
    (Gibbs.densityIsGibbsWeight gibbs configuration)
    (gibbsWeightIsNegativeActionExponential
      attachment
      (Gibbs.finiteAction gibbs configuration))

gibbsDensityStrictlyPositive :
  ∀ {Configuration Action measure laws}
    {gibbs :
      Gibbs.WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws}
    {exponential : StrictPositiveRealExponential}
    (attachment :
      WilsonGibbsExponentialDensityAttachment gibbs exponential) →
  ∀ configuration →
  0ℝ <ℝ Physical.density measure configuration
gibbsDensityStrictlyPositive
    {gibbs = gibbs} {exponential = exponential}
    attachment configuration =
  subst
    (λ value → 0ℝ <ℝ value)
    (sym
      (densityIsNegativeActionExponential
        attachment configuration))
    (expPositive exponential
      (-ℝ Gibbs.finiteAction gibbs configuration))
