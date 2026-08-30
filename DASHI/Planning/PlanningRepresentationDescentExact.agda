module DASHI.Planning.PlanningRepresentationDescentExact where

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- PLANNING REPRESENTATION DESCENT
--
-- A planning projection may legitimately decide an architectural property only
-- when that property is constant on every projection fibre.  The forward
-- theorem is generic; a single fibre witness rules out every factorisation.
------------------------------------------------------------------------

record FibreConstant
    {Design PlanningView Property : Set}
    (project : Design → PlanningView)
    (property : Design → Property) : Set₁ where
  field
    constantOnFibre :
      (left right : Design) →
      project left ≡ project right →
      property left ≡ property right

open FibreConstant public

factorisationImpliesFibreConstant :
  ∀ {Design PlanningView Property}
    {project : Design → PlanningView}
    {property : Design → Property} →
  INF.FactorsThrough project property →
  FibreConstant project property
factorisationImpliesFibreConstant factor =
  record
    { constantOnFibre = λ left right sameView →
        trans
          (INF.factorisation factor left)
          (trans
            (cong (INF.interpretFlat factor) sameView)
            (sym (INF.factorisation factor right)))
    }

representationLossBlocksDescent :
  ∀ {Design PlanningView Property}
    {project : Design → PlanningView}
    {property : Design → Property} →
  INF.NonFactorabilityWitness project property →
  INF.FactorsThrough project property →
  ⊥
representationLossBlocksDescent = INF.witnessRulesOutEveryFlatFactorisation

------------------------------------------------------------------------
-- Concrete planning-equivalent / architecturally-distinct witness.
------------------------------------------------------------------------

data Design : Set where
  shadedCourtyard exposedCourtyard : Design

data PlanningEnvelope : Set where
  sameHeightSetbackCoverage : PlanningEnvelope

data HeatExposure : Set where
  lowerExposure higherExposure : HeatExposure

planningProjection : Design → PlanningEnvelope
planningProjection shadedCourtyard = sameHeightSetbackCoverage
planningProjection exposedCourtyard = sameHeightSetbackCoverage

heatExposure : Design → HeatExposure
heatExposure shadedCourtyard = lowerExposure
heatExposure exposedCourtyard = higherExposure

samePlanningProjection :
  planningProjection shadedCourtyard ≡
  planningProjection exposedCourtyard
samePlanningProjection = refl

heatExposureDiffers :
  heatExposure shadedCourtyard ≡
  heatExposure exposedCourtyard → ⊥
heatExposureDiffers ()

planningEquivalentDesignsCanDifferArchitecturally :
  INF.NonFactorabilityWitness planningProjection heatExposure
planningEquivalentDesignsCanDifferArchitecturally =
  INF.nonFactorabilityWitness
    shadedCourtyard exposedCourtyard refl heatExposureDiffers

heatExposureDoesNotDescendThroughCoarsePlanningEnvelope :
  INF.FactorsThrough planningProjection heatExposure → ⊥
heatExposureDoesNotDescendThroughCoarsePlanningEnvelope =
  representationLossBlocksDescent
    planningEquivalentDesignsCanDifferArchitecturally

relabelingThePlanningEnvelopeCannotRecoverHeatExposure :
  ∀ {Recharted : Set} →
  (rechart : PlanningEnvelope → Recharted) →
  INF.FactorsThrough
    (λ design → rechart (planningProjection design))
    heatExposure →
  ⊥
relabelingThePlanningEnvelopeCannotRecoverHeatExposure rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart planningEquivalentDesignsCanDifferArchitecturally
