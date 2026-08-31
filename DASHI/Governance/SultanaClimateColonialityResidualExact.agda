module DASHI.Governance.SultanaClimateColonialityResidualExact where

open import DASHI.Core.Prelude
import DASHI.Core.ResponsibilityBurdenNonfactorabilityExact as Geometry
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Governance.FeministClimateJusticeSourceRegistryExact as Sources

------------------------------------------------------------------------
-- SULTANA: RESPONSIBILITY / BURDEN RESIDUAL
--
-- Farhana Sultana, "The Unbearable Heaviness of Climate Coloniality",
-- Political Geography 99 (2022), 102638.
-- DOI: 10.1016/j.polgeo.2022.102638.
--
-- The paper motivates retaining contribution/responsibility, burden/vulnerability,
-- colonial dispossession and climate debt as politically structured relations.
-- The Nat/finite comparison below is NOT an empirical emissions or damage score;
-- it is an exact nonfactorability witness for the theorem shape.
------------------------------------------------------------------------

climateJusticeGeometry :
  Geometry.ResponsibilityBurdenGeometry
    Geometry.DemoPopulation
    Geometry.DemoAggregate
    Geometry.DemoContribution
    Geometry.DemoBurden
climateJusticeGeometry = Geometry.demoGeometry

aggregateDoesNotRecoverResponsibility :
  Consumer.FactorsThrough
    (Geometry.aggregateObserver climateJusticeGeometry)
    (Geometry.contribution climateJusticeGeometry) → ⊥
aggregateDoesNotRecoverResponsibility =
  Geometry.responsibilityDoesNotDescendThroughAggregate
    Geometry.demoResponsibilityLoss

aggregateDoesNotRecoverBurden :
  Consumer.FactorsThrough
    (Geometry.aggregateObserver climateJusticeGeometry)
    (Geometry.burden climateJusticeGeometry) → ⊥
aggregateDoesNotRecoverBurden =
  Geometry.burdenDoesNotDescendThroughAggregate
    Geometry.demoBurdenLoss

-- The canonical finite state explicitly permits lower contribution with higher
-- burden.  This is structural calibration, not a pointwise empirical claim
-- about every Global South / Global North person or polity.
lowerContributionHigherBurdenWitness :
  Geometry.contribution climateJusticeGeometry Geometry.lowerContributionHigherBurden ≡ Geometry.lowContribution
lowerContributionHigherBurdenWitness = refl

higherBurdenWitness :
  Geometry.burden climateJusticeGeometry Geometry.lowerContributionHigherBurden ≡ Geometry.highBurden
higherBurdenWitness = refl

source : Sources.SourceReference
source = Sources.sultana2022

record SultanaClimateColonialityBoundary : Set where
  constructor sultanaClimateColonialityBoundary
  field
    aggregateOvershootDeterminesResponsibility : Bool
    aggregateOvershootDeterminesResponsibilityIsFalse :
      aggregateOvershootDeterminesResponsibility ≡ false
    aggregateOvershootDeterminesBurden : Bool
    aggregateOvershootDeterminesBurdenIsFalse :
      aggregateOvershootDeterminesBurden ≡ false
    completeDataDischargesResponsibilityAsymmetry : Bool
    completeDataDischargesResponsibilityAsymmetryIsFalse :
      completeDataDischargesResponsibilityAsymmetry ≡ false
    finiteWitnessIsUniversalEmpiricalBlameOrdering : Bool
    finiteWitnessIsUniversalEmpiricalBlameOrderingIsFalse :
      finiteWitnessIsUniversalEmpiricalBlameOrdering ≡ false

canonicalSultanaClimateColonialityBoundary : SultanaClimateColonialityBoundary
canonicalSultanaClimateColonialityBoundary =
  sultanaClimateColonialityBoundary false refl false refl false refl false refl
