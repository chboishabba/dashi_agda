module DASHI.Governance.MacGregorMeasurableImpactObserverBoundaryExact where

open import DASHI.Core.Prelude
import DASHI.Core.MeasurementBoundaryNonfactorabilityExact as Measurement
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Governance.FeministClimateJusticeSourceRegistryExact as Sources

------------------------------------------------------------------------
-- MACGREGOR 2010: MEASURABLE IMPACT != COMPLETE GENDERED CLIMATE DISCOURSE
--
-- Sherilyn MacGregor, "'Gender and climate change': from impacts to
-- discourses", Journal of the Indian Ocean Region 6(2):223-238 (2010).
-- DOI: 10.1080/19480881.2010.536669.
--
-- The source critiques an unnecessarily narrow fixation on material/measurable
-- impacts and passive-victim framing.  The finite witness below formalises only
-- the observer lesson: equal measured-impact code need not determine agency /
-- discourse position.  It does not claim measurement is invalid or that every
-- gender-and-climate study has the criticised framing.
------------------------------------------------------------------------

data ClimateDiscourseState : Set where
  passiveVictimFraming activePoliticalAgentFraming : ClimateDiscourseState

data MeasuredImpactCode : Set where sameMeasuredImpact : MeasuredImpactCode

data AgencyDiscourseRole : Set where passiveVictimRole activePoliticalAgentRole : AgencyDiscourseRole

measuredImpactObserver : ClimateDiscourseState → MeasuredImpactCode
measuredImpactObserver _ = sameMeasuredImpact

agencyDiscourseObserver : ClimateDiscourseState → AgencyDiscourseRole
agencyDiscourseObserver passiveVictimFraming = passiveVictimRole
agencyDiscourseObserver activePoliticalAgentFraming = activePoliticalAgentRole

impactBoundary :
  Measurement.MeasurementBoundary ClimateDiscourseState MeasuredImpactCode AgencyDiscourseRole
impactBoundary =
  Measurement.measurementBoundary measuredImpactObserver agencyDiscourseObserver

sameMeasuredImpactDifferentAgency : Measurement.BoundaryLossWitness impactBoundary
sameMeasuredImpactDifferentAgency =
  Measurement.boundaryLossWitness
    passiveVictimFraming activePoliticalAgentFraming refl (λ ())

agencyDoesNotDescendThroughMeasuredImpact :
  Consumer.FactorsThrough measuredImpactObserver agencyDiscourseObserver → ⊥
agencyDoesNotDescendThroughMeasuredImpact =
  Measurement.boundaryLossBlocksFactorization sameMeasuredImpactDifferentAgency

source : Sources.SourceReference
source = Sources.macGregor2010

record MacGregorMeasurableImpactBoundary : Set where
  constructor macGregorMeasurableImpactBoundary
  field
    measurableImpactExhaustsGenderedClimatePolitics : Bool
    measurableImpactExhaustsGenderedClimatePoliticsIsFalse :
      measurableImpactExhaustsGenderedClimatePolitics ≡ false
    measuredVulnerabilityMeansPassiveVictimByDefinition : Bool
    measuredVulnerabilityMeansPassiveVictimByDefinitionIsFalse :
      measuredVulnerabilityMeansPassiveVictimByDefinition ≡ false
    observerCritiqueMeansImpactMeasurementIsInvalid : Bool
    observerCritiqueMeansImpactMeasurementIsInvalidIsFalse :
      observerCritiqueMeansImpactMeasurementIsInvalid ≡ false

canonicalMacGregorMeasurableImpactBoundary : MacGregorMeasurableImpactBoundary
canonicalMacGregorMeasurableImpactBoundary =
  macGregorMeasurableImpactBoundary false refl false refl false refl
