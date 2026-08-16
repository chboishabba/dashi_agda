module DASHI.Biology.Physical.PlanarianControlCalibrationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
-- Joel Grodstein and Michael Levin,
-- "A Computational Approach to Explaining Bioelectrically Induced Persistent,
-- Stochastic Changes of Axial Polarity in Planarian Regeneration",
-- Bioelectricity 4 (2022), 18--30.
-- DOI: 10.1089/bioe.2021.0036.
--
-- The source reports, among other quantitative checks, a parameter search in
-- which 155 of 555 tested parameter combinations satisfied all of the listed
-- hybrid-model constraints, and summarizes an Oviedo cutting case with 65%
-- wild-type / 35% side-head outcomes.  These values are encoded here as
-- provenance-bearing calibration observations, not promoted to universal
-- regeneration probabilities or a measured continuous basin geometry.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record CountObservation : Set where
  constructor countObservation
  field
    successful rejected total : Nat
    accountsForTotal : successful + rejected ≡ total

open CountObservation public

hybridModelParameterSweep : CountObservation
hybridModelParameterSweep = countObservation 155 400 555 refl

parameterSweepSuccessfulCount : successful hybridModelParameterSweep ≡ 155
parameterSweepSuccessfulCount = refl

parameterSweepTotalCount : total hybridModelParameterSweep ≡ 555
parameterSweepTotalCount = refl

record PercentObservation : Set where
  constructor percentObservation
  field
    firstPercent secondPercent : Nat
    sumsToHundred : firstPercent + secondPercent ≡ 100

open PercentObservation public

caseIIIWildTypeVsSideHead : PercentObservation
caseIIIWildTypeVsSideHead = percentObservation 65 35 refl

caseIIIWildTypePercent : firstPercent caseIIIWildTypeVsSideHead ≡ 65
caseIIIWildTypePercent = refl

caseIIISideHeadPercent : secondPercent caseIIIWildTypeVsSideHead ≡ 35
caseIIISideHeadPercent = refl

------------------------------------------------------------------------
-- Calibration semantics: observations constrain a model family but do not by
-- themselves identify a unique latent dynamical system or basin boundary.
------------------------------------------------------------------------

record CalibrationConstraint (Parameter ModelOutput : Set) : Set₁ where
  field
    predict : Parameter → ModelOutput
    acceptable : ModelOutput → Set

open CalibrationConstraint public

record CalibrationAuthorityBoundary : Set where
  field
    parameterSweepFractionIsNaturalPopulationProbability : Bool
    parameterSweepFractionIsNaturalPopulationProbabilityIsFalse :
      parameterSweepFractionIsNaturalPopulationProbability ≡ false
    phenotypeFrequencyUniquelyIdentifiesLatentBasin : Bool
    phenotypeFrequencyUniquelyIdentifiesLatentBasinIsFalse :
      phenotypeFrequencyUniquelyIdentifiesLatentBasin ≡ false
    qualitativeCalibrationIsFullExperimentalControlCapacity : Bool
    qualitativeCalibrationIsFullExperimentalControlCapacityIsFalse :
      qualitativeCalibrationIsFullExperimentalControlCapacity ≡ false

canonicalCalibrationAuthorityBoundary : CalibrationAuthorityBoundary
canonicalCalibrationAuthorityBoundary = record
  { parameterSweepFractionIsNaturalPopulationProbability = false
  ; parameterSweepFractionIsNaturalPopulationProbabilityIsFalse = refl
  ; phenotypeFrequencyUniquelyIdentifiesLatentBasin = false
  ; phenotypeFrequencyUniquelyIdentifiesLatentBasinIsFalse = refl
  ; qualitativeCalibrationIsFullExperimentalControlCapacity = false
  ; qualitativeCalibrationIsFullExperimentalControlCapacityIsFalse = refl
  }
