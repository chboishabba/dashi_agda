module DASHI.Environment.BiocontrolChemistryObserverParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Environment.BiocontrolChemistry369IndexExact as ChemistryIndex
import DASHI.Environment.BiocontrolChemistryObservationFibreExact as ChemistryFibre
import DASHI.Environment.BiocontrolCalibratedEcologicalClassificationExact as Calibration

------------------------------------------------------------------------
-- CHEMISTRY OBSERVER PARETO SELECTION
--
-- Finite repository-local observer ladder for the biocontrol chemistry lane.
-- Ranking happens only after hard admissibility and consumer adequacy.  The
-- declared costs below are synthetic design/search coordinates: they are not
-- dollars, field effort measurements, probability, ecological value, truth,
-- ethics, or deployment authority.
--
-- species consumer:
--   bulkOnly is excluded by the equal-bulk/different-species collision;
--   speciesSensitive is the minimum eligible observer.
--
-- contextual-classification consumer:
--   speciesSensitive remains too coarse because it erases site/season/window/
--   protocol/uncertainty context;
--   contextualChemistry is the minimum eligible observer.
--
-- multiCoordinatePanel remains available as a richer admissible model but is
-- not automatically preferred merely because it retains more coordinates.
------------------------------------------------------------------------

data ChemistryParetoObserver : Set where
  bulkOnly : ChemistryParetoObserver
  speciesSensitive : ChemistryParetoObserver
  contextualChemistry : ChemistryParetoObserver
  multiCoordinatePanel : ChemistryParetoObserver

observerReference : ChemistryParetoObserver → String
observerReference bulkOnly =
  "bulk concentration only"
observerReference speciesSensitive =
  "bulk concentration plus analyte/species/fraction-sensitive assay"
observerReference contextualChemistry =
  "species-sensitive chemistry plus site/season/window/protocol/uncertainty context"
observerReference multiCoordinatePanel =
  "richer multicoordinate chemistry panel retaining additional declared chemistry/environment coordinates"

observerDescriptionLength : ChemistryParetoObserver → Nat
observerDescriptionLength bulkOnly = 1
observerDescriptionLength speciesSensitive = 2
observerDescriptionLength contextualChemistry = 3
observerDescriptionLength multiCoordinatePanel = 4

allObserversAdmissible : ChemistryParetoObserver → Set
allObserversAdmissible model = ⊤

speciesAdequate : ChemistryParetoObserver → Set
speciesAdequate bulkOnly = ⊥
speciesAdequate speciesSensitive = ⊤
speciesAdequate contextualChemistry = ⊤
speciesAdequate multiCoordinatePanel = ⊤

contextualAdequate : ChemistryParetoObserver → Set
contextualAdequate bulkOnly = ⊥
contextualAdequate speciesSensitive = ⊥
contextualAdequate contextualChemistry = ⊤
contextualAdequate multiCoordinatePanel = ⊤

data ChemistryObserverRefines :
  ChemistryParetoObserver → ChemistryParetoObserver → Set where
  bulkToSpecies : ChemistryObserverRefines bulkOnly speciesSensitive
  speciesToContextual : ChemistryObserverRefines speciesSensitive contextualChemistry
  contextualToPanel : ChemistryObserverRefines contextualChemistry multiCoordinatePanel

------------------------------------------------------------------------
-- Consumer-indexed problems over the same finite observer family.
------------------------------------------------------------------------

speciesProblem : MDL.ConsumerMDLProblem
speciesProblem = MDL.consumerMDLProblem
  ChemistryParetoObserver
  allObserversAdmissible
  speciesAdequate
  observerDescriptionLength
  ChemistryObserverRefines
  observerReference
  "finite repository-local observer code length; not empirical acquisition cost"
  "consumer asks for analyte/species/fraction-sensitive chemistry over the bulk nutrient collision"

contextualProblem : MDL.ConsumerMDLProblem
contextualProblem = MDL.consumerMDLProblem
  ChemistryParetoObserver
  allObserversAdmissible
  contextualAdequate
  observerDescriptionLength
  ChemistryObserverRefines
  observerReference
  "finite repository-local observer code length; not empirical acquisition cost"
  "consumer asks for contextual ecological classification retaining site/season/window/protocol/uncertainty coordinates"

------------------------------------------------------------------------
-- Collision-backed species obstruction.
------------------------------------------------------------------------

speciesCollisionWitness :
  NonFactor.NonFactorabilityWitness
    ChemistryIndex.bulkNutrientObserver
    ChemistryIndex.nitrogenSpeciesConsumer
speciesCollisionWitness = ChemistryIndex.nutrientSpeciesNonFactorabilityWitness

bulkSpeciesCounterexample :
  MDL.ConsumerCounterexample speciesProblem bulkOnly
bulkSpeciesCounterexample = MDL.consumerCounterexample
  (NonFactor.NonFactorabilityWitness
    ChemistryIndex.bulkNutrientObserver
    ChemistryIndex.nitrogenSpeciesConsumer)
  speciesCollisionWitness
  (λ inadequate → inadequate)
  "bulk-only chemistry erases the species distinction exhibited by the retained equal-bulk-mass collision"
  "BiocontrolChemistry369IndexExact.nutrientSpeciesNonFactorabilityWitness"

bulkExcludedFromSpeciesEligibility :
  MDL.Eligible speciesProblem bulkOnly → ⊥
bulkExcludedFromSpeciesEligibility =
  MDL.counterexampleExcludesEligibility bulkSpeciesCounterexample

------------------------------------------------------------------------
-- Existing chemistry local repair is retained as a donor receipt.  The Pareto
-- family makes the intermediate species-sensitive model explicit instead of
-- treating every richer context coordinate as mandatory for every query.
------------------------------------------------------------------------

existingBulkToSpeciatedRepair :
  MDL.LocalRefinementRepair
    ChemistryFibre.chemistryObservationProblem
    ChemistryFibre.bulkOnly
    ChemistryFibre.analyteSpeciesContext
existingBulkToSpeciatedRepair = ChemistryFibre.bulkToSpeciatedRepair

bulkToSpeciesRepair :
  MDL.LocalRefinementRepair speciesProblem bulkOnly speciesSensitive
bulkToSpeciesRepair = MDL.localRefinementRepair
  bulkSpeciesCounterexample
  bulkToSpecies
  tt
  tt
  "retain analyte/species/fraction-sensitive assay coordinates required by the live species consumer"

bulkRepairProvidesSpeciesEligibility :
  MDL.Eligible speciesProblem speciesSensitive
bulkRepairProvidesSpeciesEligibility =
  MDL.repairProvidesEligibleRefinement bulkToSpeciesRepair

------------------------------------------------------------------------
-- The contextual consumer exposes the next local defect.  Species identity is
-- useful but does not by itself pay site/season/window/protocol/uncertainty-
-- indexed ecological classification.
------------------------------------------------------------------------

speciesContextCounterexample :
  MDL.ConsumerCounterexample contextualProblem speciesSensitive
speciesContextCounterexample = MDL.consumerCounterexample
  ⊤
  tt
  (λ inadequate → inadequate)
  "species-sensitive chemistry erases site/season/window/protocol/uncertainty coordinates needed by the contextual classification consumer"
  "BiocontrolCalibratedEcologicalClassificationExact.universalThresholdCounterexample supplies the downstream context-erasure analogue"

speciesExcludedFromContextualEligibility :
  MDL.Eligible contextualProblem speciesSensitive → ⊥
speciesExcludedFromContextualEligibility =
  MDL.counterexampleExcludesEligibility speciesContextCounterexample

speciesToContextualRepair :
  MDL.LocalRefinementRepair
    contextualProblem speciesSensitive contextualChemistry
speciesToContextualRepair = MDL.localRefinementRepair
  speciesContextCounterexample
  speciesToContextual
  tt
  tt
  "retain site, season, sample window, protocol, uncertainty and calibration provenance around the species-sensitive chemistry observation"

contextualRepairProvidesEligibility :
  MDL.Eligible contextualProblem contextualChemistry
contextualRepairProvidesEligibility =
  MDL.repairProvidesEligibleRefinement speciesToContextualRepair

calibrationBoundaryDonor : Calibration.BiocontrolCalibrationBoundary
calibrationBoundaryDonor = Calibration.canonicalBiocontrolCalibrationBoundary

------------------------------------------------------------------------
-- Minimum eligible description, consumer by consumer.
------------------------------------------------------------------------

speciesNoLongerThanAnyEligible :
  (candidate : ChemistryParetoObserver) →
  allObserversAdmissible candidate →
  speciesAdequate candidate →
  observerDescriptionLength speciesSensitive ≤ observerDescriptionLength candidate
speciesNoLongerThanAnyEligible bulkOnly admissible ()
speciesNoLongerThanAnyEligible speciesSensitive admissible adequate = ≤-refl
speciesNoLongerThanAnyEligible contextualChemistry admissible adequate =
  s≤s (s≤s z≤n)
speciesNoLongerThanAnyEligible multiCoordinatePanel admissible adequate =
  s≤s (s≤s z≤n)

speciesMinimalEligible :
  MDL.MinimalEligibleDescription speciesProblem speciesSensitive
speciesMinimalEligible = MDL.minimalEligibleDescription
  tt
  tt
  speciesNoLongerThanAnyEligible
  "speciesSensitive is shortest among observers eligible for the declared species/fraction consumer"

contextualNoLongerThanAnyEligible :
  (candidate : ChemistryParetoObserver) →
  allObserversAdmissible candidate →
  contextualAdequate candidate →
  observerDescriptionLength contextualChemistry ≤ observerDescriptionLength candidate
contextualNoLongerThanAnyEligible bulkOnly admissible ()
contextualNoLongerThanAnyEligible speciesSensitive admissible ()
contextualNoLongerThanAnyEligible contextualChemistry admissible adequate = ≤-refl
contextualNoLongerThanAnyEligible multiCoordinatePanel admissible adequate =
  s≤s (s≤s (s≤s z≤n))

contextualMinimalEligible :
  MDL.MinimalEligibleDescription contextualProblem contextualChemistry
contextualMinimalEligible = MDL.minimalEligibleDescription
  tt
  tt
  contextualNoLongerThanAnyEligible
  "contextualChemistry is shortest among observers eligible for the declared contextual classification consumer"

------------------------------------------------------------------------
-- Multi-axis Pareto costs.  All axes are declared repository-local design
-- coordinates and deliberately monotone along this finite refinement chain.
------------------------------------------------------------------------

data ChemistryCostAxis : Set where
  observerComplexity : ChemistryCostAxis
  contextualBurden : ChemistryCostAxis
  retainedCoordinateCount : ChemistryCostAxis

chemistryCost : ChemistryCostAxis → ChemistryParetoObserver → Nat
chemistryCost observerComplexity bulkOnly = 1
chemistryCost observerComplexity speciesSensitive = 2
chemistryCost observerComplexity contextualChemistry = 3
chemistryCost observerComplexity multiCoordinatePanel = 4
chemistryCost contextualBurden bulkOnly = 0
chemistryCost contextualBurden speciesSensitive = 0
chemistryCost contextualBurden contextualChemistry = 1
chemistryCost contextualBurden multiCoordinatePanel = 2
chemistryCost retainedCoordinateCount bulkOnly = 1
chemistryCost retainedCoordinateCount speciesSensitive = 2
chemistryCost retainedCoordinateCount contextualChemistry = 3
chemistryCost retainedCoordinateCount multiCoordinatePanel = 4

chemistryCostReference : ChemistryCostAxis → String
chemistryCostReference observerComplexity =
  "synthetic observer/assay complexity rank; not money or empirical field effort"
chemistryCostReference contextualBurden =
  "synthetic contextual-information burden rank; not scientific value or authority"
chemistryCostReference retainedCoordinateCount =
  "repository-local retained-coordinate count rank; not physical dimensionality or truth"

speciesCostHyperfabric : MDL.CostHyperfabric speciesProblem
speciesCostHyperfabric =
  MDL.costHyperfabric ChemistryCostAxis chemistryCost chemistryCostReference

contextualCostHyperfabric : MDL.CostHyperfabric contextualProblem
contextualCostHyperfabric =
  MDL.costHyperfabric ChemistryCostAxis chemistryCost chemistryCostReference

speciesNDimParetoView : NDim.NDimParetoView speciesCostHyperfabric
speciesNDimParetoView = NDim.ndimParetoView
  3
  "three declared design axes after species-consumer eligibility"
  chemistryCostReference
  true
  "no scalarized score required"

contextualNDimParetoView : NDim.NDimParetoView contextualCostHyperfabric
contextualNDimParetoView = NDim.ndimParetoView
  3
  "three declared design axes after contextual-consumer eligibility"
  chemistryCostReference
  true
  "no scalarized score required"

------------------------------------------------------------------------
-- Componentwise selected <= every eligible candidate.  Therefore any eligible
-- candidate that weakly dominates the selected observer can only tie it on the
-- declared Pareto order; an ineligible cheap observer never enters ranking.
------------------------------------------------------------------------

speciesSelectedWeaklyDominatesAnyEligible :
  (candidate : ChemistryParetoObserver) →
  allObserversAdmissible candidate →
  speciesAdequate candidate →
  MDL.WeaklyDominates speciesCostHyperfabric speciesSensitive candidate
speciesSelectedWeaklyDominatesAnyEligible bulkOnly admissible ()
speciesSelectedWeaklyDominatesAnyEligible speciesSensitive admissible adequate axis = ≤-refl
speciesSelectedWeaklyDominatesAnyEligible contextualChemistry admissible adequate observerComplexity =
  s≤s (s≤s z≤n)
speciesSelectedWeaklyDominatesAnyEligible contextualChemistry admissible adequate contextualBurden =
  z≤n
speciesSelectedWeaklyDominatesAnyEligible contextualChemistry admissible adequate retainedCoordinateCount =
  s≤s (s≤s z≤n)
speciesSelectedWeaklyDominatesAnyEligible multiCoordinatePanel admissible adequate observerComplexity =
  s≤s (s≤s z≤n)
speciesSelectedWeaklyDominatesAnyEligible multiCoordinatePanel admissible adequate contextualBurden =
  z≤n
speciesSelectedWeaklyDominatesAnyEligible multiCoordinatePanel admissible adequate retainedCoordinateCount =
  s≤s (s≤s z≤n)

speciesParetoAdmissible :
  MDL.ParetoAdmissible speciesCostHyperfabric speciesSensitive
speciesParetoAdmissible = MDL.paretoAdmissible
  (tt , tt)
  (λ candidate eligible candidateDominates →
    speciesSelectedWeaklyDominatesAnyEligible
      candidate (proj₁ eligible) (proj₂ eligible))
  "speciesSensitive is Pareto-admissible after excluding consumer-inadequate bulkOnly; richer panels do not beat it on the declared monotone design axes"

contextualSelectedWeaklyDominatesAnyEligible :
  (candidate : ChemistryParetoObserver) →
  allObserversAdmissible candidate →
  contextualAdequate candidate →
  MDL.WeaklyDominates contextualCostHyperfabric contextualChemistry candidate
contextualSelectedWeaklyDominatesAnyEligible bulkOnly admissible ()
contextualSelectedWeaklyDominatesAnyEligible speciesSensitive admissible ()
contextualSelectedWeaklyDominatesAnyEligible contextualChemistry admissible adequate axis = ≤-refl
contextualSelectedWeaklyDominatesAnyEligible multiCoordinatePanel admissible adequate observerComplexity =
  s≤s (s≤s (s≤s z≤n))
contextualSelectedWeaklyDominatesAnyEligible multiCoordinatePanel admissible adequate contextualBurden =
  s≤s z≤n
contextualSelectedWeaklyDominatesAnyEligible multiCoordinatePanel admissible adequate retainedCoordinateCount =
  s≤s (s≤s (s≤s z≤n))

contextualParetoAdmissible :
  MDL.ParetoAdmissible contextualCostHyperfabric contextualChemistry
contextualParetoAdmissible = MDL.paretoAdmissible
  (tt , tt)
  (λ candidate eligible candidateDominates →
    contextualSelectedWeaklyDominatesAnyEligible
      candidate (proj₁ eligible) (proj₂ eligible))
  "contextualChemistry is Pareto-admissible after excluding bulkOnly and speciesSensitive for the contextual classification consumer"

------------------------------------------------------------------------
-- Local observer neighbourhood.  The two repairs remain inside the declared
-- chemistry-observer family; no unrelated model is silently substituted.
------------------------------------------------------------------------

data ChemistryObserverAddress : Set where
  aquaticChemistryParetoFamily : ChemistryObserverAddress

speciesNeighbourhood : MDL.RefinementNeighbourhood speciesProblem
speciesNeighbourhood = MDL.refinementNeighbourhood
  ChemistryObserverAddress
  (λ model → aquaticChemistryParetoFamily)
  (λ left right → ⊤)
  (λ coarse fine refinement → tt)
  "finite chemistry Pareto family: bulk -> species -> contextual -> richer panel"

contextualNeighbourhood : MDL.RefinementNeighbourhood contextualProblem
contextualNeighbourhood = MDL.refinementNeighbourhood
  ChemistryObserverAddress
  (λ model → aquaticChemistryParetoFamily)
  (λ left right → ⊤)
  (λ coarse fine refinement → tt)
  "finite chemistry Pareto family: bulk -> species -> contextual -> richer panel"

bulkRepairStaysLocal :
  MDL.sameNeighbourhood speciesNeighbourhood
    (MDL.address speciesNeighbourhood bulkOnly)
    (MDL.address speciesNeighbourhood speciesSensitive)
bulkRepairStaysLocal =
  MDL.repairStaysInDeclaredNeighbourhood speciesNeighbourhood bulkToSpeciesRepair

contextualRepairStaysLocal :
  MDL.sameNeighbourhood contextualNeighbourhood
    (MDL.address contextualNeighbourhood speciesSensitive)
    (MDL.address contextualNeighbourhood contextualChemistry)
contextualRepairStaysLocal =
  MDL.repairStaysInDeclaredNeighbourhood
    contextualNeighbourhood speciesToContextualRepair

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record BiocontrolChemistryObserverParetoBoundary : Set where
  constructor biocontrolChemistryObserverParetoBoundary
  field
    bulkOnlyEligibleForSpeciesConsumer : Bool
    bulkOnlyEligibleForSpeciesConsumerIsFalse :
      bulkOnlyEligibleForSpeciesConsumer ≡ false

    speciesSensitiveIsMinimalEligibleForSpeciesConsumer : Bool
    speciesSensitiveIsMinimalEligibleForSpeciesConsumerIsTrue :
      speciesSensitiveIsMinimalEligibleForSpeciesConsumer ≡ true

    richerPanelAutomaticallyPreferredForSpeciesConsumer : Bool
    richerPanelAutomaticallyPreferredForSpeciesConsumerIsFalse :
      richerPanelAutomaticallyPreferredForSpeciesConsumer ≡ false

    speciesSensitiveEligibleForContextualConsumer : Bool
    speciesSensitiveEligibleForContextualConsumerIsFalse :
      speciesSensitiveEligibleForContextualConsumer ≡ false

    contextualChemistryIsMinimalEligibleForContextualConsumer : Bool
    contextualChemistryIsMinimalEligibleForContextualConsumerIsTrue :
      contextualChemistryIsMinimalEligibleForContextualConsumer ≡ true

    eligibilityPrecedesParetoRanking : Bool
    eligibilityPrecedesParetoRankingIsTrue :
      eligibilityPrecedesParetoRanking ≡ true

    moreCoordinatesImproveEveryConsumer : Bool
    moreCoordinatesImproveEveryConsumerIsFalse :
      moreCoordinatesImproveEveryConsumer ≡ false

    paretoAxesAreEmpiricalFieldCosts : Bool
    paretoAxesAreEmpiricalFieldCostsIsFalse :
      paretoAxesAreEmpiricalFieldCosts ≡ false

    paretoSelectionCreatesDeploymentAuthority : Bool
    paretoSelectionCreatesDeploymentAuthorityIsFalse :
      paretoSelectionCreatesDeploymentAuthority ≡ false

    localRepairInventsChemicalMeasurement : Bool
    localRepairInventsChemicalMeasurementIsFalse :
      localRepairInventsChemicalMeasurement ≡ false

canonicalBiocontrolChemistryObserverParetoBoundary :
  BiocontrolChemistryObserverParetoBoundary
canonicalBiocontrolChemistryObserverParetoBoundary =
  biocontrolChemistryObserverParetoBoundary
    false refl
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
