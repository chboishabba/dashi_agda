module DASHI.Environment.BiocontrolChemistryParetoExperimentSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Planner
import DASHI.Environment.BiocontrolChemistry369IndexExact as ChemistryIndex
import DASHI.Environment.BiocontrolChemistryActiveDiscriminatorExact as Active
import DASHI.Environment.BiocontrolChemistryObserverParetoExact as Pareto

------------------------------------------------------------------------
-- PARETO OBSERVER -> MINIMAL ASSAY SCHEDULER
--
-- This owner closes the seam between observer selection and experiment
-- acquisition.  The order is intentionally fail-closed:
--
--   consumer collision
--     -> eligible observer family
--     -> consumer-indexed Pareto selection
--     -> declared experiment family for that selected observer
--     -> minimum collision-separating bundle
--     -> realised observation fibre.
--
-- The experiment costs and finite worlds below are DASHI synthesis.  External
-- sources retain only their source-bounded empirical/domain premises.  In
-- particular, BIPM owns SI semantics, ecology/chemistry sources own the claims
-- actually present in those sources, and Ipswich City Council owns only the
-- Springfield Lakes salvinia operational record.  None of those sources is
-- attributed with the DASHI finite collision, local repair, Pareto order,
-- minimal-bundle theorem, or synthetic context fixture.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Species/fraction consumer: the selected Pareto observer requests only the
-- missing species-sensitive assay needed to separate the retained live
-- equal-bulk-mass collision.  A richer species+pH panel is declared but loses
-- on the repository-local bundle-cost axis for this consumer.
------------------------------------------------------------------------

speciesObserverParetoReceipt :
  MDL.ParetoAdmissible Pareto.speciesCostHyperfabric Pareto.speciesSensitive
speciesObserverParetoReceipt = Pareto.speciesParetoAdmissible

speciesExistingObserver :
  ChemistryIndex.AquaticChemistryWorld → ChemistryIndex.BulkNutrientMassClass
speciesExistingObserver = ChemistryIndex.bulkNutrientObserver

speciesCollision : Synthesis.CurrentObserverCollision speciesExistingObserver
speciesCollision = Synthesis.currentObserverCollision
  ChemistryIndex.nitrateWorld
  ChemistryIndex.ammoniumWorld
  refl

speciesExperimentBundle :
  Synthesis.ExperimentBundle ChemistryIndex.AquaticChemistryWorld
speciesExperimentBundle = Active.speciesExperimentBundle

speciesPlusPHBundle :
  Synthesis.ExperimentBundle ChemistryIndex.AquaticChemistryWorld
speciesPlusPHBundle = Synthesis.experimentBundle
  (ChemistryIndex.NitrogenSpeciesState × ChemistryIndex.PHContext)
  (λ world → ChemistryIndex.nitrogenSpecies world , ChemistryIndex.pHContext world)
  2
  "species/fraction assay plus pH context panel"
  "both measurements require source-bound assay/sensor protocol, site/time identity and provenance"

data SpeciesDeclaredBundle :
  Synthesis.ExperimentBundle ChemistryIndex.AquaticChemistryWorld → Set where
  speciesOnlyDeclared : SpeciesDeclaredBundle speciesExperimentBundle
  speciesPlusPHDeclared : SpeciesDeclaredBundle speciesPlusPHBundle

speciesOnlySeparates :
  Synthesis.BundleSeparates
    speciesExperimentBundle
    ChemistryIndex.nitrateWorld
    ChemistryIndex.ammoniumWorld
speciesOnlySeparates = Active.speciesBundleSeparatesCollision

speciesPlusPHSeparates :
  Synthesis.BundleSeparates
    speciesPlusPHBundle
    ChemistryIndex.nitrateWorld
    ChemistryIndex.ammoniumWorld
speciesPlusPHSeparates = Synthesis.bundleSeparates (λ ())

speciesBundleMinimalCost :
  (alternative : Synthesis.ExperimentBundle ChemistryIndex.AquaticChemistryWorld) →
  SpeciesDeclaredBundle alternative →
  Synthesis.BundleSeparates
    alternative ChemistryIndex.nitrateWorld ChemistryIndex.ammoniumWorld →
  Synthesis.cost speciesExperimentBundle ≤ Synthesis.cost alternative
speciesBundleMinimalCost .speciesExperimentBundle speciesOnlyDeclared separates = ≤-refl
speciesBundleMinimalCost .speciesPlusPHBundle speciesPlusPHDeclared separates =
  s≤s z≤n

speciesMinimalDiscriminator :
  Synthesis.MinimalDiscriminator speciesExistingObserver SpeciesDeclaredBundle
speciesMinimalDiscriminator = Synthesis.minimalDiscriminator
  speciesCollision
  speciesExperimentBundle
  speciesOnlyDeclared
  speciesOnlySeparates
  speciesBundleMinimalCost
  "Pareto-selected speciesSensitive observer schedules the minimum declared species-sensitive assay that separates the retained bulk-mass collision; the richer species+pH panel is unnecessary for this consumer"

speciesAllHypothesesLive : ChemistryIndex.AquaticChemistryWorld → Set
speciesAllHypothesesLive world = ⊤

speciesObservedFibre : ChemistryIndex.AquaticChemistryWorld → Set
speciesObservedFibre = Planner.RefineByBundle
  speciesAllHypothesesLive
  speciesExperimentBundle
  ChemistryIndex.nitrateDominant

speciesNitrateWorld : ChemistryIndex.AquaticChemistryWorld
speciesNitrateWorld = ChemistryIndex.nitrateWorld

speciesNitrateWorldRemainsLive : speciesObservedFibre speciesNitrateWorld
speciesNitrateWorldRemainsLive = tt , refl

------------------------------------------------------------------------
-- Contextual-classification consumer.
--
-- The synthetic worlds below deliberately share the same chemistry state and
-- differ only in a retained contextual-classification key.  They are not field
-- observations from Springfield Lakes or any other site.  Their purpose is to
-- witness the next projection defect after species identity has already been
-- retained: site/season/window/protocol/uncertainty context can still matter.
------------------------------------------------------------------------

data ContextClassificationKey : Set where
  declaredContextA declaredContextB : ContextClassificationKey

record ContextualChemistryWorld : Set where
  constructor contextualChemistryWorld
  field
    chemistryWorld : ChemistryIndex.AquaticChemistryWorld
    contextKey : ContextClassificationKey

open ContextualChemistryWorld public

contextDryWorld : ContextualChemistryWorld
contextDryWorld = contextualChemistryWorld
  ChemistryIndex.nitrateWorld
  declaredContextA

contextWetWorld : ContextualChemistryWorld
contextWetWorld = contextualChemistryWorld
  ChemistryIndex.nitrateWorld
  declaredContextB

contextualObserverParetoReceipt :
  MDL.ParetoAdmissible
    Pareto.contextualCostHyperfabric Pareto.contextualChemistry
contextualObserverParetoReceipt = Pareto.contextualParetoAdmissible

contextExistingObserver :
  ContextualChemistryWorld → ChemistryIndex.NitrogenSpeciesState
contextExistingObserver world =
  ChemistryIndex.nitrogenSpecies (chemistryWorld world)

contextCollision : Synthesis.CurrentObserverCollision contextExistingObserver
contextCollision = Synthesis.currentObserverCollision
  contextDryWorld
  contextWetWorld
  refl

contextExperimentBundle :
  Synthesis.ExperimentBundle ContextualChemistryWorld
contextExperimentBundle = Synthesis.experimentBundle
  ContextClassificationKey
  contextKey
  2
  "context bundle retaining the missing site/season/window/protocol/uncertainty classification key"
  "context coordinates require their own source/protocol/calibration provenance; this finite key is DASHI synthesis, not an acquired field value"

contextFullPanelBundle :
  Synthesis.ExperimentBundle ContextualChemistryWorld
contextFullPanelBundle = Synthesis.experimentBundle
  ((ChemistryIndex.NitrogenSpeciesState × ChemistryIndex.PHContext) × ContextClassificationKey)
  (λ world →
    ( ChemistryIndex.nitrogenSpecies (chemistryWorld world)
    , ChemistryIndex.pHContext (chemistryWorld world)
    )
    , contextKey world)
  4
  "richer chemistry plus contextual-classification panel"
  "all physical and contextual coordinates require separately attributed acquisition/calibration receipts"

data ContextDeclaredBundle :
  Synthesis.ExperimentBundle ContextualChemistryWorld → Set where
  contextOnlyDeclared : ContextDeclaredBundle contextExperimentBundle
  contextFullPanelDeclared : ContextDeclaredBundle contextFullPanelBundle

contextBundleSeparates :
  Synthesis.BundleSeparates contextExperimentBundle contextDryWorld contextWetWorld
contextBundleSeparates = Synthesis.bundleSeparates (λ ())

contextFullPanelSeparates :
  Synthesis.BundleSeparates contextFullPanelBundle contextDryWorld contextWetWorld
contextFullPanelSeparates = Synthesis.bundleSeparates (λ ())

contextBundleMinimalCost :
  (alternative : Synthesis.ExperimentBundle ContextualChemistryWorld) →
  ContextDeclaredBundle alternative →
  Synthesis.BundleSeparates alternative contextDryWorld contextWetWorld →
  Synthesis.cost contextExperimentBundle ≤ Synthesis.cost alternative
contextBundleMinimalCost .contextExperimentBundle contextOnlyDeclared separates = ≤-refl
contextBundleMinimalCost .contextFullPanelBundle contextFullPanelDeclared separates =
  s≤s (s≤s z≤n)

contextMinimalDiscriminator :
  Synthesis.MinimalDiscriminator contextExistingObserver ContextDeclaredBundle
contextMinimalDiscriminator = Synthesis.minimalDiscriminator
  contextCollision
  contextExperimentBundle
  contextOnlyDeclared
  contextBundleSeparates
  contextBundleMinimalCost
  "Pareto-selected contextualChemistry observer schedules the minimum declared context bundle needed to separate the retained contextual collision; already-known species information is not reacquired by default"

contextAllHypothesesLive : ContextualChemistryWorld → Set
contextAllHypothesesLive world = ⊤

contextObservedFibre : ContextualChemistryWorld → Set
contextObservedFibre = Planner.RefineByBundle
  contextAllHypothesesLive
  contextExperimentBundle
  declaredContextA

contextDryWorldRemainsLive : contextObservedFibre contextDryWorld
contextDryWorldRemainsLive = tt , refl

------------------------------------------------------------------------
-- End-to-end scheduler receipts.
------------------------------------------------------------------------

record SpeciesParetoScheduledExperiment : Set₁ where
  constructor speciesParetoScheduledExperiment
  field
    selectedObserver : Pareto.ChemistryParetoObserver
    observerIsSpeciesSensitive : selectedObserver ≡ Pareto.speciesSensitive
    observerPareto :
      MDL.ParetoAdmissible Pareto.speciesCostHyperfabric Pareto.speciesSensitive
    minimalAssay :
      Synthesis.MinimalDiscriminator speciesExistingObserver SpeciesDeclaredBundle
    realisedFibre : speciesObservedFibre speciesNitrateWorld
    schedulerReference : String

canonicalSpeciesParetoScheduledExperiment : SpeciesParetoScheduledExperiment
canonicalSpeciesParetoScheduledExperiment = speciesParetoScheduledExperiment
  Pareto.speciesSensitive
  refl
  speciesObserverParetoReceipt
  speciesMinimalDiscriminator
  speciesNitrateWorldRemainsLive
  "species consumer -> eligible/Pareto speciesSensitive observer -> minimum declared species assay -> nitrate-valued refined live fibre"

record ContextParetoScheduledExperiment : Set₁ where
  constructor contextParetoScheduledExperiment
  field
    selectedObserver : Pareto.ChemistryParetoObserver
    observerIsContextualChemistry : selectedObserver ≡ Pareto.contextualChemistry
    observerPareto :
      MDL.ParetoAdmissible
        Pareto.contextualCostHyperfabric Pareto.contextualChemistry
    minimalAssay :
      Synthesis.MinimalDiscriminator contextExistingObserver ContextDeclaredBundle
    realisedFibre : contextObservedFibre contextDryWorld
    schedulerReference : String

canonicalContextParetoScheduledExperiment : ContextParetoScheduledExperiment
canonicalContextParetoScheduledExperiment = contextParetoScheduledExperiment
  Pareto.contextualChemistry
  refl
  contextualObserverParetoReceipt
  contextMinimalDiscriminator
  contextDryWorldRemainsLive
  "contextual classification consumer -> eligible/Pareto contextualChemistry observer -> minimum missing-context bundle -> context-refined live fibre"

------------------------------------------------------------------------
-- Attribution / promotion boundary.
------------------------------------------------------------------------

record BiocontrolChemistryParetoSchedulerBoundary : Set where
  constructor biocontrolChemistryParetoSchedulerBoundary
  field
    observerSelectionPrecedesBundleRanking : Bool
    observerSelectionPrecedesBundleRankingIsTrue :
      observerSelectionPrecedesBundleRanking ≡ true

    cheaperInadequateObserverMayScheduleExperiment : Bool
    cheaperInadequateObserverMayScheduleExperimentIsFalse :
      cheaperInadequateObserverMayScheduleExperiment ≡ false

    richerPanelAutomaticallyPreferred : Bool
    richerPanelAutomaticallyPreferredIsFalse :
      richerPanelAutomaticallyPreferred ≡ false

    bundleCostIsEmpiricalFieldCost : Bool
    bundleCostIsEmpiricalFieldCostIsFalse :
      bundleCostIsEmpiricalFieldCost ≡ false

    selectedBundleInventsMeasurement : Bool
    selectedBundleInventsMeasurementIsFalse :
      selectedBundleInventsMeasurement ≡ false

    selectedBundleCreatesDeploymentAuthority : Bool
    selectedBundleCreatesDeploymentAuthorityIsFalse :
      selectedBundleCreatesDeploymentAuthority ≡ false

    externalSourcesOwnDashiFiniteSchedulerTheorems : Bool
    externalSourcesOwnDashiFiniteSchedulerTheoremsIsFalse :
      externalSourcesOwnDashiFiniteSchedulerTheorems ≡ false

    crossPollinationTransfersAuthorshipOrEmpiricalStatus : Bool
    crossPollinationTransfersAuthorshipOrEmpiricalStatusIsFalse :
      crossPollinationTransfersAuthorshipOrEmpiricalStatus ≡ false

    bipmRoleRemainsMetrologyOnly : Bool
    bipmRoleRemainsMetrologyOnlyIsTrue :
      bipmRoleRemainsMetrologyOnly ≡ true

    ipswichRoleRemainsSalviniaOperationalOnly : Bool
    ipswichRoleRemainsSalviniaOperationalOnlyIsTrue :
      ipswichRoleRemainsSalviniaOperationalOnly ≡ true

    syntheticContextFixtureIsSpringfieldObservation : Bool
    syntheticContextFixtureIsSpringfieldObservationIsFalse :
      syntheticContextFixtureIsSpringfieldObservation ≡ false

canonicalBiocontrolChemistryParetoSchedulerBoundary :
  BiocontrolChemistryParetoSchedulerBoundary
canonicalBiocontrolChemistryParetoSchedulerBoundary =
  biocontrolChemistryParetoSchedulerBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl

attributionReading : String
attributionReading =
  "External sources remain source-bounded: BIPM pays SI semantics; ecology/chemistry/government sources pay only their acquired empirical or operational premises; Ipswich City Council pays only the Springfield Lakes salvinia equipment/access record. DASHI owns the finite observer family, synthetic worlds, collision witnesses, local repairs, Pareto axes/order, minimal-discriminator proofs and scheduler weld. Citation imports neither proof nor authority, and cross-pollination transfers structure rather than authorship or empirical status."
