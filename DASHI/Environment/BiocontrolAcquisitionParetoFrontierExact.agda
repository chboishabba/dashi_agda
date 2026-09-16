module DASHI.Environment.BiocontrolAcquisitionParetoFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Core.EvidenceAcquisitionSelectiveReopeningExact as Acquisition
import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Environment.BiocontrolChemistryAcquisitionPromotionExact as Promotion

------------------------------------------------------------------------
-- ACQUISITION PARETO FRONTIER
--
-- The scheduler and promotion owner can leave multiple targeted acquisition
-- obligations open.  This owner ranks only provenance-admissible acquisition
-- packages for one declared consumer at a time.
--
-- The candidate family, synthetic costs, Pareto order and dependency graph are
-- DASHI synthesis.  They are not empirical field costs, source authority,
-- probabilities, ecological values, or observations.  External sources remain
-- responsible only for the source-bounded records they actually provide.
------------------------------------------------------------------------

data AcquisitionCandidate : Set where
  metadataOnlyShortcut : AcquisitionCandidate
  speciesQualifiedPackage : AcquisitionCandidate
  contextQualifiedPackage : AcquisitionCandidate
  combinedQualifiedPanel : AcquisitionCandidate

candidateReference : AcquisitionCandidate → String
candidateReference metadataOnlyShortcut =
  "metadata-only shortcut lacking the required source/sample/protocol/value qualification"
candidateReference speciesQualifiedPackage =
  "species/fraction acquisition package with source/site/sample/time/protocol/uncertainty lineage"
candidateReference contextQualifiedPackage =
  "context acquisition package with site/season/window/protocol/uncertainty lineage"
candidateReference combinedQualifiedPanel =
  "combined species plus context acquisition package"

candidateDescriptionLength : AcquisitionCandidate → Nat
candidateDescriptionLength metadataOnlyShortcut = 1
candidateDescriptionLength speciesQualifiedPackage = 2
candidateDescriptionLength contextQualifiedPackage = 2
candidateDescriptionLength combinedQualifiedPanel = 4

AcquisitionAdmissible : AcquisitionCandidate → Set
AcquisitionAdmissible metadataOnlyShortcut = ⊥
AcquisitionAdmissible speciesQualifiedPackage = ⊤
AcquisitionAdmissible contextQualifiedPackage = ⊤
AcquisitionAdmissible combinedQualifiedPanel = ⊤

SpeciesAcquisitionAdequate : AcquisitionCandidate → Set
SpeciesAcquisitionAdequate metadataOnlyShortcut = ⊥
SpeciesAcquisitionAdequate speciesQualifiedPackage = ⊤
SpeciesAcquisitionAdequate contextQualifiedPackage = ⊥
SpeciesAcquisitionAdequate combinedQualifiedPanel = ⊤

ContextAcquisitionAdequate : AcquisitionCandidate → Set
ContextAcquisitionAdequate metadataOnlyShortcut = ⊥
ContextAcquisitionAdequate speciesQualifiedPackage = ⊥
ContextAcquisitionAdequate contextQualifiedPackage = ⊤
ContextAcquisitionAdequate combinedQualifiedPanel = ⊤

data AcquisitionRefines : AcquisitionCandidate → AcquisitionCandidate → Set where
  metadataToSpecies : AcquisitionRefines metadataOnlyShortcut speciesQualifiedPackage
  metadataToContext : AcquisitionRefines metadataOnlyShortcut contextQualifiedPackage
  speciesToCombined : AcquisitionRefines speciesQualifiedPackage combinedQualifiedPanel
  contextToCombined : AcquisitionRefines contextQualifiedPackage combinedQualifiedPanel

speciesAcquisitionProblem : MDL.ConsumerMDLProblem
speciesAcquisitionProblem = MDL.consumerMDLProblem
  AcquisitionCandidate
  AcquisitionAdmissible
  SpeciesAcquisitionAdequate
  candidateDescriptionLength
  AcquisitionRefines
  candidateReference
  "repository-local acquisition package code length; not money or measured field effort"
  "acquire the next source/protocol-qualified record needed by the species/fraction consumer"

contextAcquisitionProblem : MDL.ConsumerMDLProblem
contextAcquisitionProblem = MDL.consumerMDLProblem
  AcquisitionCandidate
  AcquisitionAdmissible
  ContextAcquisitionAdequate
  candidateDescriptionLength
  AcquisitionRefines
  candidateReference
  "repository-local acquisition package code length; not money or measured field effort"
  "acquire the next source/protocol-qualified record needed by the contextual-classification consumer"

------------------------------------------------------------------------
-- Open obligations inherited from the promotion owner.  Their existence does
-- not mean the corresponding records have been acquired.
------------------------------------------------------------------------

speciesOpenObligation :
  Acquisition.AcquisitionObligation Promotion.speciesAssayAcquisitionTarget
speciesOpenObligation = Promotion.speciesAssayAcquisitionObligation

contextOpenObligation :
  Acquisition.AcquisitionObligation Promotion.contextAcquisitionTarget
contextOpenObligation = Promotion.contextAcquisitionObligation

------------------------------------------------------------------------
-- The superficially shortest shortcut is excluded before ranking because it
-- lacks the provenance/protocol/value qualification required for promotion.
------------------------------------------------------------------------

metadataSpeciesCounterexample :
  MDL.ConsumerCounterexample speciesAcquisitionProblem metadataOnlyShortcut
metadataSpeciesCounterexample = MDL.consumerCounterexample
  ⊤
  tt
  (λ adequate → adequate)
  "metadata-only acquisition erases the species/fraction observation-value and source/protocol qualification needed by the consumer"
  "BiocontrolChemistryAcquisitionPromotionExact.QualifiedObservation requires source, protocol, value, same-object and non-synthetic payment"

metadataContextCounterexample :
  MDL.ConsumerCounterexample contextAcquisitionProblem metadataOnlyShortcut
metadataContextCounterexample = MDL.consumerCounterexample
  ⊤
  tt
  (λ adequate → adequate)
  "metadata-only acquisition erases the contextual record and its source/protocol qualification"
  "BiocontrolChemistryAcquisitionPromotionExact.QualifiedObservation promotion gate"

metadataShortcutExcludedFromSpecies :
  MDL.Eligible speciesAcquisitionProblem metadataOnlyShortcut → ⊥
metadataShortcutExcludedFromSpecies eligible = proj₁ eligible

metadataShortcutExcludedFromContext :
  MDL.Eligible contextAcquisitionProblem metadataOnlyShortcut → ⊥
metadataShortcutExcludedFromContext eligible = proj₁ eligible

metadataToSpeciesRepair :
  MDL.LocalRefinementRepair
    speciesAcquisitionProblem metadataOnlyShortcut speciesQualifiedPackage
metadataToSpeciesRepair = MDL.localRefinementRepair
  metadataSpeciesCounterexample
  metadataToSpecies
  tt
  tt
  "pay source/site/sample/time/protocol/uncertainty and species/fraction value coordinates before the species acquisition candidate enters the eligible frontier"

metadataToContextRepair :
  MDL.LocalRefinementRepair
    contextAcquisitionProblem metadataOnlyShortcut contextQualifiedPackage
metadataToContextRepair = MDL.localRefinementRepair
  metadataContextCounterexample
  metadataToContext
  tt
  tt
  "pay source/site/time/protocol/uncertainty and contextual-value coordinates before the context acquisition candidate enters the eligible frontier"

------------------------------------------------------------------------
-- Minimum eligible next acquisition, consumer by consumer.
------------------------------------------------------------------------

speciesNoLongerThanAnyEligible :
  (candidate : AcquisitionCandidate) →
  AcquisitionAdmissible candidate →
  SpeciesAcquisitionAdequate candidate →
  candidateDescriptionLength speciesQualifiedPackage ≤ candidateDescriptionLength candidate
speciesNoLongerThanAnyEligible metadataOnlyShortcut () adequate
speciesNoLongerThanAnyEligible speciesQualifiedPackage admissible adequate = ≤-refl
speciesNoLongerThanAnyEligible contextQualifiedPackage admissible ()
speciesNoLongerThanAnyEligible combinedQualifiedPanel admissible adequate =
  s≤s (s≤s z≤n)

speciesMinimalNextAcquisition :
  MDL.MinimalEligibleDescription speciesAcquisitionProblem speciesQualifiedPackage
speciesMinimalNextAcquisition = MDL.minimalEligibleDescription
  tt
  tt
  speciesNoLongerThanAnyEligible
  "speciesQualifiedPackage is the minimum eligible next acquisition for the species/fraction consumer"

contextNoLongerThanAnyEligible :
  (candidate : AcquisitionCandidate) →
  AcquisitionAdmissible candidate →
  ContextAcquisitionAdequate candidate →
  candidateDescriptionLength contextQualifiedPackage ≤ candidateDescriptionLength candidate
contextNoLongerThanAnyEligible metadataOnlyShortcut () adequate
contextNoLongerThanAnyEligible speciesQualifiedPackage admissible ()
contextNoLongerThanAnyEligible contextQualifiedPackage admissible adequate = ≤-refl
contextNoLongerThanAnyEligible combinedQualifiedPanel admissible adequate =
  s≤s (s≤s z≤n)

contextMinimalNextAcquisition :
  MDL.MinimalEligibleDescription contextAcquisitionProblem contextQualifiedPackage
contextMinimalNextAcquisition = MDL.minimalEligibleDescription
  tt
  tt
  contextNoLongerThanAnyEligible
  "contextQualifiedPackage is the minimum eligible next acquisition for the contextual-classification consumer"

------------------------------------------------------------------------
-- Multi-axis synthetic acquisition Pareto costs.
--
-- Lower is better on each declared axis.  `provenanceDeficit` makes explicit
-- that an unqualified shortcut is not merely a cheap version of a qualified
-- record; in any case it is excluded by hard admissibility before Pareto rank.
------------------------------------------------------------------------

data AcquisitionCostAxis : Set where
  acquisitionBurden : AcquisitionCostAxis
  provenanceDeficit : AcquisitionCostAxis
  redundantCoordinateBurden : AcquisitionCostAxis
  remainingConsumerGap : AcquisitionCostAxis

speciesAcquisitionCost : AcquisitionCostAxis → AcquisitionCandidate → Nat
speciesAcquisitionCost acquisitionBurden metadataOnlyShortcut = 0
speciesAcquisitionCost acquisitionBurden speciesQualifiedPackage = 1
speciesAcquisitionCost acquisitionBurden contextQualifiedPackage = 1
speciesAcquisitionCost acquisitionBurden combinedQualifiedPanel = 3
speciesAcquisitionCost provenanceDeficit metadataOnlyShortcut = 2
speciesAcquisitionCost provenanceDeficit speciesQualifiedPackage = 0
speciesAcquisitionCost provenanceDeficit contextQualifiedPackage = 0
speciesAcquisitionCost provenanceDeficit combinedQualifiedPanel = 0
speciesAcquisitionCost redundantCoordinateBurden metadataOnlyShortcut = 0
speciesAcquisitionCost redundantCoordinateBurden speciesQualifiedPackage = 0
speciesAcquisitionCost redundantCoordinateBurden contextQualifiedPackage = 0
speciesAcquisitionCost redundantCoordinateBurden combinedQualifiedPanel = 2
speciesAcquisitionCost remainingConsumerGap metadataOnlyShortcut = 1
speciesAcquisitionCost remainingConsumerGap speciesQualifiedPackage = 0
speciesAcquisitionCost remainingConsumerGap contextQualifiedPackage = 1
speciesAcquisitionCost remainingConsumerGap combinedQualifiedPanel = 0

contextAcquisitionCost : AcquisitionCostAxis → AcquisitionCandidate → Nat
contextAcquisitionCost acquisitionBurden metadataOnlyShortcut = 0
contextAcquisitionCost acquisitionBurden speciesQualifiedPackage = 1
contextAcquisitionCost acquisitionBurden contextQualifiedPackage = 1
contextAcquisitionCost acquisitionBurden combinedQualifiedPanel = 3
contextAcquisitionCost provenanceDeficit metadataOnlyShortcut = 2
contextAcquisitionCost provenanceDeficit speciesQualifiedPackage = 0
contextAcquisitionCost provenanceDeficit contextQualifiedPackage = 0
contextAcquisitionCost provenanceDeficit combinedQualifiedPanel = 0
contextAcquisitionCost redundantCoordinateBurden metadataOnlyShortcut = 0
contextAcquisitionCost redundantCoordinateBurden speciesQualifiedPackage = 0
contextAcquisitionCost redundantCoordinateBurden contextQualifiedPackage = 0
contextAcquisitionCost redundantCoordinateBurden combinedQualifiedPanel = 2
contextAcquisitionCost remainingConsumerGap metadataOnlyShortcut = 1
contextAcquisitionCost remainingConsumerGap speciesQualifiedPackage = 1
contextAcquisitionCost remainingConsumerGap contextQualifiedPackage = 0
contextAcquisitionCost remainingConsumerGap combinedQualifiedPanel = 0

acquisitionAxisReference : AcquisitionCostAxis → String
acquisitionAxisReference acquisitionBurden =
  "synthetic acquisition/search burden rank; not money, labour hours or measured field effort"
acquisitionAxisReference provenanceDeficit =
  "count-like synthetic provenance deficit; not source credibility or truth probability"
acquisitionAxisReference redundantCoordinateBurden =
  "synthetic burden for coordinates unnecessary to the declared consumer"
acquisitionAxisReference remainingConsumerGap =
  "synthetic remaining consumer-information gap; not ecological value or expected utility"

speciesAcquisitionCosts : MDL.CostHyperfabric speciesAcquisitionProblem
speciesAcquisitionCosts =
  MDL.costHyperfabric AcquisitionCostAxis speciesAcquisitionCost acquisitionAxisReference

contextAcquisitionCosts : MDL.CostHyperfabric contextAcquisitionProblem
contextAcquisitionCosts =
  MDL.costHyperfabric AcquisitionCostAxis contextAcquisitionCost acquisitionAxisReference

speciesAcquisitionNDimView : NDim.NDimParetoView speciesAcquisitionCosts
speciesAcquisitionNDimView = NDim.ndimParetoView
  4
  "four repository-local acquisition-design axes after hard provenance admissibility"
  acquisitionAxisReference
  true
  "no scalar acquisition score required"

contextAcquisitionNDimView : NDim.NDimParetoView contextAcquisitionCosts
contextAcquisitionNDimView = NDim.ndimParetoView
  4
  "four repository-local acquisition-design axes after hard provenance admissibility"
  acquisitionAxisReference
  true
  "no scalar acquisition score required"

speciesSelectedWeaklyDominatesAnyEligible :
  (candidate : AcquisitionCandidate) →
  AcquisitionAdmissible candidate →
  SpeciesAcquisitionAdequate candidate →
  MDL.WeaklyDominates speciesAcquisitionCosts speciesQualifiedPackage candidate
speciesSelectedWeaklyDominatesAnyEligible metadataOnlyShortcut () adequate
speciesSelectedWeaklyDominatesAnyEligible speciesQualifiedPackage admissible adequate axis = ≤-refl
speciesSelectedWeaklyDominatesAnyEligible contextQualifiedPackage admissible ()
speciesSelectedWeaklyDominatesAnyEligible combinedQualifiedPanel admissible adequate acquisitionBurden =
  s≤s z≤n
speciesSelectedWeaklyDominatesAnyEligible combinedQualifiedPanel admissible adequate provenanceDeficit =
  z≤n
speciesSelectedWeaklyDominatesAnyEligible combinedQualifiedPanel admissible adequate redundantCoordinateBurden =
  z≤n
speciesSelectedWeaklyDominatesAnyEligible combinedQualifiedPanel admissible adequate remainingConsumerGap =
  z≤n

speciesAcquisitionPareto :
  MDL.ParetoAdmissible speciesAcquisitionCosts speciesQualifiedPackage
speciesAcquisitionPareto = MDL.paretoAdmissible
  (tt , tt)
  (λ candidate eligible candidateDominates →
    speciesSelectedWeaklyDominatesAnyEligible candidate (proj₁ eligible) (proj₂ eligible))
  "after provenance/admissibility gates, speciesQualifiedPackage is Pareto-admissible for the species acquisition consumer"

contextSelectedWeaklyDominatesAnyEligible :
  (candidate : AcquisitionCandidate) →
  AcquisitionAdmissible candidate →
  ContextAcquisitionAdequate candidate →
  MDL.WeaklyDominates contextAcquisitionCosts contextQualifiedPackage candidate
contextSelectedWeaklyDominatesAnyEligible metadataOnlyShortcut () adequate
contextSelectedWeaklyDominatesAnyEligible speciesQualifiedPackage admissible ()
contextSelectedWeaklyDominatesAnyEligible contextQualifiedPackage admissible adequate axis = ≤-refl
contextSelectedWeaklyDominatesAnyEligible combinedQualifiedPanel admissible adequate acquisitionBurden =
  s≤s z≤n
contextSelectedWeaklyDominatesAnyEligible combinedQualifiedPanel admissible adequate provenanceDeficit =
  z≤n
contextSelectedWeaklyDominatesAnyEligible combinedQualifiedPanel admissible adequate redundantCoordinateBurden =
  z≤n
contextSelectedWeaklyDominatesAnyEligible combinedQualifiedPanel admissible adequate remainingConsumerGap =
  z≤n

contextAcquisitionPareto :
  MDL.ParetoAdmissible contextAcquisitionCosts contextQualifiedPackage
contextAcquisitionPareto = MDL.paretoAdmissible
  (tt , tt)
  (λ candidate eligible candidateDominates →
    contextSelectedWeaklyDominatesAnyEligible candidate (proj₁ eligible) (proj₂ eligible))
  "after provenance/admissibility gates, contextQualifiedPackage is Pareto-admissible for the contextual acquisition consumer"

------------------------------------------------------------------------
-- Expected selective reopening sets.
--
-- These paths say what must be reconsidered if the corresponding qualified
-- observation changes.  They are not empirical claims that a measurement has
-- occurred or that a downstream ecological state actually changed.
------------------------------------------------------------------------

data AcquisitionFrontierArtifact : Set where
  speciesObservationArtifact : AcquisitionFrontierArtifact
  contextObservationArtifact : AcquisitionFrontierArtifact
  chemistryInterpretationArtifact : AcquisitionFrontierArtifact
  calibratedClassificationArtifact : AcquisitionFrontierArtifact
  reboundConsumerArtifact : AcquisitionFrontierArtifact
  springfieldEquipmentArtifact : AcquisitionFrontierArtifact

data AcquisitionFrontierDepends :
  AcquisitionFrontierArtifact → AcquisitionFrontierArtifact → Set where
  speciesToChemistry :
    AcquisitionFrontierDepends speciesObservationArtifact chemistryInterpretationArtifact
  chemistryToClassification :
    AcquisitionFrontierDepends chemistryInterpretationArtifact calibratedClassificationArtifact
  contextToClassification :
    AcquisitionFrontierDepends contextObservationArtifact calibratedClassificationArtifact
  classificationToRebound :
    AcquisitionFrontierDepends calibratedClassificationArtifact reboundConsumerArtifact

acquisitionFrontierDependencyGraph :
  Acquisition.AcquisitionDependencyGraph AcquisitionFrontierArtifact
acquisitionFrontierDependencyGraph = Acquisition.acquisition-dependency-graph
  AcquisitionFrontierDepends
  "species observation -> chemistry interpretation -> calibrated classification -> rebound; context observation -> calibrated classification -> rebound; no equipment edge"

speciesObservationReopensChemistry :
  Acquisition.SelectiveAcquisitionReopening
    acquisitionFrontierDependencyGraph
    speciesObservationArtifact chemistryInterpretationArtifact
speciesObservationReopensChemistry =
  Acquisition.oneEdgeAcquisitionReopening speciesToChemistry

chemistryReopensClassification :
  Acquisition.SelectiveAcquisitionReopening
    acquisitionFrontierDependencyGraph
    chemistryInterpretationArtifact calibratedClassificationArtifact
chemistryReopensClassification =
  Acquisition.oneEdgeAcquisitionReopening chemistryToClassification

speciesObservationReopensClassification :
  Acquisition.SelectiveAcquisitionReopening
    acquisitionFrontierDependencyGraph
    speciesObservationArtifact calibratedClassificationArtifact
speciesObservationReopensClassification = Acquisition.selective-acquisition-reopening
  (Dependency.obligationsCompose
    (Acquisition.obligation speciesObservationReopensChemistry)
    (Acquisition.obligation chemistryReopensClassification))
  "species observation reaches calibrated classification through chemistry interpretation"

contextObservationReopensClassification :
  Acquisition.SelectiveAcquisitionReopening
    acquisitionFrontierDependencyGraph
    contextObservationArtifact calibratedClassificationArtifact
contextObservationReopensClassification =
  Acquisition.oneEdgeAcquisitionReopening contextToClassification

classificationReopensRebound :
  Acquisition.SelectiveAcquisitionReopening
    acquisitionFrontierDependencyGraph
    calibratedClassificationArtifact reboundConsumerArtifact
classificationReopensRebound =
  Acquisition.oneEdgeAcquisitionReopening classificationToRebound

speciesObservationReopensRebound :
  Acquisition.SelectiveAcquisitionReopening
    acquisitionFrontierDependencyGraph
    speciesObservationArtifact reboundConsumerArtifact
speciesObservationReopensRebound = Acquisition.selective-acquisition-reopening
  (Dependency.obligationsCompose
    (Acquisition.obligation speciesObservationReopensClassification)
    (Acquisition.obligation classificationReopensRebound))
  "species acquisition can reopen the dependency-reachable rebound consumer after chemistry interpretation and calibrated classification"

contextObservationReopensRebound :
  Acquisition.SelectiveAcquisitionReopening
    acquisitionFrontierDependencyGraph
    contextObservationArtifact reboundConsumerArtifact
contextObservationReopensRebound = Acquisition.selective-acquisition-reopening
  (Dependency.obligationsCompose
    (Acquisition.obligation contextObservationReopensClassification)
    (Acquisition.obligation classificationReopensRebound))
  "context acquisition can reopen the dependency-reachable rebound consumer through calibrated classification"

------------------------------------------------------------------------
-- Attribution / Pareto boundary.
------------------------------------------------------------------------

record BiocontrolAcquisitionParetoBoundary : Set where
  constructor biocontrolAcquisitionParetoBoundary
  field
    provenanceInadequateCheapRecordMayWin : Bool
    provenanceInadequateCheapRecordMayWinIsFalse :
      provenanceInadequateCheapRecordMayWin ≡ false

    rankingOccursAfterHardAdmissibility : Bool
    rankingOccursAfterHardAdmissibilityIsTrue :
      rankingOccursAfterHardAdmissibility ≡ true

    acquisitionCostsAreMeasuredFieldCosts : Bool
    acquisitionCostsAreMeasuredFieldCostsIsFalse :
      acquisitionCostsAreMeasuredFieldCosts ≡ false

    downstreamReopeningIsExpectedUtility : Bool
    downstreamReopeningIsExpectedUtilityIsFalse :
      downstreamReopeningIsExpectedUtility ≡ false

    selectedPackageIsAlreadyAcquiredObservation : Bool
    selectedPackageIsAlreadyAcquiredObservationIsFalse :
      selectedPackageIsAlreadyAcquiredObservation ≡ false

    actualPromotionStillRequiresQualifiedObservation : Bool
    actualPromotionStillRequiresQualifiedObservationIsTrue :
      actualPromotionStillRequiresQualifiedObservation ≡ true

    externalSourcesOwnDashiParetoRanking : Bool
    externalSourcesOwnDashiParetoRankingIsFalse :
      externalSourcesOwnDashiParetoRanking ≡ false

    crossPollinationTransfersEmpiricalStatus : Bool
    crossPollinationTransfersEmpiricalStatusIsFalse :
      crossPollinationTransfersEmpiricalStatus ≡ false

    springfieldOperationalRecordPaysChemistryAcquisition : Bool
    springfieldOperationalRecordPaysChemistryAcquisitionIsFalse :
      springfieldOperationalRecordPaysChemistryAcquisition ≡ false

    dependencyPathCreatesEquipmentReopeningWithoutEdge : Bool
    dependencyPathCreatesEquipmentReopeningWithoutEdgeIsFalse :
      dependencyPathCreatesEquipmentReopeningWithoutEdge ≡ false

canonicalBiocontrolAcquisitionParetoBoundary : BiocontrolAcquisitionParetoBoundary
canonicalBiocontrolAcquisitionParetoBoundary = biocontrolAcquisitionParetoBoundary
  false refl
  true refl
  false refl
  false refl
  false refl
  true refl
  false refl
  false refl
  false refl
  false refl

attributionReading : String
attributionReading =
  "Acquisition targets may be source-directed, but the finite candidate family, admissibility gate, synthetic Pareto axes, ranking and dependency-reopening paths are DASHI constructions. External sources own only records actually acquired from them. A selected package remains an obligation/plan until a same-object source/protocol-qualified observation pays the promotion gate. Citation and cross-pollination import neither proof, empirical status nor authority."
