module DASHI.Biology.Protein.ProteinConsumerFamilyRefinementKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Biology.Protein.ProteinConsumerProjectionAdequacyExact as Portfolio

------------------------------------------------------------------------
-- PROTEIN CONSUMER-FAMILY REFINEMENT KERNEL
--
-- The portfolio already establishes four consumer-specific projection defects.
-- This owner turns those defects/repairs into one finite selection kernel.
-- Description length is applied only after consumer adequacy; it is not truth,
-- empirical support, source authority, or a universal protein representation.
--
-- Source/domain ownership remains upstream:
--   Feng/TRPA1                 -> thermal/residue premises
--   4AKE/1AKE structural lane  -> conformation/context premises
--   Li-Liu-Ji AdK              -> topology/rate premises
--   Allium/allicin thiol lane  -> accessibility/context premise
--
-- The selection kernel and cross-consumer comparison are DASHI synthesis.
------------------------------------------------------------------------

data ProteinCoordinateModel : Set where
  identityOnly : ProteinCoordinateModel
  identityPlusResidue : ProteinCoordinateModel
  sequenceOnly : ProteinCoordinateModel
  sequencePlusEnvironment : ProteinCoordinateModel
  topologyOnly : ProteinCoordinateModel
  topologyPlusRate : ProteinCoordinateModel
  cysteineOnly : ProteinCoordinateModel
  cysteinePlusAccessibility : ProteinCoordinateModel
  universalRichObservation : ProteinCoordinateModel

modelReference : ProteinCoordinateModel → String
modelReference identityOnly = "protein identity only"
modelReference identityPlusResidue = "protein identity + query-relevant residue state"
modelReference sequenceOnly = "primary sequence only"
modelReference sequencePlusEnvironment = "primary sequence + ligand/environment context"
modelReference topologyOnly = "route topology only"
modelReference topologyPlusRate = "route topology + transition-rate coordinate"
modelReference cysteineOnly = "cysteine presence only"
modelReference cysteinePlusAccessibility = "cysteine presence + accessibility/local chemical context"
modelReference universalRichObservation =
  "repository-local rich protein observation retaining identity, sequence/residue, conformation, environment, perturbation, assay, observable definition, topology, rate, accessibility and provenance coordinates"

modelDescriptionLength : ProteinCoordinateModel → Nat
modelDescriptionLength identityOnly = 1
modelDescriptionLength identityPlusResidue = 2
modelDescriptionLength sequenceOnly = 1
modelDescriptionLength sequencePlusEnvironment = 2
modelDescriptionLength topologyOnly = 1
modelDescriptionLength topologyPlusRate = 2
modelDescriptionLength cysteineOnly = 1
modelDescriptionLength cysteinePlusAccessibility = 2
modelDescriptionLength universalRichObservation = 11

allModelsAdmissible : ProteinCoordinateModel → Set
allModelsAdmissible model = ⊤

------------------------------------------------------------------------
-- Consumer-indexed adequacy.  Each declared local repair is sufficient for its
-- own consumer, while the deliberately richer model is also sufficient.  No
-- other cross-lane repair is silently promoted.
------------------------------------------------------------------------

thermalAdequate : ProteinCoordinateModel → Set
thermalAdequate identityPlusResidue = ⊤
thermalAdequate universalRichObservation = ⊤
thermalAdequate _ = ⊥

conformationAdequate : ProteinCoordinateModel → Set
conformationAdequate sequencePlusEnvironment = ⊤
conformationAdequate universalRichObservation = ⊤
conformationAdequate _ = ⊥

rateAdequate : ProteinCoordinateModel → Set
rateAdequate topologyPlusRate = ⊤
rateAdequate universalRichObservation = ⊤
rateAdequate _ = ⊥

thiolAdequate : ProteinCoordinateModel → Set
thiolAdequate cysteinePlusAccessibility = ⊤
thiolAdequate universalRichObservation = ⊤
thiolAdequate _ = ⊥

data ProteinRefines : ProteinCoordinateModel → ProteinCoordinateModel → Set where
  identityToResidue : ProteinRefines identityOnly identityPlusResidue
  sequenceToEnvironment : ProteinRefines sequenceOnly sequencePlusEnvironment
  topologyToRate : ProteinRefines topologyOnly topologyPlusRate
  cysteineToAccessibility : ProteinRefines cysteineOnly cysteinePlusAccessibility
  residueToRich : ProteinRefines identityPlusResidue universalRichObservation
  environmentToRich : ProteinRefines sequencePlusEnvironment universalRichObservation
  rateToRich : ProteinRefines topologyPlusRate universalRichObservation
  accessibilityToRich : ProteinRefines cysteinePlusAccessibility universalRichObservation

thermalProblem : MDL.ConsumerMDLProblem
thermalProblem = MDL.consumerMDLProblem
  ProteinCoordinateModel
  allModelsAdmissible
  thermalAdequate
  modelDescriptionLength
  ProteinRefines
  modelReference
  "repository-local coordinate-count code; source authority is not a code-length axis"
  "TRPA1 thermal-response consumer"

conformationProblem : MDL.ConsumerMDLProblem
conformationProblem = MDL.consumerMDLProblem
  ProteinCoordinateModel
  allModelsAdmissible
  conformationAdequate
  modelDescriptionLength
  ProteinRefines
  modelReference
  "repository-local coordinate-count code; source authority is not a code-length axis"
  "adenylate-kinase resolved-conformation consumer"

rateProblem : MDL.ConsumerMDLProblem
rateProblem = MDL.consumerMDLProblem
  ProteinCoordinateModel
  allModelsAdmissible
  rateAdequate
  modelDescriptionLength
  ProteinRefines
  modelReference
  "repository-local coordinate-count code; source authority is not a code-length axis"
  "adenylate-kinase transition-rate consumer"

thiolProblem : MDL.ConsumerMDLProblem
thiolProblem = MDL.consumerMDLProblem
  ProteinCoordinateModel
  allModelsAdmissible
  thiolAdequate
  modelDescriptionLength
  ProteinRefines
  modelReference
  "repository-local coordinate-count code; source authority is not a code-length axis"
  "allicin/protein-thiol modification consumer"

problemFor : Portfolio.ProteinConsumer → MDL.ConsumerMDLProblem
problemFor Portfolio.thermalResponseConsumer = thermalProblem
problemFor Portfolio.resolvedConformationConsumer = conformationProblem
problemFor Portfolio.transitionRateConsumer = rateProblem
problemFor Portfolio.thiolModificationConsumer = thiolProblem

selectedModel : Portfolio.ProteinConsumer → ProteinCoordinateModel
selectedModel Portfolio.thermalResponseConsumer = identityPlusResidue
selectedModel Portfolio.resolvedConformationConsumer = sequencePlusEnvironment
selectedModel Portfolio.transitionRateConsumer = topologyPlusRate
selectedModel Portfolio.thiolModificationConsumer = cysteinePlusAccessibility

------------------------------------------------------------------------
-- Minimum eligible receipts.  The richer model remains eligible but is longer;
-- all cross-lane models are ineligible for the declared consumer.
------------------------------------------------------------------------

thermalNoLongerThanAnyEligible :
  (candidate : ProteinCoordinateModel) →
  allModelsAdmissible candidate →
  thermalAdequate candidate →
  modelDescriptionLength identityPlusResidue ≤ modelDescriptionLength candidate
thermalNoLongerThanAnyEligible identityOnly admissible ()
thermalNoLongerThanAnyEligible identityPlusResidue admissible adequate = ≤-refl
thermalNoLongerThanAnyEligible sequenceOnly admissible ()
thermalNoLongerThanAnyEligible sequencePlusEnvironment admissible ()
thermalNoLongerThanAnyEligible topologyOnly admissible ()
thermalNoLongerThanAnyEligible topologyPlusRate admissible ()
thermalNoLongerThanAnyEligible cysteineOnly admissible ()
thermalNoLongerThanAnyEligible cysteinePlusAccessibility admissible ()
thermalNoLongerThanAnyEligible universalRichObservation admissible adequate =
  s≤s (s≤s z≤n)

conformationNoLongerThanAnyEligible :
  (candidate : ProteinCoordinateModel) →
  allModelsAdmissible candidate →
  conformationAdequate candidate →
  modelDescriptionLength sequencePlusEnvironment ≤ modelDescriptionLength candidate
conformationNoLongerThanAnyEligible identityOnly admissible ()
conformationNoLongerThanAnyEligible identityPlusResidue admissible ()
conformationNoLongerThanAnyEligible sequenceOnly admissible ()
conformationNoLongerThanAnyEligible sequencePlusEnvironment admissible adequate = ≤-refl
conformationNoLongerThanAnyEligible topologyOnly admissible ()
conformationNoLongerThanAnyEligible topologyPlusRate admissible ()
conformationNoLongerThanAnyEligible cysteineOnly admissible ()
conformationNoLongerThanAnyEligible cysteinePlusAccessibility admissible ()
conformationNoLongerThanAnyEligible universalRichObservation admissible adequate =
  s≤s (s≤s z≤n)

rateNoLongerThanAnyEligible :
  (candidate : ProteinCoordinateModel) →
  allModelsAdmissible candidate →
  rateAdequate candidate →
  modelDescriptionLength topologyPlusRate ≤ modelDescriptionLength candidate
rateNoLongerThanAnyEligible identityOnly admissible ()
rateNoLongerThanAnyEligible identityPlusResidue admissible ()
rateNoLongerThanAnyEligible sequenceOnly admissible ()
rateNoLongerThanAnyEligible sequencePlusEnvironment admissible ()
rateNoLongerThanAnyEligible topologyOnly admissible ()
rateNoLongerThanAnyEligible topologyPlusRate admissible adequate = ≤-refl
rateNoLongerThanAnyEligible cysteineOnly admissible ()
rateNoLongerThanAnyEligible cysteinePlusAccessibility admissible ()
rateNoLongerThanAnyEligible universalRichObservation admissible adequate =
  s≤s (s≤s z≤n)

thiolNoLongerThanAnyEligible :
  (candidate : ProteinCoordinateModel) →
  allModelsAdmissible candidate →
  thiolAdequate candidate →
  modelDescriptionLength cysteinePlusAccessibility ≤ modelDescriptionLength candidate
thiolNoLongerThanAnyEligible identityOnly admissible ()
thiolNoLongerThanAnyEligible identityPlusResidue admissible ()
thiolNoLongerThanAnyEligible sequenceOnly admissible ()
thiolNoLongerThanAnyEligible sequencePlusEnvironment admissible ()
thiolNoLongerThanAnyEligible topologyOnly admissible ()
thiolNoLongerThanAnyEligible topologyPlusRate admissible ()
thiolNoLongerThanAnyEligible cysteineOnly admissible ()
thiolNoLongerThanAnyEligible cysteinePlusAccessibility admissible adequate = ≤-refl
thiolNoLongerThanAnyEligible universalRichObservation admissible adequate =
  s≤s (s≤s z≤n)

thermalMinimal : MDL.MinimalEligibleDescription thermalProblem identityPlusResidue
thermalMinimal = MDL.minimalEligibleDescription
  tt tt thermalNoLongerThanAnyEligible
  "identity+residue is shortest eligible model in the declared TRPA1 thermal family"

conformationMinimal :
  MDL.MinimalEligibleDescription conformationProblem sequencePlusEnvironment
conformationMinimal = MDL.minimalEligibleDescription
  tt tt conformationNoLongerThanAnyEligible
  "sequence+environment is shortest eligible model in the declared AdK conformation family"

rateMinimal : MDL.MinimalEligibleDescription rateProblem topologyPlusRate
rateMinimal = MDL.minimalEligibleDescription
  tt tt rateNoLongerThanAnyEligible
  "topology+rate is shortest eligible model in the declared AdK transition-rate family"

thiolMinimal :
  MDL.MinimalEligibleDescription thiolProblem cysteinePlusAccessibility
thiolMinimal = MDL.minimalEligibleDescription
  tt tt thiolNoLongerThanAnyEligible
  "cysteine+accessibility is shortest eligible model in the declared allicin modification family"

minimalFor :
  (consumer : Portfolio.ProteinConsumer) →
  MDL.MinimalEligibleDescription (problemFor consumer) (selectedModel consumer)
minimalFor Portfolio.thermalResponseConsumer = thermalMinimal
minimalFor Portfolio.resolvedConformationConsumer = conformationMinimal
minimalFor Portfolio.transitionRateConsumer = rateMinimal
minimalFor Portfolio.thiolModificationConsumer = thiolMinimal

selectedIsEligible :
  (consumer : Portfolio.ProteinConsumer) →
  MDL.Eligible (problemFor consumer) (selectedModel consumer)
selectedIsEligible consumer = MDL.minimalDescriptionIsEligible (minimalFor consumer)

------------------------------------------------------------------------
-- Local refinement receipts connect the portfolio's coarse surfaces to exactly
-- the coordinate family selected by this kernel.
------------------------------------------------------------------------

record ProteinConsumerRefinementReceipt : Set where
  constructor protein-consumer-refinement-receipt
  field
    consumer : Portfolio.ProteinConsumer
    coarseModel : ProteinCoordinateModel
    fineModel : ProteinCoordinateModel
    retainedCoordinate : Portfolio.ProteinCoordinateClass
    sourcePayment : String
    dashiSelectionRole : String
open ProteinConsumerRefinementReceipt public

refinementReceipt : Portfolio.ProteinConsumer → ProteinConsumerRefinementReceipt
refinementReceipt Portfolio.thermalResponseConsumer =
  protein-consumer-refinement-receipt
    Portfolio.thermalResponseConsumer identityOnly identityPlusResidue
    Portfolio.sequenceResidueCoordinate
    (Portfolio.sourcePayment Portfolio.thermalProjectionProfile)
    "DASHI selects the minimal consumer-adequate retained coordinate family; Feng et al. retain ownership only of the source-bounded TRPA1 premise"
refinementReceipt Portfolio.resolvedConformationConsumer =
  protein-consumer-refinement-receipt
    Portfolio.resolvedConformationConsumer sequenceOnly sequencePlusEnvironment
    Portfolio.environmentCoordinate
    (Portfolio.sourcePayment Portfolio.conformationProjectionProfile)
    "DASHI selects the minimal consumer-adequate retained coordinate family; structural sources retain ownership only of the bounded 4AKE/1AKE premise"
refinementReceipt Portfolio.transitionRateConsumer =
  protein-consumer-refinement-receipt
    Portfolio.transitionRateConsumer topologyOnly topologyPlusRate
    Portfolio.rateCoordinate
    (Portfolio.sourcePayment Portfolio.rateProjectionProfile)
    "DASHI selects the minimal consumer-adequate retained coordinate family; Li-Liu-Ji retain ownership only of source-bounded AdK rate premises"
refinementReceipt Portfolio.thiolModificationConsumer =
  protein-consumer-refinement-receipt
    Portfolio.thiolModificationConsumer cysteineOnly cysteinePlusAccessibility
    Portfolio.siteAccessibilityCoordinate
    (Portfolio.sourcePayment Portfolio.thiolModificationProjectionProfile)
    "DASHI selects the minimal consumer-adequate retained coordinate family; Allium literature retains ownership only of source-bounded thiol/accessibility premises"

------------------------------------------------------------------------
-- WrongType / cross-query firewalls.
------------------------------------------------------------------------

data ThermalSelectionMayAnswerRateQuery : Set where
data RateSelectionMayAnswerConformationQuery : Set where
data ThiolSelectionMayAnswerThermalQuery : Set where
data RicherModelMakesLocalRepairFalse : Set where
data SourceIdentifierCreatesSelectionTheorem : Set where
data SourceAttributionTransfersAcrossConsumers : Set where

thermalSelectionDoesNotAnswerRateQuery : ThermalSelectionMayAnswerRateQuery → ⊥
thermalSelectionDoesNotAnswerRateQuery ()

rateSelectionDoesNotAnswerConformationQuery : RateSelectionMayAnswerConformationQuery → ⊥
rateSelectionDoesNotAnswerConformationQuery ()

thiolSelectionDoesNotAnswerThermalQuery : ThiolSelectionMayAnswerThermalQuery → ⊥
thiolSelectionDoesNotAnswerThermalQuery ()

richerModelDoesNotRefuteLocalRepair : RicherModelMakesLocalRepairFalse → ⊥
richerModelDoesNotRefuteLocalRepair ()

sourceIdentifierDoesNotCreateSelectionTheorem : SourceIdentifierCreatesSelectionTheorem → ⊥
sourceIdentifierDoesNotCreateSelectionTheorem ()

sourceAttributionDoesNotTransferAcrossConsumers : SourceAttributionTransfersAcrossConsumers → ⊥
sourceAttributionDoesNotTransferAcrossConsumers ()

sourceAttributionRemainsDomainLocal : Bool
sourceAttributionRemainsDomainLocal = true

crossQueryPromotionAllowed : Bool
crossQueryPromotionAllowed = false

attributionRule : String
attributionRule =
  "DOI/PMID/PMCID/QID/PDB/UniProt remain publication/object identity and provenance coordinates only. Feng/TRPA1, 4AKE/1AKE, Li-Liu-Ji/AdK, and Allium/allicin sources pay only their own acquired biological premises. The consumer-family selection kernel, description-length comparison, minimality receipts, and cross-consumer firewalls are DASHI synthesis."

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ProteinConsumerFamilyRefinementBoundary : Set where
  constructor protein-consumer-family-refinement-boundary
  field
    fourConsumersRetained : Bool
    eachConsumerHasLocalSelectedModel : Bool
    richerUniversalObservationRetained : Bool
    richerUniversalObservationAutomaticallyPreferred : Bool
    minimalityAppliedAfterAdequacy : Bool
    crossQueryPromotionAllowed : Bool
    sourceAttributionRemainsDomainLocal : Bool
    externalIdentityCreatesSelectionAuthority : Bool
    oneSelectedModelIsUniversallySufficient : Bool
open ProteinConsumerFamilyRefinementBoundary public

canonicalProteinConsumerFamilyRefinementBoundary : ProteinConsumerFamilyRefinementBoundary
canonicalProteinConsumerFamilyRefinementBoundary =
  protein-consumer-family-refinement-boundary
    true true true false true false true false false
