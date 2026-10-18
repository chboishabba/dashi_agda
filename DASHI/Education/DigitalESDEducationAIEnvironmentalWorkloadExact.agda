module DASHI.Education.DigitalESDEducationAIEnvironmentalWorkloadExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDMaterialEnvironmentalSubstrateExact as Material
import DASHI.Education.DigitalESDMaterialImpactAllocationExact as Allocation
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- EDUCATION-SPECIFIC GENAI WORKLOAD / ENERGY FIXTURE
--
-- Pareto acquisition: unlike generic data-centre or AI-LCA context, this source
-- is directly about a design-education GenAI workshop.  It remains a preprint
-- and its energy accounting is retained as an operational/workload estimate,
-- not promoted to a cradle-to-grave deployment LCA or universal classroom law.
------------------------------------------------------------------------

lupettiCavallinMurrayRustSource : Attr.AttributedSource
lupettiCavallinMurrayRustSource = Attr.mkDOISource
  "Maria Luce Lupetti; Elena Cavallin; Dave Murray-Rust"
  "The Unbearable Lightness of Prompting: A Critical Reflection on the Environmental Impact of genAI use in Design Education"
  "arXiv preprint arXiv:2501.16061"
  "2025"
  "10.48550/arXiv.2501.16061"
  "https://arxiv.org/abs/2501.16061"
  (Attr.namedSourceKind "preprint")
  "Primary preprint/source-bounded design-education workload fixture. Uses a 2023 GenAI workshop with 49 students to estimate the energy costs of text/image generation activities. Supports a bounded educational-workload energy claim and critical pedagogical reflection; does not create a peer-reviewed deployment LCA, model-specific universal footprint, embodied-hardware inventory or long-term educational outcome."
  Attr.publicAttribution

workshopStudentCount : Nat
workshopStudentCount = 49

workshopScope : PNF.AssertionScope
workshopScope = PNF.assertionScope
  "49 students participating in a 2023 GenAI design workshop"
  "design-education workshop context"
  "student use of generative text/image tools during workshop activities"
  "estimated GenAI-workshop computer-energy burden compared with conventional student computer-use baseline"
  "estimated energy cost of the educational computing activity"
  "single workshop / short-term activity"

workshopPredicates : List PNF.PredicateAtom
workshopPredicates =
  PNF.predicateAtom "workshop-student-carrier" PNF.populationPredicate "student × workshop"
    "49 students form the source-reported workshop carrier"
  ∷ PNF.predicateAtom "genai-design-activity" PNF.interventionPredicate "student × GenAI-workshop"
    "students used text- and image-generation tools in design-education activities"
  ∷ PNF.predicateAtom "operational-energy-estimate" PNF.outcomePredicate "workshop × estimated-energy"
    "the source estimates energy costs associated with the GenAI workshop activities"
  ∷ PNF.predicateAtom "computer-use-comparator" PNF.comparatorPredicate "GenAI-workshop × conventional-computer-use"
    "the reported interpretation compares estimated GenAI-workshop energy with energy associated with students' ordinary computer use"
  ∷ PNF.predicateAtom "preprint-evidence-state" PNF.contextPredicate "source × publication-state"
    "the source is an arXiv preprint; publication state is retained rather than promoted to peer-reviewed evidence"
  ∷ PNF.predicateAtom "operational-not-lifecycle" PNF.contextPredicate "estimated-energy × system-boundary"
    "the workshop estimate does not by itself close semiconductor fabrication, training allocation, water, device end-of-life or affected-community incidence"
  ∷ []

workshopEnergyAssertion : PNF.PredicateNormalAssertion
workshopEnergyAssertion = PNF.predicateNormalAssertion
  "lupetti-2025-genai-design-workshop-energy"
  "For the reported 49-student 2023 design workshop, the source estimates that GenAI activities can approximately double the energy cost associated with students' computer use."
  PNF.studyPopulationQ
  PNF.comparativeF
  workshopScope
  workshopPredicates
  "same-object arXiv:2501.16061 / DOI 10.48550/arXiv.2501.16061; source status retained as preprint"

strongestPaidImplication : Cone.ImplicationKind
strongestPaidImplication = Cone.restatesMeasuredResult

strongestPaidReason : String
strongestPaidReason =
  "The source pays a bounded education-specific operational/workload energy estimate for its own 49-student workshop and a critical-reflection claim about that estimated burden."

firstUnpaidImplication : Cone.ImplicationKind
firstUnpaidImplication = Cone.transportsPopulation

firstUnpaidReason : String
firstUnpaidReason =
  "One workshop and one estimation method do not establish the energy footprint of all GenAI courses, platforms, models, institutions or learner populations."

materialBoundary : Material.MaterialEnvironmentalBoundary
materialBoundary = Material.canonicalMaterialEnvironmentalBoundary

allocationBoundary : Allocation.MaterialImpactAllocationBoundary
allocationBoundary = Allocation.canonicalMaterialImpactAllocationBoundary

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

data PreprintWorkshopEstimateCreatesDeploymentLCA : Set where
data OperationalEnergyEstimateCreatesLifecycleFootprint : Set where
data FortyNineStudentsCreatePopulationTransport : Set where
data EstimatedDoublingCreatesUniversalReboundLaw : Set where

preprintWorkshopEstimateDoesNotCreateDeploymentLCA :
  PreprintWorkshopEstimateCreatesDeploymentLCA → ⊥
preprintWorkshopEstimateDoesNotCreateDeploymentLCA ()

operationalEnergyEstimateDoesNotCreateLifecycleFootprint :
  OperationalEnergyEstimateCreatesLifecycleFootprint → ⊥
operationalEnergyEstimateDoesNotCreateLifecycleFootprint ()

fortyNineStudentsDoNotCreatePopulationTransport :
  FortyNineStudentsCreatePopulationTransport → ⊥
fortyNineStudentsDoNotCreatePopulationTransport ()

estimatedDoublingDoesNotCreateUniversalReboundLaw :
  EstimatedDoublingCreatesUniversalReboundLaw → ⊥
estimatedDoublingDoesNotCreateUniversalReboundLaw ()

workloadReading : String
workloadReading =
  "This preprint is retained because it pays a rare education-specific material predicate: an estimated operational-energy burden for a 49-student GenAI design workshop. It does not backfill a cradle-to-grave footprint. The material-substrate and allocation overlays still require model/hardware/system-boundary, training/serving/embodied allocation, water, service life and externality-incidence receipts before a named educational deployment footprint can be claimed."
