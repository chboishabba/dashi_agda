module DASHI.Culture.MissingDeceasedHypothesisDiscriminatorMatrixExact where

------------------------------------------------------------------------
-- COMPETING-HYPOTHESIS DISCRIMINATOR MATRIX
--
-- Candidate explanations are allowed to explain different subsets of the
-- roster.  This avoids forcing one mega-hypothesis to absorb every case.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)


data CandidateExplanation : Set where
  fusionEnergyIncumbentDisruption
  foreignStrategicCapabilityDenial
  rivalProgrammeOrContractBenefit
  lowReplaceabilityTacitKnowledgeSelection
  capabilityAwareCrossDomainSelection
  openScienceKnowledgeReleaseSelection
  retrospectiveNarrativeAssembly
  heterogeneousUnrelatedCases
  : CandidateExplanation

data DiscriminatorAxis : Set where
  rosterEnrichment
  actualDisruptionEffect
  actorMaterialBenefit
  capabilityAwareVisibility
  threatPerception
  opportunityOrAccess
  operationalEvidence
  matchedControlRobustness
  crossCaseCommonality
  negativeCaseTolerance
  knowledgeReleaseBoundaryEvidence
  : DiscriminatorAxis

data RequirementLevel : Set where
  required
  stronglyExpected
  informative
  notRequired
  : RequirementLevel

record HypothesisAxisRequirement : Set where
  constructor hypothesis-axis-requirement
  field
    hypothesis : CandidateExplanation
    axis : DiscriminatorAxis
    level : RequirementLevel
    rationale : String

open HypothesisAxisRequirement public

fusionNeedsEnrichment : HypothesisAxisRequirement
fusionNeedsEnrichment = hypothesis-axis-requirement
  fusionEnergyIncumbentDisruption rosterEnrichment required
  "A fossil/incumbent-energy explanation should enrich the roster for direct energy-transition relevance relative to matched peers; weak/negative cases cannot be silently recoded as positives."

fusionNeedsActorBenefit : HypothesisAxisRequirement
fusionNeedsActorBenefit = hypothesis-axis-requirement
  fusionEnergyIncumbentDisruption actorMaterialBenefit required
  "A specific incumbent actor must have material exposure to the relevant fusion transition."

fusionNeedsThreatPerception : HypothesisAxisRequirement
fusionNeedsThreatPerception = hypothesis-axis-requirement
  fusionEnergyIncumbentDisruption threatPerception stronglyExpected
  "Economic exposure is substantially more informative if contemporaneous evidence shows the actor actually perceived fusion as a threat."

strategicDenialNeedsCapabilityVisibility : HypothesisAxisRequirement
strategicDenialNeedsCapabilityVisibility = hypothesis-axis-requirement
  foreignStrategicCapabilityDenial capabilityAwareVisibility required
  "A strategic-denial selector must be able to recognise why the specialist's work matters to the affected capability."

lowReplaceabilityNeedsImpact : HypothesisAxisRequirement
lowReplaceabilityNeedsImpact = hypothesis-axis-requirement
  lowReplaceabilityTacitKnowledgeSelection actualDisruptionEffect required
  "If removal was valuable because the person was hard to replace, unusually large substitution cost/delay should be observable relative to matched departures."

capabilitySelectionNeedsCrossDomainObserver : HypothesisAxisRequirement
capabilitySelectionNeedsCrossDomainObserver = hypothesis-axis-requirement
  capabilityAwareCrossDomainSelection capabilityAwareVisibility required
  "The explanatory observer must see complementary capability contributions, not merely names or public publications."

openScienceNeedsEnrichment : HypothesisAxisRequirement
openScienceNeedsEnrichment = hypothesis-axis-requirement
  openScienceKnowledgeReleaseSelection rosterEnrichment required
  "Publication is common among scientists, so an open-science explanation is discriminating only if O1-O6 behaviour/posture is enriched relative to matched peers under a predeclared rubric."

openScienceNeedsVisibility : HypothesisAxisRequirement
openScienceNeedsVisibility = hypothesis-axis-requirement
  openScienceKnowledgeReleaseSelection capabilityAwareVisibility required
  "A selector explanation must identify an observer capable of seeing the relevant openness/release behaviour, not merely the person's technical field."

openScienceO6NeedsBoundaryEvidence : HypothesisAxisRequirement
openScienceO6NeedsBoundaryEvidence = hypothesis-axis-requirement
  openScienceKnowledgeReleaseSelection knowledgeReleaseBoundaryEvidence required
  "Any strong restricted-to-public release claim requires a prior-restriction receipt, a public-release receipt and a same-object weld. Ordinary publication, patents or disclosure advocacy cannot substitute."

openScienceActualDisruptionIsInformative : HypothesisAxisRequirement
openScienceActualDisruptionIsInformative = hypothesis-axis-requirement
  openScienceKnowledgeReleaseSelection actualDisruptionEffect informative
  "Open-science selection does not logically require programme paralysis, but actual knowledge-transfer consequences can distinguish a consequential release posture from ordinary public dissemination."

retrospectiveNarrativePredictsWeakControls : HypothesisAxisRequirement
retrospectiveNarrativePredictsWeakControls = hypothesis-axis-requirement
  retrospectiveNarrativeAssembly matchedControlRobustness required
  "If the cluster is assembled retrospectively from interesting biographies, apparent common features should weaken substantially against predeclared matched controls."

heterogeneousCasesDoNotRequireCommonActor : HypothesisAxisRequirement
heterogeneousCasesDoNotRequireCommonActor = hypothesis-axis-requirement
  heterogeneousUnrelatedCases crossCaseCommonality notRequired
  "A heterogeneous null permits different causes and therefore does not require one common selector, beneficiary or mechanism."

record DiscriminatorMatrixBoundary : Set where
  constructor discriminator-matrix-boundary
  field
    oneHypothesisMustExplainEveryRosterMember : Bool
    oneHypothesisMustExplainEveryRosterMemberIsFalse :
      oneHypothesisMustExplainEveryRosterMember ≡ false

    negativeCasesMayBeDiscardedToProtectHypothesis : Bool
    negativeCasesMayBeDiscardedToProtectHypothesisIsFalse :
      negativeCasesMayBeDiscardedToProtectHypothesis ≡ false

    explanatoryCoverageEqualsCausalProof : Bool
    explanatoryCoverageEqualsCausalProofIsFalse :
      explanatoryCoverageEqualsCausalProof ≡ false

    ordinaryPublicationAloneCanMakeOpenScienceSelectionDiscriminating : Bool
    ordinaryPublicationAloneCanMakeOpenScienceSelectionDiscriminatingIsFalse :
      ordinaryPublicationAloneCanMakeOpenScienceSelectionDiscriminating ≡ false

    restrictedReleaseMayBeInferredWithoutSameObjectBoundaryEvidence : Bool
    restrictedReleaseMayBeInferredWithoutSameObjectBoundaryEvidenceIsFalse :
      restrictedReleaseMayBeInferredWithoutSameObjectBoundaryEvidence ≡ false

    nullOrHeterogeneousExplanationMustRemainLive : Bool
    nullOrHeterogeneousExplanationMustRemainLiveIsTrue :
      nullOrHeterogeneousExplanationMustRemainLive ≡ true

canonicalDiscriminatorMatrixBoundary : DiscriminatorMatrixBoundary
canonicalDiscriminatorMatrixBoundary = discriminator-matrix-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
  true refl
