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

    nullOrHeterogeneousExplanationMustRemainLive : Bool
    nullOrHeterogeneousExplanationMustRemainLiveIsTrue :
      nullOrHeterogeneousExplanationMustRemainLive ≡ true

canonicalDiscriminatorMatrixBoundary : DiscriminatorMatrixBoundary
canonicalDiscriminatorMatrixBoundary = discriminator-matrix-boundary
  false refl
  false refl
  false refl
  true refl
