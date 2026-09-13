module DASHI.Cognition.PNF.SensibLawUniversalLegalAlgebraEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawSourceFormAuthorityRoleBidiExact as SourceRole
import DASHI.Cognition.PNF.SensibLawPrecedentApplicabilityDistinguishingExact as Precedent
import DASHI.Cognition.PNF.SensibLawStatutoryRuleStructureAlgebraExact as Statute
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawNegligenceDutyRequirementSalienceExact as DutySalience
import DASHI.Cognition.PNF.SensibLawNegligenceDutyGenericParetoFrontierExact as DutyPareto
import DASHI.Cognition.PNF.SensibLawNegligenceDutyParetoProofPromotionExact as DutyParetoProof
import DASHI.Cognition.PNF.SensibLawWrongTypeRequirementSalienceFrontierExact as Frontier
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierProofPromotionExact as ParetoProof
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual
import DASHI.Cognition.PNF.SensibLawLegalGraphRefinementReopeningExact as Refinement
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawFiniteLegalCutGuardExact as CutGuard
import DASHI.Cognition.PNF.SensibLawCullenPublicAuthorityDutyCalibrationExact as Cullen
import DASHI.Cognition.PNF.SensibLawRecentDutyCaseSourceAtlasExact as PrimarySources
import DASHI.Cognition.PNF.SensibLawDutyPublicAuthoritySourceLineageGraphExact as SourceLineage
import DASHI.Cognition.PNF.SensibLawDutySourceLineageRefinementCutRerunExact as SourceRerun

------------------------------------------------------------------------
-- Universal graph and issue-specific graph are one architecture.
------------------------------------------------------------------------

data IssueSpecificPipelineIsSeparateLegalSystem : Set where
issueProjectionIsNotSeparateSystem : IssueSpecificPipelineIsSeparateLegalSystem → ⊥
issueProjectionIsNotSeparateSystem ()

------------------------------------------------------------------------
-- Duty has been lifted out of the climate-only vocabulary.
------------------------------------------------------------------------

climatePhysicalInjuryUsesNegligenceWrongType :
  Negligence.ClimateDutySpecialisation.wrongType
    Negligence.australiaPhysicalInjuryDutySpecialisation
  ≡ Negligence.negligenceWrongType
climatePhysicalInjuryUsesNegligenceWrongType = refl

climatePhysicalInjuryTargetsDutyElement :
  Negligence.ClimateDutySpecialisation.targetElement
    Negligence.australiaPhysicalInjuryDutySpecialisation
  ≡ Negligence.dutyElement
climatePhysicalInjuryTargetsDutyElement = refl

------------------------------------------------------------------------
-- Source form and authority role remain orthogonal.
------------------------------------------------------------------------

caseContainerDoesNotFlattenPropositionRoles :
  SourceRole.CaseSourceMakesEveryPropositionBindingRatio → ⊥
caseContainerDoesNotFlattenPropositionRoles =
  SourceRole.caseContainerDoesNotFlattenRoles

similarFactSurfaceDoesNotAutomaticallyApplyPrecedent :
  Precedent.SimilarFactsAutomaticallyApplyPrecedent → ⊥
similarFactSurfaceDoesNotAutomaticallyApplyPrecedent =
  Precedent.similarityDoesNotProveApplication

statutoryDefinitionRemainsScoped :
  Statute.DefinitionIsGlobalDictionaryMeaning → ⊥
statutoryDefinitionRemainsScoped = Statute.definitionIsScoped

------------------------------------------------------------------------
-- Legacy WrongElement string references no longer count as proof.
------------------------------------------------------------------------

legacyElementReferenceIsNotElementDerivation :
  Elements.ElementStringReferenceIsElementProof → ⊥
legacyElementReferenceIsNotElementDerivation = Elements.stringReferenceDoesNotProveElement

------------------------------------------------------------------------
-- Duty-coordinate stratification and live salience are separate coordinates.
------------------------------------------------------------------------

foreseeabilityClassIsFactual :
  Negligence.classifyDutyIssue Climate.reasonableForeseeability
  ≡ Negligence.factualDutyFeature
foreseeabilityClassIsFactual = refl

corePolicyClassIsInstitutional :
  Negligence.classifyDutyIssue Climate.coreGovernmentPolicy
  ≡ Negligence.institutionalDutyConstraint
corePolicyClassIsInstitutional = refl

causationClassIsDownstreamElement :
  Negligence.classifyDutyIssue Climate.causation
  ≡ Negligence.downstreamNegligenceElement
causationClassIsDownstreamElement = refl

foreseeabilityMayRemainRequiredWithoutBeingCurrentSplitter :
  Frontier.NecessaryButCurrentlyNonDiscriminating
    DutySalience.currentDutyProblem
    Climate.reasonableForeseeability
foreseeabilityMayRemainRequiredWithoutBeingCurrentSplitter =
  DutySalience.foreseeabilityRequiredButCurrentlyNonDiscriminating

corePolicyMayBeCurrentDutySplitter :
  Frontier.SalientRequirement
    DutySalience.currentDutyProblem
    Climate.coreGovernmentPolicy
corePolicyMayBeCurrentDutySplitter = DutySalience.corePolicyCurrentlySplitsDutyFibre

statutoryCoherenceMayBecomeSalientAfterPolicyClosure :
  Frontier.SalientRequirement
    DutySalience.postPolicyProblem
    Climate.statutoryCoherence
statutoryCoherenceMayBecomeSalientAfterPolicyClosure =
  DutySalience.statutoryCoherenceBecomesSalientAfterPolicyClosure

------------------------------------------------------------------------
-- Generic finite Pareto frontier computes the current question set; proof
-- promotion remains a separate receipt over that same portfolio.
------------------------------------------------------------------------

currentDutyParetoFrontierSelectsCorePolicy :
  Pareto.paretoFrontier DutyPareto.currentDutyPortfolio
  ≡ DutyPareto.currentCorePolicyCell ∷ []
currentDutyParetoFrontierSelectsCorePolicy =
  DutyPareto.currentDutyParetoFrontierIsCorePolicyOnly

currentDutyCorePolicyHasProofPromotion :
  ParetoProof.FrontierPromotion
    DutyPareto.currentDutyPortfolio
    DutyPareto.currentCorePolicyCell
currentDutyCorePolicyHasProofPromotion = DutyParetoProof.corePolicyPromotion

postPolicyParetoFrontierSelectsStatutoryCoherence :
  Pareto.paretoFrontier DutyPareto.postPolicyPortfolio
  ≡ DutyPareto.postPolicyStatutoryCoherenceCell ∷ []
postPolicyParetoFrontierSelectsStatutoryCoherence =
  DutyPareto.postPolicyDutyParetoFrontierIsStatutoryCoherenceOnly

postPolicyStatutoryCoherenceHasProofPromotion :
  ParetoProof.FrontierPromotion
    DutyPareto.postPolicyPortfolio
    DutyPareto.postPolicyStatutoryCoherenceCell
postPolicyStatutoryCoherenceHasProofPromotion =
  DutyParetoProof.statutoryCoherencePromotion

foreseeabilityRemainsRequiredWhileOffParetoFrontier :
  Pareto.requiredForConsumer DutyPareto.currentForeseeabilityCell ≡ true
foreseeabilityRemainsRequiredWhileOffParetoFrontier =
  DutyPareto.foreseeabilityRequiredButOffCurrentParetoFrontier

------------------------------------------------------------------------
-- Preferred source-owned duty/public-authority graph.
-- PrimarySources keeps court publication identity separate from graph roles.
------------------------------------------------------------------------

sourceLineageMallonlandConstraintReachable :
  Search.reachable 1 SourceLineage.dutyPublicAuthoritySourceLineageGraph
    SourceLineage.mallonlandAssessmentFacts
    SourceLineage.mallonlandFurtherSalientFeaturesRequired ≡ true
sourceLineageMallonlandConstraintReachable =
  SourceLineage.mallonlandConstraintReachable

sourceLineageCullenDutyReachable :
  Search.reachable 1 SourceLineage.dutyPublicAuthoritySourceLineageGraph
    SourceLineage.cullenHoldingFacts Cullen.cullenDutyProposition ≡ true
sourceLineageCullenDutyReachable = SourceLineage.cullenSpecificDutyReachable

sourceLineagePabaiObstructionReachable :
  Search.reachable 1 SourceLineage.dutyPublicAuthoritySourceLineageGraph
    SourceLineage.pabaiPolicyFacts
    SourceLineage.pabaiCurrentPleadedClimateDutyUnavailable ≡ true
sourceLineagePabaiObstructionReachable =
  SourceLineage.pabaiCurrentObstructionReachable

sourceLineageClimateDoesNotAutoReceiveCullen :
  Search.reachable 1 SourceLineage.dutyPublicAuthoritySourceLineageGraph
    SourceLineage.climateComparatorFacts Cullen.cullenDutyProposition ≡ false
sourceLineageClimateDoesNotAutoReceiveCullen =
  SourceLineage.climateFactsDoNotReachCullenSpecificDuty

sourceLineageCullenDoesNotAutoReceivePabai :
  Search.reachable 1 SourceLineage.dutyPublicAuthoritySourceLineageGraph
    SourceLineage.cullenHoldingFacts
    SourceLineage.pabaiCurrentPleadedClimateDutyUnavailable ≡ false
sourceLineageCullenDoesNotAutoReceivePabai =
  SourceLineage.cullenFactsDoNotReachPabaiClimateObstruction

sourceLineageCullenHasProofRelevantRoute :
  Algebra.Reachable SourceLineage.dutyPublicAuthoritySourceLineageGraph
    SourceLineage.cullenHoldingFacts Cullen.cullenDutyProposition
sourceLineageCullenHasProofRelevantRoute = SourceLineage.cullenSpecificDutyProof

------------------------------------------------------------------------
-- Source-owned material-feature refinement over the same richer graph.
------------------------------------------------------------------------

positiveActRefinementPreservesGraphAndHistory :
  Refinement.LegalRefinementReceipt.oldHistoryPreserved
    SourceRerun.positiveActRefinementReceipt ≡ true
positiveActRefinementPreservesGraphAndHistory = refl

cullenRouteClosedBeforePositiveAct :
  Search.reachable 1 SourceLineage.dutyPublicAuthoritySourceLineageGraph
    SourceRerun.beforePositiveActFacts Cullen.cullenDutyProposition ≡ false
cullenRouteClosedBeforePositiveAct =
  SourceRerun.cullenDutyUnreachableBeforePositiveAct

cullenRouteOpensAfterPositiveAct :
  Search.reachable 1 SourceLineage.dutyPublicAuthoritySourceLineageGraph
    SourceRerun.afterPositiveActFacts Cullen.cullenDutyProposition ≡ true
cullenRouteOpensAfterPositiveAct =
  SourceRerun.cullenDutyReachableAfterPositiveAct

cullenRouteHasProofAfterPositiveAct :
  Algebra.Reachable SourceLineage.dutyPublicAuthoritySourceLineageGraph
    SourceRerun.afterPositiveActFacts Cullen.cullenDutyProposition
cullenRouteHasProofAfterPositiveAct = SourceRerun.cullenDutyProofAfterPositiveAct

noMeaningfulCutBeforePositiveAct :
  CutGuard.searchReachableMinimalCut 1
    SourceLineage.dutyPublicAuthoritySourceLineageGraph
    SourceRerun.beforePositiveActFacts Cullen.cullenDutyProposition
  ≡ Search.notFound
noMeaningfulCutBeforePositiveAct = SourceRerun.noGuardedCutBeforePositiveAct

cullenRatioIsGuardedCutAfterPositiveAct :
  CutGuard.searchReachableMinimalCut 1
    SourceLineage.dutyPublicAuthoritySourceLineageGraph
    SourceRerun.afterPositiveActFacts Cullen.cullenDutyProposition
  ≡ Search.found
    (Search.ruleKey SourceLineage.cullenPositiveOperationalDutyRule ∷ [])
cullenRatioIsGuardedCutAfterPositiveAct = SourceRerun.cullenRatioCutAfterPositiveAct

------------------------------------------------------------------------
-- Reverse epistemic path.
------------------------------------------------------------------------

statutoryCoherenceMissingnessRoutesToStatutoryText :
  Residual.preferredRoute
    (Residual.dutyResidualKind Climate.statutoryCoherence)
  ≡ Residual.inspectStatutoryText
statutoryCoherenceMissingnessRoutesToStatutoryText = refl

corePolicyMissingnessRoutesToReasons :
  Residual.preferredRoute
    (Residual.dutyResidualKind Climate.coreGovernmentPolicy)
  ≡ Residual.inspectJudicialReasons
corePolicyMissingnessRoutesToReasons = refl

richerGraphMayDefeatAsWellAsOpen :
  Refinement.NewFactCanOnlyOpenAndNeverDefeat → ⊥
richerGraphMayDefeatAsWellAsOpen = Refinement.newFactsMayActivateExceptionsOrDefeaters

refinementDoesNotFreezeOldCut :
  Refinement.OldMinimalCutRemainsMinimalAfterRefinement → ⊥
refinementDoesNotFreezeOldCut = Refinement.minimalCutMustBeRechecked

------------------------------------------------------------------------
-- Aggregate does not claim corpus-complete legal extraction or kernel receipt.
------------------------------------------------------------------------

data UniversalAlgebraAggregateMeansCorpusComplete : Set where
data UniversalAlgebraAggregateMeansKernelValidated : Set where

aggregateDoesNotClaimCorpusCompleteness :
  UniversalAlgebraAggregateMeansCorpusComplete → ⊥
aggregateDoesNotClaimCorpusCompleteness ()

aggregateDoesNotClaimKernelValidation :
  UniversalAlgebraAggregateMeansKernelValidated → ⊥
aggregateDoesNotClaimKernelValidation ()
