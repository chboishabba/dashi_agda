module DASHI.Interop.StateIndexedLiveCutParetoCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.PenroseLocalGlobalHyperfabricCrossPollinationExact as Parent
import DASHI.Core.ResidualLiveSetSalienceSchedulerBidiExact as Live
import DASHI.Core.ResidualConditionedExperimentPortfolioExact as Portfolio
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.LiteralFrontierSchedulerExact as Literal
import DASHI.Core.ClayCrossDomainLiteralFrontierExact as Clay
import DASHI.Physics.NSYMLiteralFrontierSchedulerExact as NSYM
import DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact as YM146
import DASHI.Physics.YangMills.BalabanFrontierRouteAdmissionRound147Exact as YM147
import DASHI.Physics.YangMills.BalabanActiveSourceDiscriminator2026Exact as YMSource
import DASHI.Cognition.PNF.SensibLawDutySourceLineageRefinementCutRerunExact as GuardedCut
import DASHI.Physics.Closure.NSTriadKNCanonicalClayProofSearchRound486Exact as NS486

record StateIndexedLiveCutParetoAdapter : Set where
  constructor stateIndexedLiveCutParetoAdapter
  field
    liveSetReference : String
    residualPortfolioReference : String
    guardedCutReference : String
    paretoReference : String
    salienceIndexedByResidualAndLiveSet : Bool
    salienceIndexedByResidualAndLiveSetIsTrue : salienceIndexedByResidualAndLiveSet ≡ true
    magnitudeGreedyMayMissLiveNarrowing : Bool
    magnitudeGreedyMayMissLiveNarrowingIsTrue : magnitudeGreedyMayMissLiveNarrowing ≡ true
    salienceCreatesCandidateAdmission : Bool
    salienceCreatesCandidateAdmissionIsFalse : salienceCreatesCandidateAdmission ≡ false
    residualUpdateMayChangeSelectedExperiment : Bool
    residualUpdateMayChangeSelectedExperimentIsTrue : residualUpdateMayChangeSelectedExperiment ≡ true
    portfolioSelectionCreatesExecutionAuthority : Bool
    portfolioSelectionCreatesExecutionAuthorityIsFalse : portfolioSelectionCreatesExecutionAuthority ≡ false
    terminalConsumerStillRequired : Bool
    terminalConsumerStillRequiredIsTrue : terminalConsumerStillRequired ≡ true
    sameGraphFactAppendMayChangeReachabilityAndCut : Bool
    sameGraphFactAppendMayChangeReachabilityAndCutIsTrue : sameGraphFactAppendMayChangeReachabilityAndCut ≡ true
    stateIndexedSelectionDoesNotCreateSourceAuthority : Bool
    stateIndexedSelectionDoesNotCreateSourceAuthorityIsTrue : stateIndexedSelectionDoesNotCreateSourceAuthority ≡ true
    historicalEvidenceMayRemainValidWhileNextStepSalienceChanges : Bool
    historicalEvidenceMayRemainValidWhileNextStepSalienceChangesIsTrue : historicalEvidenceMayRemainValidWhileNextStepSalienceChanges ≡ true

open StateIndexedLiveCutParetoAdapter public

canonicalStateIndexedLiveCutParetoAdapter : StateIndexedLiveCutParetoAdapter
canonicalStateIndexedLiveCutParetoAdapter = stateIndexedLiveCutParetoAdapter
  "ResidualLiveSetSalienceSchedulerBidiExact: salience is strict narrowing of the current live set"
  "ResidualConditionedExperimentPortfolioExact: relevance/admissibility are indexed by current residual, consumer, and authority"
  "SensibLawDutySourceLineageRefinementCutRerunExact: same source-lineage graph, source-owned fact append, recomputed reachability and guarded cut"
  "PenroseLocalGlobalHyperfabricCrossPollinationExact: terminal consumer and hard-gated Pareto selection"
  (Live.salienceIndexedByResidualAndLiveSet Live.canonicalResidualLiveSetSalienceBoundary) refl
  (Live.magnitudeGreedyMayMissNarrowing Live.canonicalResidualLiveSetSalienceBoundary) refl
  (Live.salienceCreatesCandidateAdmission Live.canonicalResidualLiveSetSalienceBoundary) refl
  (Portfolio.residualUpdateMayChangeSelectedExperiment Portfolio.canonicalResidualConditionedPortfolioBoundary)
  (Portfolio.residualUpdateMayChangeSelectedExperimentIsTrue Portfolio.canonicalResidualConditionedPortfolioBoundary)
  (Portfolio.portfolioSelectionCreatesExecutionAuthority Portfolio.canonicalResidualConditionedPortfolioBoundary)
  (Portfolio.portfolioSelectionCreatesExecutionAuthorityIsFalse Portfolio.canonicalResidualConditionedPortfolioBoundary)
  Parent.terminalConsumerStillMustBePaid Parent.terminalConsumerStillMustBePaidIsTrue
  true refl true refl true refl

asStateIndexedMDLProblem :
  (P : Portfolio.ExperimentPortfolio) →
  Portfolio.ResidualContext P →
  Portfolio.Consumer P →
  Portfolio.Authority P →
  Pareto.ConsumerMDLProblem
asStateIndexedMDLProblem P residual consumer authority =
  Pareto.consumerMDLProblem
    (Portfolio.Experiment P)
    (λ experiment → Portfolio.admissibleNow P authority experiment ≡ true)
    (λ experiment → Portfolio.relevantNow P residual consumer experiment ≡ true)
    (λ experiment → Choice.cost (Portfolio.move P experiment))
    (λ _ _ → ⊤)
    (Portfolio.experimentReference P)
    "state-indexed residual-portfolio resource-cost code"
    "current residual / consumer / authority context"

portfolioCandidateIsEligible :
  ∀ {P residual consumer authority experiment} →
  Portfolio.PortfolioCandidate P residual consumer authority experiment →
  Pareto.Eligible (asStateIndexedMDLProblem P residual consumer authority) experiment
portfolioCandidateIsEligible candidate = Portfolio.admissible candidate , Portfolio.relevant candidate

stateIndexedEligibilityDoesNotCreateRouteAdmission : Bool
stateIndexedEligibilityDoesNotCreateRouteAdmission = true

stateIndexedEligibilityDoesNotCreateRouteAdmissionIsTrue : stateIndexedEligibilityDoesNotCreateRouteAdmission ≡ true
stateIndexedEligibilityDoesNotCreateRouteAdmissionIsTrue = refl

record AdmittedStateIndexedCandidate
    (P : Portfolio.ExperimentPortfolio)
    (residual : Portfolio.ResidualContext P)
    (consumer : Portfolio.Consumer P)
    (authority : Portfolio.Authority P)
    (experiment : Portfolio.Experiment P) : Set where
  constructor admitted-state-indexed-candidate
  field
    currentPortfolioCandidate : Portfolio.PortfolioCandidate P residual consumer authority experiment
    routeAdmission : ProofSearch.RouteAdmission
    terminalConsumerReference : String

open AdmittedStateIndexedCandidate public

admittedStateIndexedCandidateEligible :
  ∀ {P residual consumer authority experiment} →
  AdmittedStateIndexedCandidate P residual consumer authority experiment →
  Pareto.Eligible (asStateIndexedMDLProblem P residual consumer authority) experiment
admittedStateIndexedCandidateEligible admitted = portfolioCandidateIsEligible (currentPortfolioCandidate admitted)

admittedCandidateAutomaticallyParetoOptimal : Bool
admittedCandidateAutomaticallyParetoOptimal = false

admittedCandidateAutomaticallyParetoOptimalIsFalse : admittedCandidateAutomaticallyParetoOptimal ≡ false
admittedCandidateAutomaticallyParetoOptimalIsFalse = refl

admittedCandidateAutomaticallyClosesTerminalConsumer : Bool
admittedCandidateAutomaticallyClosesTerminalConsumer = false

admittedCandidateAutomaticallyClosesTerminalConsumerIsFalse : admittedCandidateAutomaticallyClosesTerminalConsumer ≡ false
admittedCandidateAutomaticallyClosesTerminalConsumerIsFalse = refl

GuardedCutAuthorityPromotion : Set
GuardedCutAuthorityPromotion = GuardedCut.GuardedCutPromotesReconstructionToRatio

guardedCutCannotPromoteAuthority : GuardedCutAuthorityPromotion → ⊥
guardedCutCannotPromoteAuthority = GuardedCut.cutDoesNotChangeAuthorityRole

OpenCullenRouteTransfersToClimate : Set
OpenCullenRouteTransfersToClimate = GuardedCut.OpenCullenRouteTransfersToClimate

openCullenRouteStillDoesNotTransfer : OpenCullenRouteTransfersToClimate → ⊥
openCullenRouteStillDoesNotTransfer = GuardedCut.specificOpenRouteStillDoesNotTransfer

record NSCanonicalCurrentCutParetoAdapter : Set where
  constructor nsCanonicalCurrentCutParetoAdapter
  field
    canonicalConsumerReference : String
    sourceCustodyReference : String
    canonicalShortestConsumerIsR423 : Bool
    canonicalShortestConsumerIsR423IsTrue : canonicalShortestConsumerIsR423 ≡ true
    directR423BudgetPaid : Bool
    directR423BudgetPaidIsFalse : directR423BudgetPaid ≡ false
    crossOutputCoherenceRequired : Bool
    crossOutputCoherenceRequiredIsFalse : crossOutputCoherenceRequired ≡ false
    r284DecompositionMandatory : Bool
    r284DecompositionMandatoryIsFalse : r284DecompositionMandatory ≡ false
    clayPromotionPaid : Bool
    clayPromotionPaidIsFalse : clayPromotionPaid ≡ false
    staleRound83SnapshotMayOverrideCanonicalCut : Bool
    staleRound83SnapshotMayOverrideCanonicalCutIsFalse : staleRound83SnapshotMayOverrideCanonicalCut ≡ false
    optionalProducerMayBecomeMandatoryWithoutFrontierImprovement : Bool
    optionalProducerMayBecomeMandatoryWithoutFrontierImprovementIsFalse : optionalProducerMayBecomeMandatoryWithoutFrontierImprovement ≡ false
    crossDomainSchedulerShapeProvesSharedMathematics : Bool
    crossDomainSchedulerShapeProvesSharedMathematicsIsFalse : crossDomainSchedulerShapeProvesSharedMathematics ≡ false

open NSCanonicalCurrentCutParetoAdapter public

canonicalNSCanonicalCurrentCutParetoAdapter : NSCanonicalCurrentCutParetoAdapter
canonicalNSCanonicalCurrentCutParetoAdapter = nsCanonicalCurrentCutParetoAdapter
  "R486/R423: cutoff-uniform integrated signed quadratic-companion heat-cross payment"
  "canonical NS frontier and attribution remain owned by NSTriadKNCanonicalClayProofSearchRound486Exact and ClayCrossDomainLiteralFrontierExact"
  NS486.round486R423IsCanonicalShortestConsumer NS486.round486R423IsCanonicalShortestConsumerIsTrue
  NS486.round486DirectR423BudgetClosed NS486.round486DirectR423BudgetClosedIsFalse
  NS486.round486CrossOutputCoherenceRequired NS486.round486CrossOutputCoherenceRequiredIsFalse
  NS486.round486R284DecompositionMandatory NS486.round486R284DecompositionMandatoryIsFalse
  NS486.round486ClayPromotion NS486.round486ClayPromotionIsFalse
  false refl false refl
  (Clay.sharedSchedulerShapeProvesSharedMathematics Clay.canonicalCrossDomainBoundary)
  (Clay.sharedSchedulerShapeProvesSharedMathematicsIsFalse Clay.canonicalCrossDomainBoundary)

nsCurrentResidualIsDirectR423Budget :
  NS486.firstCanonicalNSResidual NS486.currentCanonicalNSStatus ≡ NS486.missingCutoffUniformSignedCompanionBudget
nsCurrentResidualIsDirectR423Budget = NS486.currentFirstMissingIsR423Budget

nsCurrentRouteAdmission : ProofSearch.RouteAdmission
nsCurrentRouteAdmission = NS486.directR423RouteAdmission

record LiteralFrontierParetoBoundaryAdapter : Set where
  constructor literalFrontierParetoBoundaryAdapter
  field
    literalSchedulerReference : String
    ymSchedulerReference : String
    paretoReferenceConstructsCostHyperfabric : Bool
    paretoReferenceConstructsCostHyperfabricIsFalse : paretoReferenceConstructsCostHyperfabric ≡ false
    redirectEqualsFormalClosure : Bool
    redirectEqualsFormalClosureIsFalse : redirectEqualsFormalClosure ≡ false
    formalClosureRequiresExactConsumerReceipt : Bool
    formalClosureRequiresExactConsumerReceiptIsTrue : formalClosureRequiresExactConsumerReceipt ≡ true
    ymOneChildAuthorityClosesParent : Bool
    ymOneChildAuthorityClosesParentIsFalse : ymOneChildAuthorityClosesParent ≡ false
    ymQuantitativeParetoRankingAvailableWithoutDeclaredCosts : Bool
    ymQuantitativeParetoRankingAvailableWithoutDeclaredCostsIsFalse : ymQuantitativeParetoRankingAvailableWithoutDeclaredCosts ≡ false

open LiteralFrontierParetoBoundaryAdapter public

canonicalLiteralFrontierParetoBoundaryAdapter : LiteralFrontierParetoBoundaryAdapter
canonicalLiteralFrontierParetoBoundaryAdapter = literalFrontierParetoBoundaryAdapter
  "DASHI.Core.LiteralFrontierSchedulerExact owns close/redirect/reject outcomes"
  "DASHI.Physics.NSYMLiteralFrontierSchedulerExact owns current NS/YM literal moves"
  false refl
  (Literal.redirectEqualsFormalClosure Literal.canonicalLiteralFrontierSchedulerBoundary)
  (Literal.redirectEqualsFormalClosureIsFalse Literal.canonicalLiteralFrontierSchedulerBoundary)
  (Literal.formalClosureRequiresExactConsumerReceipt Literal.canonicalLiteralFrontierSchedulerBoundary)
  (Literal.formalClosureRequiresExactConsumerReceiptIsTrue Literal.canonicalLiteralFrontierSchedulerBoundary)
  (NSYM.ymParentRouteInheritsOneChildAuthority NSYM.canonicalNSYMLiteralFrontierBoundary)
  (NSYM.ymParentRouteInheritsOneChildAuthorityIsFalse NSYM.canonicalNSYMLiteralFrontierBoundary)
  false refl

ymDirectRouteStillConjunctive :
  YM146.routeTargets YM146.directRound108ActionRoute
  ≡ YM146.round108FixedDensitySemantics ∷ YM146.round108SelectedPotentialMatchesBC1 ∷ []
ymDirectRouteStillConjunctive = NSYM.ymDirectRouteHasTwoChildren

YMNumericalDirectClosure : Set
YMNumericalDirectClosure = YM147.DirectLeafClosureCapability YM147.numericalExperiment

ymNumericalCannotCloseLeaf : YMNumericalDirectClosure → ⊥
ymNumericalCannotCloseLeaf = NSYM.ymNumericalCannotCloseLeaf

------------------------------------------------------------------------
-- Costed YM source-recovery consumer probe.
------------------------------------------------------------------------

record YMSourceRecoveryConsumerAdapter : Set where
  constructor ymSourceRecoveryConsumerAdapter
  field
    sourceProbeReference : String
    sourceProbeCost : Nat
    matchingSourceLabelsCloseLiteralRecovery : Bool
    matchingSourceLabelsCloseLiteralRecoveryIsFalse : matchingSourceLabelsCloseLiteralRecovery ≡ false
    sourceProbeMayRefineRecoveryFibre : Bool
    sourceProbeMayRefineRecoveryFibreIsTrue : sourceProbeMayRefineRecoveryFibre ≡ true
    consumerClosureRequiresWholeSourceIdentity : Bool
    consumerClosureRequiresWholeSourceIdentityIsFalse : consumerClosureRequiresWholeSourceIdentity ≡ false
    machineCheckedCompilerImpliesLiteralSourceInhabitation : Bool
    machineCheckedCompilerImpliesLiteralSourceInhabitationIsFalse : machineCheckedCompilerImpliesLiteralSourceInhabitation ≡ false
    declaredProbeCostCreatesRouteAdmission : Bool
    declaredProbeCostCreatesRouteAdmissionIsFalse : declaredProbeCostCreatesRouteAdmission ≡ false
    consumerClosingProbeClosesYMTheoremLeaf : Bool
    consumerClosingProbeClosesYMTheoremLeafIsFalse : consumerClosingProbeClosesYMTheoremLeaf ≡ false

open YMSourceRecoveryConsumerAdapter public

canonicalYMSourceRecoveryConsumerAdapter : YMSourceRecoveryConsumerAdapter
canonicalYMSourceRecoveryConsumerAdapter = ymSourceRecoveryConsumerAdapter
  "Balaban literal same-object recovery discriminator; source-exact reconstruction receipt, not numerical calibration"
  (Synthesis.cost YMSource.literalRecoveryBundle)
  (YMSource.matchingSourceLabelsCloseLiteralRecovery YMSource.canonicalBalabanActiveSourceBoundary)
  (YMSource.matchingSourceLabelsCloseLiteralRecoveryIsFalse YMSource.canonicalBalabanActiveSourceBoundary)
  (YMSource.sourceProbeMayRefineRecoveryFibre YMSource.canonicalBalabanActiveSourceBoundary)
  (YMSource.sourceProbeMayRefineRecoveryFibreIsTrue YMSource.canonicalBalabanActiveSourceBoundary)
  (YMSource.consumerClosureRequiresWholeSourceIdentity YMSource.canonicalBalabanActiveSourceBoundary)
  (YMSource.consumerClosureRequiresWholeSourceIdentityIsFalse YMSource.canonicalBalabanActiveSourceBoundary)
  (YMSource.machineCheckedCompilerImpliesLiteralSourceInhabitation YMSource.canonicalBalabanActiveSourceBoundary)
  (YMSource.machineCheckedCompilerImpliesLiteralSourceInhabitationIsFalse YMSource.canonicalBalabanActiveSourceBoundary)
  false refl false refl

ymLiteralRecoveryProbeCostIsOne : Synthesis.cost YMSource.literalRecoveryBundle ≡ 1
ymLiteralRecoveryProbeCostIsOne = refl

ymLiteralProbeClosesRecoveryDecision :
  Synthesis.ProspectivelyClosesConsumer
    YMSource.compatible
    YMSource.recoveryDecision
    YMSource.literalRecoveryBundle
ymLiteralProbeClosesRecoveryDecision = YMSource.literalProbeClosesDecision

record LeastPrivilegeLiveCutAdmissionAdapter : Set where
  constructor leastPrivilegeLiveCutAdmissionAdapter
  field
    admissionReference : String
    theoremNameStringCreatesProofCapability : Bool
    theoremNameStringCreatesProofCapabilityIsFalse : theoremNameStringCreatesProofCapability ≡ false
    routeMayElaborateBeforeAdmission : Bool
    routeMayElaborateBeforeAdmissionIsFalse : routeMayElaborateBeforeAdmission ≡ false
    routeMaySilentlyStrengthenHypotheses : Bool
    routeMaySilentlyStrengthenHypothesesIsFalse : routeMaySilentlyStrengthenHypotheses ≡ false
    localLemmaAutomaticallyMovesProgrammeFrontier : Bool
    localLemmaAutomaticallyMovesProgrammeFrontierIsFalse : localLemmaAutomaticallyMovesProgrammeFrontier ≡ false
    lemmaCountIsAuthoritativeProgress : Bool
    lemmaCountIsAuthoritativeProgressIsFalse : lemmaCountIsAuthoritativeProgress ≡ false
    duplicateRouteShouldBeReproved : Bool
    duplicateRouteShouldBeReprovedIsFalse : duplicateRouteShouldBeReproved ≡ false
    liveCutSalienceCannotBypassRouteAdmission : Bool
    liveCutSalienceCannotBypassRouteAdmissionIsTrue : liveCutSalienceCannotBypassRouteAdmission ≡ true

open LeastPrivilegeLiveCutAdmissionAdapter public

canonicalLeastPrivilegeLiveCutAdmissionAdapter : LeastPrivilegeLiveCutAdmissionAdapter
canonicalLeastPrivilegeLiveCutAdmissionAdapter = leastPrivilegeLiveCutAdmissionAdapter
  "current live-cut candidates still require ProofSearch.RouteAdmission before elaboration; salience is not capability"
  (ProofSearch.theoremNameStringIsProofCapability ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.theoremNameStringIsProofCapabilityIsFalse ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.routeMayElaborateBeforeAdmission ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.routeMayElaborateBeforeAdmissionIsFalse ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.routeMaySilentlyStrengthenHypotheses ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.routeMaySilentlyStrengthenHypothesesIsFalse ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.localLemmaAutomaticallyMovesProgrammeFrontier ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.localLemmaAutomaticallyMovesProgrammeFrontierIsFalse ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.lemmaCountIsAuthoritativeProgress ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.lemmaCountIsAuthoritativeProgressIsFalse ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.duplicateRouteShouldBeReproved ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.duplicateRouteShouldBeReprovedIsFalse ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  true refl

parentSnowballPaymentMaySkipDependency : Bool
parentSnowballPaymentMaySkipDependency = Parent.snowballPaymentMaySkipUnpaidParentDependency

parentSnowballPaymentMaySkipDependencyIsFalse : parentSnowballPaymentMaySkipDependency ≡ false
parentSnowballPaymentMaySkipDependencyIsFalse = Parent.snowballPaymentMaySkipUnpaidParentDependencyIsFalse

parentCrossDomainAnalogyCreatesAuthority : Bool
parentCrossDomainAnalogyCreatesAuthority = Parent.crossDomainAnalogyCreatesSourceAuthority

parentCrossDomainAnalogyCreatesAuthorityIsFalse : parentCrossDomainAnalogyCreatesAuthority ≡ false
parentCrossDomainAnalogyCreatesAuthorityIsFalse = Parent.crossDomainAnalogyCreatesSourceAuthorityIsFalse

record StateIndexedLiveCutParetoBoundary : Set where
  constructor stateIndexedLiveCutParetoBoundary
  field
    staleHistoricalEvidenceMustBeDeleted : Bool
    staleHistoricalEvidenceMustBeDeletedIsFalse : staleHistoricalEvidenceMustBeDeleted ≡ false
    onceUsefulExperimentAlwaysHighestSalience : Bool
    onceUsefulExperimentAlwaysHighestSalienceIsFalse : onceUsefulExperimentAlwaysHighestSalience ≡ false
    currentSalienceAutomaticallyCreatesAuthority : Bool
    currentSalienceAutomaticallyCreatesAuthorityIsFalse : currentSalienceAutomaticallyCreatesAuthority ≡ false
    currentMinimalCutAutomaticallyTransfersAcrossDomains : Bool
    currentMinimalCutAutomaticallyTransfersAcrossDomainsIsFalse : currentMinimalCutAutomaticallyTransfersAcrossDomains ≡ false
    paretoRankingMayIgnoreCurrentResidualState : Bool
    paretoRankingMayIgnoreCurrentResidualStateIsFalse : paretoRankingMayIgnoreCurrentResidualState ≡ false

open StateIndexedLiveCutParetoBoundary public

canonicalStateIndexedLiveCutParetoBoundary : StateIndexedLiveCutParetoBoundary
canonicalStateIndexedLiveCutParetoBoundary = stateIndexedLiveCutParetoBoundary
  false refl
  (Portfolio.onceUsefulExperimentAlwaysHighestSalience Portfolio.canonicalResidualConditionedPortfolioBoundary)
  (Portfolio.onceUsefulExperimentAlwaysHighestSalienceIsFalse Portfolio.canonicalResidualConditionedPortfolioBoundary)
  false refl false refl false refl
