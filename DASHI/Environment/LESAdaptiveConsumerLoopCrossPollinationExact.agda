module DASHI.Environment.LESAdaptiveConsumerLoopCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdaptiveConsumerModelLoopExact as Loop
import DASHI.Core.ConsumerRelativeReductionCanonicalBridgeExact as Canonical
import DASHI.Core.ConsumerRelativeReductionSearchExact as Search
import DASHI.Core.ConsumerRelativeMinimalFidelityExact as Minimal
import DASHI.Core.ConsumerRelativeApproximateFidelityBridgeExact as Approx
import DASHI.Core.ConsumerReductionDependencyReopeningExact as Reopening
import DASHI.Core.RobustInterventionAcrossHypothesesExact as Robust
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Sequential
import DASHI.Core.SequentialRobustActionabilityPlannerExact as SequentialAction
import DASHI.Core.JointSequentialInformationFidelityPolicyExact as Joint
import DASHI.Environment.LESSPACFidelityCounterexampleFixturesExact as Fixtures
import DASHI.Environment.LESDiscriminatorSynthesisExact as LESSynthesis
import DASHI.Environment.LESSequentialExperimentPlannerExact as LESSequential
import DASHI.Environment.LESJointSequentialMeasurementFidelityPolicyExact as LESJoint

adaptiveConsumerLoopOwner : String
adaptiveConsumerLoopOwner = "DASHI.Core.AdaptiveConsumerModelLoopExact"

canonicalFutureBridgeOwner : String
canonicalFutureBridgeOwner = "DASHI.Core.ConsumerRelativeReductionCanonicalBridgeExact"

reductionSearchOwner : String
reductionSearchOwner = "DASHI.Core.ConsumerRelativeReductionSearchExact"

minimalFidelityOwner : String
minimalFidelityOwner = "DASHI.Core.ConsumerRelativeMinimalFidelityExact"

approximateFidelityOwner : String
approximateFidelityOwner = "DASHI.Core.ConsumerRelativeApproximateFidelityBridgeExact"

robustInterventionOwner : String
robustInterventionOwner = "DASHI.Core.RobustInterventionAcrossHypothesesExact"

selectiveReopeningOwner : String
selectiveReopeningOwner = "DASHI.Core.ConsumerReductionDependencyReopeningExact"

discriminatorSynthesisOwner : String
discriminatorSynthesisOwner = "DASHI.Core.DiscriminatorSynthesisExact"

sequentialExperimentPlannerOwner : String
sequentialExperimentPlannerOwner = "DASHI.Core.SequentialConsumerExperimentPlannerExact"

sequentialActionabilityPlannerOwner : String
sequentialActionabilityPlannerOwner = "DASHI.Core.SequentialRobustActionabilityPlannerExact"

jointSequentialPolicyOwner : String
jointSequentialPolicyOwner = "DASHI.Core.JointSequentialInformationFidelityPolicyExact"

lesDiscriminatorSynthesisOwner : String
lesDiscriminatorSynthesisOwner = "DASHI.Environment.LESDiscriminatorSynthesisExact"

lesSequentialExperimentOwner : String
lesSequentialExperimentOwner = "DASHI.Environment.LESSequentialExperimentPlannerExact"

lesJointMeasurementFidelityOwner : String
lesJointMeasurementFidelityOwner = "DASHI.Environment.LESJointSequentialMeasurementFidelityPolicyExact"

finiteSPACCounterexampleOwner : String
finiteSPACCounterexampleOwner = "DASHI.Environment.LESSPACFidelityCounterexampleFixturesExact"

loopBoundaryImported : Loop.AdaptiveConsumerLoopBoundary
loopBoundaryImported = Loop.canonicalAdaptiveConsumerLoopBoundary

minimalBoundaryImported : Minimal.MinimalFidelityBoundary
minimalBoundaryImported = Minimal.canonicalMinimalFidelityBoundary

approximateBoundaryImported : Approx.ConsumerApproximateFidelityBoundary
approximateBoundaryImported = Approx.canonicalConsumerApproximateFidelityBoundary

robustBoundaryImported : Robust.RobustInterventionBoundary
robustBoundaryImported = Robust.canonicalRobustInterventionBoundary

reopeningBoundaryImported : Reopening.ReductionDependencyReopeningBoundary
reopeningBoundaryImported = Reopening.canonicalReductionDependencyReopeningBoundary

discriminatorBoundaryImported : Synthesis.DiscriminatorSynthesisBoundary
discriminatorBoundaryImported = Synthesis.canonicalDiscriminatorSynthesisBoundary

sequentialBoundaryImported : Sequential.SequentialExperimentPlannerBoundary
sequentialBoundaryImported = Sequential.canonicalSequentialExperimentPlannerBoundary

sequentialActionBoundaryImported : SequentialAction.SequentialActionabilityPlannerBoundary
sequentialActionBoundaryImported = SequentialAction.canonicalSequentialActionabilityPlannerBoundary

jointBoundaryImported : Joint.JointSequentialPolicyBoundary
jointBoundaryImported = Joint.canonicalJointSequentialPolicyBoundary

lesDiscriminatorBoundaryImported : LESSynthesis.LESDiscriminatorSynthesisBoundary
lesDiscriminatorBoundaryImported = LESSynthesis.canonicalLESDiscriminatorSynthesisBoundary

lesSequentialBoundaryImported : LESSequential.LESSequentialExperimentBoundary
lesSequentialBoundaryImported = LESSequential.canonicalLESSequentialExperimentBoundary

lesJointBoundaryImported : LESJoint.LESJointMeasurementFidelityBoundary
lesJointBoundaryImported = LESJoint.canonicalLESJointMeasurementFidelityBoundary

fixtureBoundaryImported : Fixtures.SPACFidelityCounterexampleBoundary
fixtureBoundaryImported = Fixtures.canonicalSPACFidelityCounterexampleBoundary

record LESAdaptiveConsumerArchitectureCutset : Set where
  constructor lesAdaptiveConsumerArchitectureCutset
  field
    fineWorldStateExplicit candidateConsumerReductionExplicit : Bool
    exactCertificateBranchTyped approximateDecisionMarginBranchTyped : Bool
    futureCounterexampleBranchTyped exactBranchMapsToCanonicalFutureSafety : Bool
    approximateBranchMapsToDecisionSafety counterexampleBranchRefutesConsumerCandidate : Bool
    reopenablePortfolioTyped liveEvidenceFibreTyped : Bool
    robustInterventionBranchTyped authorityRemainsSeparateFromRobustness : Bool
    discriminatingMeasurementOrFidelityBranchTyped evidenceUpdateTyped : Bool
    selectiveDependencyReopeningTyped minimalSufficientFidelityCertificateTyped : Bool
    pairwiseDiscriminatorSynthesisTyped prospectiveConsumerClosingBundleTyped : Bool
    observerJoinRefinementTyped nuisanceRobustSeparatorTyped : Bool
    optionalSymmetryInvariantExperimentTyped lesActionabilitySynthesisTyped : Bool
    outcomeAdaptiveSequentialExperimentTreeTyped : Bool
    impossibleMeasurementOutcomesPrunedByRealizabilityWitness : Bool
    worstCaseSequentialCostCertificateTyped : Bool
    sequentialPlanMayStopAtConsumerClosureWithoutWorldIdentity : Bool
    sequentialActionabilityPlanMayStopAtRobustAuthorisedControl : Bool
    jointMeasurementFidelityPolicyTyped : Bool
    fidelityTransitionKeepsLiveFibreTyped : Bool
    evidenceTransitionRefinesLiveFibreTyped : Bool
    jointWorstCaseCostObjectiveTyped : Bool
    jointPolicyMayStopAtRobustAuthorisedControl : Bool
    bucketHydraulicCounterexampleFixturePresent : Bool
    richardsPlantHistoryCounterexampleFixturePresent : Bool
    hydraulicSPACNutrientCounterexampleFixturePresent : Bool
open LESAdaptiveConsumerArchitectureCutset public

canonicalLESAdaptiveConsumerArchitectureCutset : LESAdaptiveConsumerArchitectureCutset
canonicalLESAdaptiveConsumerArchitectureCutset =
  lesAdaptiveConsumerArchitectureCutset
    true true true true true true true true true true
    true true true true true true true true true true
    true true true true true true true true true true
    true true true true true

record LESAdaptiveConsumerArchitectureBoundary : Set where
  constructor lesAdaptiveConsumerArchitectureBoundary
  field
    exactFutureSafetyEqualsWorldIdentity : Bool
    exactFutureSafetyEqualsWorldIdentityIsFalse : exactFutureSafetyEqualsWorldIdentity ≡ false
    approximateDecisionSafetyEqualsExactFutureQuotient : Bool
    approximateDecisionSafetyEqualsExactFutureQuotientIsFalse : approximateDecisionSafetyEqualsExactFutureQuotient ≡ false
    cheapestModelAutomaticallyWins : Bool
    cheapestModelAutomaticallyWinsIsFalse : cheapestModelAutomaticallyWins ≡ false
    richestModelAutomaticallyWins : Bool
    richestModelAutomaticallyWinsIsFalse : richestModelAutomaticallyWins ≡ false
    unresolvedModelFibreAlwaysBlocksAction : Bool
    unresolvedModelFibreAlwaysBlocksActionIsFalse : unresolvedModelFibreAlwaysBlocksAction ≡ false
    robustActionAutomaticallyAuthorized : Bool
    robustActionAutomaticallyAuthorizedIsFalse : robustActionAutomaticallyAuthorized ≡ false
    pairwiseDiscriminatorAutomaticallyClosesWholeDecisionFibre : Bool
    pairwiseDiscriminatorAutomaticallyClosesWholeDecisionFibreIsFalse :
      pairwiseDiscriminatorAutomaticallyClosesWholeDecisionFibre ≡ false
    sequentialPlanningRequiresFixedMeasurementOrder : Bool
    sequentialPlanningRequiresFixedMeasurementOrderIsFalse :
      sequentialPlanningRequiresFixedMeasurementOrder ≡ false
    robustAuthorisedActionRequiresFullModelIdentification : Bool
    robustAuthorisedActionRequiresFullModelIdentificationIsFalse :
      robustAuthorisedActionRequiresFullModelIdentification ≡ false
    richerModelAutomaticallyCreatesNewEmpiricalEvidence : Bool
    richerModelAutomaticallyCreatesNewEmpiricalEvidenceIsFalse :
      richerModelAutomaticallyCreatesNewEmpiricalEvidence ≡ false
    oneChangedDependencyReopensEntireRepository : Bool
    oneChangedDependencyReopensEntireRepositoryIsFalse : oneChangedDependencyReopensEntireRepository ≡ false
    syntheticCounterexampleFixtureIsPhysicalValidation : Bool
    syntheticCounterexampleFixtureIsPhysicalValidationIsFalse : syntheticCounterexampleFixtureIsPhysicalValidation ≡ false

canonicalLESAdaptiveConsumerArchitectureBoundary : LESAdaptiveConsumerArchitectureBoundary
canonicalLESAdaptiveConsumerArchitectureBoundary =
  lesAdaptiveConsumerArchitectureBoundary
    false refl false refl false refl false refl false refl false refl
    false refl false refl false refl false refl false refl false refl
