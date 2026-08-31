module DASHI.Governance.DistributionalExternalityCrossDomainExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BenefitBurdenExternalityDistributionExact as Dist
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.ExecutionGovernanceClosureAssayExact as Execution
import DASHI.Governance.ConstitutionalAxisResidualCapabilityExact as Constitutional
import DASHI.Governance.SultanaClimateColonialityResidualExact as Climate
import DASHI.Governance.SocioTechnicalPowerSelectionAssayExact as Industrial
import DASHI.Governance.FormalisationGovernanceCapstoneExact as Formalisation
import DASHI.Governance.RecognitionDistributionRepresentationAxesExact as Fraser
import DASHI.Governance.SmithResearchAgendaAuthorityBoundaryExact as Smith
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK

------------------------------------------------------------------------
-- DISTRIBUTIONAL EXTERNALITY CROSS-DOMAIN ADAPTER
--
-- Generic spine:
--
--   who contributes
--   != who benefits
--   != who bears burden/risk
--   != who has voice/authority.
--
-- Existing source-bound owners are reused only as calibration/instantiation
-- surfaces.  No climate, feminist, Indigenous, education, labour or research
-- source is credited with the generic finite DASHI theorem.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. High-impact execution must carry affected-party/distributional coverage.
------------------------------------------------------------------------

record DistributionallyCoveredHighImpact : Set where
  constructor distributionallyCoveredHighImpact
  field
    constitutionalCoverage : Constitutional.ConstitutionalCoverage
    distributionalCoverage : Dist.DistributionalCoverage

canonicalDistributionallyCoveredHighImpact : DistributionallyCoveredHighImpact
canonicalDistributionallyCoveredHighImpact =
  distributionallyCoveredHighImpact
    Constitutional.canonicalConstitutionalCoverage
    Dist.canonicalDistributionalCoverage

data DistributionResidual : Set where
  distributionResolved distributionUnresolved : DistributionResidual

executionCoverage : DistributionResidual → Execution.CoverageState
executionCoverage distributionResolved = Execution.completeCoverage
executionCoverage distributionUnresolved = Execution.unresolvedExternality

unresolvedDistributionBlocksIrreversibleExecution :
  Execution.AutonomousExecution
    Execution.irreversibleHighConsequence
    (executionCoverage distributionUnresolved) → ⊥
unresolvedDistributionBlocksIrreversibleExecution =
  Execution.unresolvedHighConsequenceBlocksAutonomousExecution

------------------------------------------------------------------------
-- 2. Climate: aggregate outcome != contribution/burden distribution.
------------------------------------------------------------------------

climateResponsibilityBurdenBoundary : Climate.SultanaClimateColonialityBoundary
climateResponsibilityBurdenBoundary =
  Climate.canonicalSultanaClimateColonialityBoundary

climateAggregateStillDoesNotRecoverBurden :
  INF.FactorsThrough
    (Dist.aggregateObserver Dist.demoDistributionGeometry)
    (Dist.burden Dist.demoDistributionGeometry) → ⊥
climateAggregateStillDoesNotRecoverBurden = Dist.aggregateCannotRecoverBurden

-- The generic benefit/voice axes are additions to the DASHI distributional
-- geometry.  They are not attributed to the Sultana source owner.

------------------------------------------------------------------------
-- 3. Industrialisation: productivity/machinery surface != surplus/power route.
------------------------------------------------------------------------

industrialPowerBoundary : Industrial.SocioTechnicalPowerSelectionBoundary
industrialPowerBoundary = Industrial.canonicalSocioTechnicalPowerSelectionBoundary

industrialSameMachineryStillDoesNotFixDistribution : String
industrialSameMachineryStillDoesNotFixDistribution =
  "Same machinery or functional service does not determine labour power, surplus routing, ecological fit or political voice; the generic distribution geometry adds explicit benefit/burden consumers without turning the synthetic industrial assay into an empirical history law."

------------------------------------------------------------------------
-- 4. Education: same aggregate learning surface can hide burden and voice.
--
-- Synthetic DASHI fixture only.  It does not assert that a named pedagogy,
-- school system, teacher or learner population has either state.
------------------------------------------------------------------------

data EducationDistributionState : Set where
  sameGainLowLearnerBurden sameGainHighLearnerBurden : EducationDistributionState

data EducationAggregate : Set where sameMeasuredLearningGain : EducationAggregate

data LearnerBurden : Set where lowerLearnerBurden higherLearnerBurden : LearnerBurden

data LearnerVoice : Set where learnerVoiceRepresented learnerVoiceMissing : LearnerVoice

educationAggregate : EducationDistributionState → EducationAggregate
educationAggregate _ = sameMeasuredLearningGain

learnerBurden : EducationDistributionState → LearnerBurden
learnerBurden sameGainLowLearnerBurden = lowerLearnerBurden
learnerBurden sameGainHighLearnerBurden = higherLearnerBurden

learnerVoice : EducationDistributionState → LearnerVoice
learnerVoice sameGainLowLearnerBurden = learnerVoiceRepresented
learnerVoice sameGainHighLearnerBurden = learnerVoiceMissing

aggregateLearningGainCannotRecoverLearnerBurden :
  INF.FactorsThrough educationAggregate learnerBurden → ⊥
aggregateLearningGainCannotRecoverLearnerBurden =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameGainLowLearnerBurden sameGainHighLearnerBurden refl (λ ()))

aggregateLearningGainCannotRecoverLearnerVoice :
  INF.FactorsThrough educationAggregate learnerVoice → ⊥
aggregateLearningGainCannotRecoverLearnerVoice =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameGainLowLearnerBurden sameGainHighLearnerBurden refl (λ ()))

------------------------------------------------------------------------
-- 5. Formalisation: formal success/recognition != distribution/representation.
------------------------------------------------------------------------

formalisationBoundary : Formalisation.ThreeStoreyBoundary
formalisationBoundary = Formalisation.canonicalThreeStoreyBoundary

formalisationRecognitionDoesNotRecoverDistribution :
  INF.FactorsThrough Fraser.recognition Fraser.distribution → ⊥
formalisationRecognitionDoesNotRecoverDistribution =
  Formalisation.recognitionDoesNotRecoverDistribution

formalisationDistributionDoesNotRecoverRepresentation :
  INF.FactorsThrough Fraser.distribution Fraser.representation → ⊥
formalisationDistributionDoesNotRecoverRepresentation =
  Formalisation.distributionDoesNotRecoverRepresentation

------------------------------------------------------------------------
-- 6. Research: correctness, agenda authority and benefit sharing are distinct.
------------------------------------------------------------------------

researchAgendaBoundary : Smith.SmithAgendaBoundary
researchAgendaBoundary = Smith.canonicalSmithAgendaBoundary

scientificResultStillDoesNotRecoverBenefitSharing :
  INF.FactorsThrough IK.scientificResult IK.benefitSharingStatus → ⊥
scientificResultStillDoesNotRecoverBenefitSharing =
  IK.scientificResultCannotRecoverBenefitSharing

scientificResultStillDoesNotRecoverConsent :
  INF.FactorsThrough IK.scientificResult IK.accessStatus → ⊥
scientificResultStillDoesNotRecoverConsent =
  IK.scientificResultCannotRecoverConsent

------------------------------------------------------------------------
-- 7. Experiment-selection consequence.
--
-- The existing ActionabilityCostedExperimentChoice cost is intentionally a
-- search/resource order, not a welfare function.  The core fixture now makes
-- that non-identification mechanical: equal declared cost can hide different
-- benefit, burden and affected-party voice.
------------------------------------------------------------------------

equalExperimentCostDoesNotRecoverExternalBurden :
  INF.FactorsThrough Dist.strategyCost Dist.strategyExternalBurden → ⊥
equalExperimentCostDoesNotRecoverExternalBurden =
  Dist.costCannotRecoverExternalBurden

equalExperimentCostDoesNotRecoverBenefitRoute :
  INF.FactorsThrough Dist.strategyCost Dist.strategyBenefitRoute → ⊥
equalExperimentCostDoesNotRecoverBenefitRoute =
  Dist.costCannotRecoverBenefitRoute

equalExperimentCostDoesNotRecoverAffectedVoice :
  INF.FactorsThrough Dist.strategyCost Dist.strategyAffectedVoice → ⊥
equalExperimentCostDoesNotRecoverAffectedVoice =
  Dist.costCannotRecoverAffectedVoice

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record DistributionalExternalityCrossDomainBoundary : Set where
  constructor distributional-externality-cross-domain-boundary
  field
    aggregateSuccessMeansBenefitsAndBurdensAreEquitablyDistributed : Bool
    aggregateSuccessMeansBenefitsAndBurdensAreEquitablyDistributedIsFalse :
      aggregateSuccessMeansBenefitsAndBurdensAreEquitablyDistributed ≡ false
    cheapestExperimentMeansLowestAffectedPartyBurden : Bool
    cheapestExperimentMeansLowestAffectedPartyBurdenIsFalse :
      cheapestExperimentMeansLowestAffectedPartyBurden ≡ false
    technicallyCorrectResearchMeansCommunityAuthorizedAgenda : Bool
    technicallyCorrectResearchMeansCommunityAuthorizedAgendaIsFalse :
      technicallyCorrectResearchMeansCommunityAuthorizedAgenda ≡ false
    scientificBenefitMeansBenefitSharingOccurred : Bool
    scientificBenefitMeansBenefitSharingOccurredIsFalse :
      scientificBenefitMeansBenefitSharingOccurred ≡ false
    aggregateLearningGainMeansLearnerBurdenAndVoiceAreAdequate : Bool
    aggregateLearningGainMeansLearnerBurdenAndVoiceAreAdequateIsFalse :
      aggregateLearningGainMeansLearnerBurdenAndVoiceAreAdequate ≡ false
    formalisationSuccessMeansDistributionAndRepresentationAreAdequate : Bool
    formalisationSuccessMeansDistributionAndRepresentationAreAdequateIsFalse :
      formalisationSuccessMeansDistributionAndRepresentationAreAdequate ≡ false
    unresolvedDistributionPermitsIrreversibleHighImpactExecution : Bool
    unresolvedDistributionPermitsIrreversibleHighImpactExecutionIsFalse :
      unresolvedDistributionPermitsIrreversibleHighImpactExecution ≡ false
    distributionalCoverageAutomaticallySettlesJustice : Bool
    distributionalCoverageAutomaticallySettlesJusticeIsFalse :
      distributionalCoverageAutomaticallySettlesJustice ≡ false

canonicalDistributionalExternalityCrossDomainBoundary :
  DistributionalExternalityCrossDomainBoundary
canonicalDistributionalExternalityCrossDomainBoundary =
  distributional-externality-cross-domain-boundary
    false refl false refl false refl false refl
    false refl false refl false refl false refl
