module DASHI.Core.BenefitBurdenExternalityDistributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice

------------------------------------------------------------------------
-- BENEFIT / BURDEN / EXTERNALITY DISTRIBUTION GEOMETRY
--
-- A system-level success, aggregate output or research result does not by
-- itself identify who contributed, who benefits, who bears burden/risk, or who
-- has effective voice.  These are independent downstream consumers.
--
-- This file is source-neutral DASHI mathematics.  Climate justice,
-- industrialisation, education, formalisation, research and Indigenous
-- benefit-sharing are downstream calibration domains, not theorem authors.
------------------------------------------------------------------------

record DistributionGeometry
    (Party Aggregate Contribution Benefit Burden Voice : Set) : Set₁ where
  constructor distributionGeometry
  field
    aggregateObserver : Party → Aggregate
    contribution : Party → Contribution
    benefit : Party → Benefit
    burden : Party → Burden
    voice : Party → Voice

open DistributionGeometry public

------------------------------------------------------------------------
-- Finite structural witness.
------------------------------------------------------------------------

data DemoParty : Set where
  contributingBeneficiary affectedLowVoiceParty : DemoParty

data DemoAggregate : Set where sameAggregateSuccess : DemoAggregate

data DemoContribution : Set where lowContribution highContribution : DemoContribution

data DemoBenefit : Set where lowBenefit highBenefit : DemoBenefit

data DemoBurden : Set where lowBurden highBurden : DemoBurden

data DemoVoice : Set where lowVoice highVoice : DemoVoice

demoAggregate : DemoParty → DemoAggregate
demoAggregate _ = sameAggregateSuccess

demoContribution : DemoParty → DemoContribution
demoContribution contributingBeneficiary = highContribution
demoContribution affectedLowVoiceParty = lowContribution

demoBenefit : DemoParty → DemoBenefit
demoBenefit contributingBeneficiary = highBenefit
demoBenefit affectedLowVoiceParty = lowBenefit

demoBurden : DemoParty → DemoBurden
demoBurden contributingBeneficiary = lowBurden
demoBurden affectedLowVoiceParty = highBurden

demoVoice : DemoParty → DemoVoice
demoVoice contributingBeneficiary = highVoice
demoVoice affectedLowVoiceParty = lowVoice

demoDistributionGeometry :
  DistributionGeometry
    DemoParty DemoAggregate DemoContribution DemoBenefit DemoBurden DemoVoice
demoDistributionGeometry =
  distributionGeometry
    demoAggregate demoContribution demoBenefit demoBurden demoVoice

aggregateCannotRecoverContribution :
  INF.FactorsThrough demoAggregate demoContribution → ⊥
aggregateCannotRecoverContribution =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      contributingBeneficiary affectedLowVoiceParty refl (λ ()))

aggregateCannotRecoverBenefit :
  INF.FactorsThrough demoAggregate demoBenefit → ⊥
aggregateCannotRecoverBenefit =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      contributingBeneficiary affectedLowVoiceParty refl (λ ()))

aggregateCannotRecoverBurden :
  INF.FactorsThrough demoAggregate demoBurden → ⊥
aggregateCannotRecoverBurden =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      contributingBeneficiary affectedLowVoiceParty refl (λ ()))

aggregateCannotRecoverVoice :
  INF.FactorsThrough demoAggregate demoVoice → ⊥
aggregateCannotRecoverVoice =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      contributingBeneficiary affectedLowVoiceParty refl (λ ()))

------------------------------------------------------------------------
-- Distributional coverage is distinct from an aggregate outcome receipt.
------------------------------------------------------------------------

data ContributionCoverage : Set where contributionCovered : ContributionCoverage
data BenefitCoverage : Set where benefitCovered : BenefitCoverage
data BurdenCoverage : Set where burdenCovered : BurdenCoverage
data VoiceCoverage : Set where voiceCovered : VoiceCoverage

record DistributionalCoverage : Set where
  constructor distributionalCoverage
  field
    contributionCoverage : ContributionCoverage
    benefitCoverage : BenefitCoverage
    burdenCoverage : BurdenCoverage
    voiceCoverage : VoiceCoverage

canonicalDistributionalCoverage : DistributionalCoverage
canonicalDistributionalCoverage =
  distributionalCoverage
    contributionCovered benefitCovered burdenCovered voiceCovered

------------------------------------------------------------------------
-- Experiment/proof-search cost is not a welfare or externality metric.
------------------------------------------------------------------------

data ResearchStrategy : Set where
  institutionCentredStrategy distributionAwareStrategy : ResearchStrategy

strategyMove : ResearchStrategy → Choice.InformationMove
strategyMove institutionCentredStrategy =
  Choice.informationMove
    Choice.takeMeasurement
    (suc zero)
    "institution-centred information move"
    "declared search/resource cost only"
    "domain-specific admissibility still required"
strategyMove distributionAwareStrategy =
  Choice.informationMove
    Choice.takeMeasurement
    (suc zero)
    "distribution-aware information move"
    "declared search/resource cost only"
    "affected-party/distributional admissibility required"

strategyCost : ResearchStrategy → Nat
strategyCost strategy = Choice.cost (strategyMove strategy)

data StrategyBenefitRoute : Set where
  concentratedBenefitRoute sharedBenefitRoute : StrategyBenefitRoute

data StrategyExternalBurden : Set where
  highExternalBurden lowExternalBurden : StrategyExternalBurden

data StrategyAffectedVoice : Set where
  affectedVoiceMissing affectedVoiceRepresented : StrategyAffectedVoice

strategyBenefitRoute : ResearchStrategy → StrategyBenefitRoute
strategyBenefitRoute institutionCentredStrategy = concentratedBenefitRoute
strategyBenefitRoute distributionAwareStrategy = sharedBenefitRoute

strategyExternalBurden : ResearchStrategy → StrategyExternalBurden
strategyExternalBurden institutionCentredStrategy = highExternalBurden
strategyExternalBurden distributionAwareStrategy = lowExternalBurden

strategyAffectedVoice : ResearchStrategy → StrategyAffectedVoice
strategyAffectedVoice institutionCentredStrategy = affectedVoiceMissing
strategyAffectedVoice distributionAwareStrategy = affectedVoiceRepresented

sameDeclaredSearchCost :
  strategyCost institutionCentredStrategy ≡
  strategyCost distributionAwareStrategy
sameDeclaredSearchCost = refl

costCannotRecoverBenefitRoute :
  INF.FactorsThrough strategyCost strategyBenefitRoute → ⊥
costCannotRecoverBenefitRoute =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      institutionCentredStrategy distributionAwareStrategy refl (λ ()))

costCannotRecoverExternalBurden :
  INF.FactorsThrough strategyCost strategyExternalBurden → ⊥
costCannotRecoverExternalBurden =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      institutionCentredStrategy distributionAwareStrategy refl (λ ()))

costCannotRecoverAffectedVoice :
  INF.FactorsThrough strategyCost strategyAffectedVoice → ⊥
costCannotRecoverAffectedVoice =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      institutionCentredStrategy distributionAwareStrategy refl (λ ()))

------------------------------------------------------------------------
-- Cross-domain calibration vocabulary.  The constructors do not assert an
-- empirical distribution in any named domain; they state which questions an
-- application may need to instantiate.
------------------------------------------------------------------------

data DistributionDomain : Set where
  climate industrialisation education formalisation research : DistributionDomain

data DistributionQuestion : Set where
  whoContributed whoBenefits whoBearsBurden whoHasVoice : DistributionQuestion

domainQuestion : DistributionDomain → DistributionQuestion → String
domainQuestion climate whoContributed = "climate contribution/responsibility distribution"
domainQuestion climate whoBenefits = "benefit distribution from mitigation/adaptation/provisioning"
domainQuestion climate whoBearsBurden = "climate harm/transition/adaptation burden distribution"
domainQuestion climate whoHasVoice = "affected-party representation in climate decisions"
domainQuestion industrialisation whoContributed = "labour/material/ecological contribution"
domainQuestion industrialisation whoBenefits = "surplus/productivity/service benefit distribution"
domainQuestion industrialisation whoBearsBurden = "labour/ecological/displacement burden distribution"
domainQuestion industrialisation whoHasVoice = "worker/community governance representation"
domainQuestion education whoContributed = "learner/teacher/community contribution"
domainQuestion education whoBenefits = "learning/institutional/policy benefit distribution"
domainQuestion education whoBearsBurden = "assessment/workload/exclusion/intervention burden distribution"
domainQuestion education whoHasVoice = "learner/teacher/community epistemic and decision voice"
domainQuestion formalisation whoContributed = "source/translator/formaliser/reviewer contribution"
domainQuestion formalisation whoBenefits = "machine-checkability/reuse/status benefit distribution"
domainQuestion formalisation whoBearsBurden = "translation/maintenance/semantic-loss burden distribution"
domainQuestion formalisation whoHasVoice = "source-community/consumer representation in formalisation"
domainQuestion research whoContributed = "knowledge/data/participation/research contribution"
domainQuestion research whoBenefits = "publication/commercial/community/public benefit distribution"
domainQuestion research whoBearsBurden = "participation/extraction/risk/opportunity-cost burden distribution"
domainQuestion research whoHasVoice = "agenda/method/interpretation/downstream-use authority"

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record BenefitBurdenExternalityBoundary : Set where
  constructor benefit-burden-externality-boundary
  field
    aggregateSuccessDeterminesContribution : Bool
    aggregateSuccessDeterminesContributionIsFalse :
      aggregateSuccessDeterminesContribution ≡ false
    aggregateSuccessDeterminesBenefit : Bool
    aggregateSuccessDeterminesBenefitIsFalse :
      aggregateSuccessDeterminesBenefit ≡ false
    aggregateSuccessDeterminesBurden : Bool
    aggregateSuccessDeterminesBurdenIsFalse :
      aggregateSuccessDeterminesBurden ≡ false
    aggregateSuccessDeterminesVoice : Bool
    aggregateSuccessDeterminesVoiceIsFalse :
      aggregateSuccessDeterminesVoice ≡ false
    equalDeclaredExperimentCostMeansEqualExternality : Bool
    equalDeclaredExperimentCostMeansEqualExternalityIsFalse :
      equalDeclaredExperimentCostMeansEqualExternality ≡ false
    equalDeclaredExperimentCostMeansEqualBenefitDistribution : Bool
    equalDeclaredExperimentCostMeansEqualBenefitDistributionIsFalse :
      equalDeclaredExperimentCostMeansEqualBenefitDistribution ≡ false
    distributionalCoverageSettlesSubstantiveJustice : Bool
    distributionalCoverageSettlesSubstantiveJusticeIsFalse :
      distributionalCoverageSettlesSubstantiveJustice ≡ false

canonicalBenefitBurdenExternalityBoundary : BenefitBurdenExternalityBoundary
canonicalBenefitBurdenExternalityBoundary =
  benefit-burden-externality-boundary
    false refl false refl false refl false refl false refl false refl false refl
