module DASHI.Finance.DeepStatArbFibrePipelineExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Finance.TemporalMarketFibreExact as Temporal
import DASHI.Finance.PointInTimeUniverseFibreExact as PIT

------------------------------------------------------------------------
-- Residual statistical arbitrage as fibre morphisms over time.
--
-- The neural architecture is deliberately abstracted behind a policy socket.
-- What is formalised here is the causal/provenance shape: market fibre ->
-- residual fibre -> learned policy -> portfolio fibre -> execution fibre ->
-- realised-return fibre, with no authority promotion by projection alone.
------------------------------------------------------------------------

data FactorMethod : Set where
  famaFrench5 : FactorMethod
  pca : FactorMethod
  ipca : FactorMethod
  learnedConditionalFactors : FactorMethod
  attentionFactors : FactorMethod

record ResidualFibre : Set where
  constructor residualFibre
  field
    residualTime : Nat
    factorMethod : FactorMethod
    residualPayload : String
    fitReceipt : String
    sourceUniverse : PIT.UniverseFibre
    residualProvenance : String

open ResidualFibre public

record ResidualProjection
    (market : Temporal.MarketFibre)
    (residual : ResidualFibre) : Set where
  constructor residualProjection
  field
    sameTime : residualTime residual ≡ Temporal.time market
    causalFit : Bool
    causalFitIsTrue : causalFit ≡ true
    projectionCreatesMispricingTruth : Bool
    projectionCreatesMispricingTruthIsFalse :
      projectionCreatesMispricingTruth ≡ false

open ResidualProjection public

record RollingProtocol : Set where
  constructor rollingProtocol
  field
    trainingDays : Nat
    testingDays : Nat
    pointInTime : Bool
    pointInTimeIsTrue : pointInTime ≡ true
    testFeedsTraining : Bool
    testFeedsTrainingIsFalse : testFeedsTraining ≡ false

open RollingProtocol public

longXiaoProtocol : RollingProtocol
longXiaoProtocol =
  rollingProtocol 1000 125 true refl false refl

------------------------------------------------------------------------
-- Architecture sockets.  CNN+Transformer and newer sequence models inhabit
-- the same extensional policy carrier; their internal approximation theory is
-- not confused with PIT/backtest validity.
------------------------------------------------------------------------

data SequenceArchitecture : Set where
  cnnTransformer : SequenceArchitecture
  genericSequenceModel : SequenceArchitecture
  otherCausalSequenceModel : SequenceArchitecture

record LearnedPolicy : Set where
  constructor learnedPolicy
  field
    architecture : SequenceArchitecture
    trainingReceipt : String
    policyPayload : String
    usesOnlyAvailableResidualHistory : Bool
    usesOnlyAvailableResidualHistoryIsTrue :
      usesOnlyAvailableResidualHistory ≡ true

open LearnedPolicy public

record PortfolioFibre : Set where
  constructor portfolioFibre
  field
    portfolioTime : Nat
    weightPayload : String
    constraintReceipt : String
    dollarNeutral : Bool

open PortfolioFibre public

record PolicyMorphism
    (residual : ResidualFibre)
    (policy : LearnedPolicy)
    (portfolio : PortfolioFibre) : Set where
  constructor policyMorphism
  field
    decisionAtResidualTime : portfolioTime portfolio ≡ residualTime residual
    policyCausal : usesOnlyAvailableResidualHistory policy ≡ true
    constraintsChecked : Bool
    constraintsCheckedIsTrue : constraintsChecked ≡ true

open PolicyMorphism public

record ExecutionFibre : Set where
  constructor executionFibre
  field
    executionTime : Nat
    fillPayload : String
    costPayload : String
    impactPayload : String
    executionProvenance : String

open ExecutionFibre public

record ExecutionTransport
    (portfolio : PortfolioFibre)
    (execution : ExecutionFibre) : Set where
  constructor executionTransport
  field
    forwardExecution : Temporal.ForwardPath (portfolioTime portfolio) (executionTime execution)
    costsAccounted : Bool
    costsAccountedIsTrue : costsAccounted ≡ true

open ExecutionTransport public

record ReturnFibre : Set where
  constructor returnFibre
  field
    returnTime : Nat
    grossReturnPayload : String
    netReturnPayload : String
    returnProvenance : String
    unresolvedResidual : String

open ReturnFibre public

record RealisedReturnTransport
    (execution : ExecutionFibre)
    (ret : ReturnFibre) : Set where
  constructor realisedReturnTransport
  field
    realisedForward : Temporal.ForwardPath (executionTime execution) (returnTime ret)
    netDerivedAfterCosts : Bool
    netDerivedAfterCostsIsTrue : netDerivedAfterCosts ≡ true

open RealisedReturnTransport public

------------------------------------------------------------------------
-- Performance is a contraction of an already-realised return braid.  The
-- metric does not erase residual qualification or create deployment authority.
------------------------------------------------------------------------

record PerformanceContraction : Set where
  constructor performanceContraction
  field
    metricLabel : String
    metricValue : String
    returnBraidReceipt : String
    residualQualification : String
    metricCreatesFutureProfitGuarantee : Bool
    metricCreatesFutureProfitGuaranteeIsFalse :
      metricCreatesFutureProfitGuarantee ≡ false

open PerformanceContraction public

record SharpeAuthorityBoundary : Set where
  constructor sharpeAuthorityBoundary
  field
    grossSharpeEqualsNetSharpeAutomatically : Bool
    grossSharpeEqualsNetSharpeAutomaticallyIsFalse :
      grossSharpeEqualsNetSharpeAutomatically ≡ false
    highHistoricalSharpeImpliesFutureArbitrage : Bool
    highHistoricalSharpeImpliesFutureArbitrageIsFalse :
      highHistoricalSharpeImpliesFutureArbitrage ≡ false

canonicalSharpeAuthorityBoundary : SharpeAuthorityBoundary
canonicalSharpeAuthorityBoundary =
  sharpeAuthorityBoundary false refl false refl

------------------------------------------------------------------------
-- Cross-pollinated SOTA sockets.
--
-- DLSA: residualisation and trading policy may be separate.
-- Attention Factors: factor construction and trading objective may be jointly
-- learned after costs.
-- Robust stat-arb: profitability may be required over an ambiguity family.
------------------------------------------------------------------------

data StatArbFamily : Set where
  residualThenPolicy : StatArbFamily
  jointFactorPolicy : StatArbFamily
  robustAmbiguityPolicy : StatArbFamily

record JointFactorPolicyCertificate : Set where
  constructor jointFactorPolicyCertificate
  field
    family : StatArbFamily
    jointlyLearned : Bool
    afterCostObjective : Bool
    trainingProvenance : String
    jointLearningCreatesCausalValidity : Bool
    jointLearningCreatesCausalValidityIsFalse :
      jointLearningCreatesCausalValidity ≡ false

open JointFactorPolicyCertificate public

attentionFactorSocket : JointFactorPolicyCertificate
attentionFactorSocket =
  jointFactorPolicyCertificate
    jointFactorPolicy
    true
    true
    "Attention Factors: conditional latent factors and trading policy jointly estimated for after-cost performance"
    false refl

record AmbiguityRobustnessCertificate : Set where
  constructor ambiguityRobustnessCertificate
  field
    family : StatArbFamily
    ambiguitySetReceipt : String
    robustObjectiveReceipt : String
    sampleProfitImpliesRobustProfit : Bool
    sampleProfitImpliesRobustProfitIsFalse :
      sampleProfitImpliesRobustProfit ≡ false

open AmbiguityRobustnessCertificate public

robustStatArbSocket : AmbiguityRobustnessCertificate
robustStatArbSocket =
  ambiguityRobustnessCertificate
    robustAmbiguityPolicy
    "data-derived admissible probability family"
    "profitability objective evaluated across model ambiguity"
    false refl

pipelineBoundaryStatement : String
pipelineBoundaryStatement =
  "A residual stat-arb backtest is a braid of fibre-local projections and forward transports; factor residuality, learned prediction, high Sharpe, and deployment authority remain distinct proof obligations."
