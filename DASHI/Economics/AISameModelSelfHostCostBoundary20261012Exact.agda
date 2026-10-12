module DASHI.Economics.AISameModelSelfHostCostBoundary20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- SAME-MODEL HOSTED-vs-SELF-HOST ENGINEERING COST BOUNDARY
--
-- This is deliberately not a provider-margin theorem.  The public source is a
-- third-party engineering cost dataset with a disclosed commercial conflict.
-- It gives a useful same-model substitution receipt under one explicit serving
-- configuration, which is stronger than comparing different model families but
-- weaker than observing a provider's own marginal-cost ledger.
------------------------------------------------------------------------

engineeringDatasetKind : Source.SourceKind
engineeringDatasetKind = Source.namedSourceKind "public engineering cost dataset with disclosed vendor conflict"

inferenceCostTruthSource : Source.AttributedSource
inferenceCostTruthSource = Source.mkNoDOISource
  "RightNow AI"
  "inference-cost-truth"
  "GitHub engineering dataset / 2026-07-31 snapshot"
  "2026-07-31"
  "https://github.com/RightNow-AI/inference-cost-truth/tree/a61c501241da17f3403597d75a7a8847c53cb29e"
  engineeringDatasetKind
  "source states that MiniMax-M3 on AMD MI355X at concurrency 512 and 30 percent sustained utilisation is estimated at USD 0.93 per million output tokens self-hosted versus USD 1.20 hosted; source explicitly discloses that the maintainer sells GPU-kernel optimisation"
  Source.publicAttribution

record SameModelCostComparison : Set where
  constructor same-model-cost-comparison
  field
    model : String
    hostedProviderClass : String
    accelerator : String
    concurrency : Nat
    inputTokens : Nat
    utilizationPercent : Nat
    selfHostCostCentsPerMillionOutput : Nat
    hostedCostCentsPerMillionOutput : Nat
    sameModelIdentity : Bool
    configurationSensitive : Bool
    sourceConflictDisclosed : Bool
    directProviderMarginalCostObserved : Bool
    frontierClosedModelComparator : Bool
    globalSelfHostAdvantageEstablished : Bool
    source : Source.AttributedSource

open SameModelCostComparison public

miniMaxM3EngineeringComparison : SameModelCostComparison
miniMaxM3EngineeringComparison = same-model-cost-comparison
  "MiniMax-M3"
  "hosted open-model API"
  "AMD MI355X"
  512
  1000
  30
  93
  120
  true
  true
  true
  false
  false
  false
  inferenceCostTruthSource

sameModelIdentityPaid : sameModelIdentity miniMaxM3EngineeringComparison ≡ true
sameModelIdentityPaid = refl

selfHostCostCentsPerMillionIs93 :
  selfHostCostCentsPerMillionOutput miniMaxM3EngineeringComparison ≡ 93
selfHostCostCentsPerMillionIs93 = refl

hostedCostCentsPerMillionIs120 :
  hostedCostCentsPerMillionOutput miniMaxM3EngineeringComparison ≡ 120
hostedCostCentsPerMillionIs120 = refl

configurationSensitivityRetained :
  configurationSensitive miniMaxM3EngineeringComparison ≡ true
configurationSensitivityRetained = refl

providerMarginalCostStillUnobserved :
  directProviderMarginalCostObserved miniMaxM3EngineeringComparison ≡ false
providerMarginalCostStillUnobserved = refl

data EngineeringCostImpliesProviderMarginPermission : Set where
data OneFavourableConfigurationImpliesGlobalSelfHostAdvantagePermission : Set where
data HostedOpenComparatorImpliesClosedModelScarcityRentPermission : Set where

engineeringCostDoesNotCreateProviderMargin :
  EngineeringCostImpliesProviderMarginPermission → ⊥
engineeringCostDoesNotCreateProviderMargin ()

oneConfigurationDoesNotCreateGlobalSelfHostAdvantage :
  OneFavourableConfigurationImpliesGlobalSelfHostAdvantagePermission → ⊥
oneConfigurationDoesNotCreateGlobalSelfHostAdvantage ()

hostedOpenDoesNotCreateClosedModelScarcityRent :
  HostedOpenComparatorImpliesClosedModelScarcityRentPermission → ⊥
hostedOpenDoesNotCreateClosedModelScarcityRent ()

record ServingCostResidual : Set where
  constructor serving-cost-residual
  field
    sameModelEngineeringComparatorPaid : Bool
    providerOwnMarginalCostLedgerPaid : Bool
    matchedLatencySLAPaid : Bool
    matchedCachingPolicyPaid : Bool
    matchedUtilizationPaid : Bool
    qualityAdjustedClosedOpenMarginPaid : Bool

open ServingCostResidual public

currentServingCostResidual : ServingCostResidual
currentServingCostResidual = serving-cost-residual
  true false false false false false

boundary : String
boundary =
  "The 2026-07-31 inference-cost-truth snapshot supplies a same-model MiniMax-M3 engineering comparison: under MI355X, concurrency 512, 1k input and 30 percent sustained utilisation, estimated self-host cost is USD 0.93/M output tokens versus USD 1.20/M hosted. This is a configuration-sensitive substitution receipt with a disclosed source conflict. It does not reveal the hosted provider's own marginal cost, establish global self-host advantage, or create a closed-vs-open scarcity-rent theorem."
