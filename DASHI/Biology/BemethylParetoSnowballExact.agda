module DASHI.Biology.BemethylParetoSnowballExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record ParetoSnowball : Set where
  field
    targetEngagementPriority : Nat
    modernPerformancePriority : Nat
    heatOxygenPriority : Nat
    humanPKPriority : Nat
    historicalUsePriority : Nat

    targetEngagementWouldCollapseMechanismLeaf : Bool
    modernPerformanceWouldCollapseReplicationLeaf : Bool
    historicalControlledPerformanceEvidenceNowAcquired : Bool
    heatOxygenHistoricalHumanEvidenceNowAcquired : Bool
    humanPKHistoricalExposureEvidenceNowAcquired : Bool
    historicalUseFurtherAcquisitionChangesMechanismFrontier : Bool

    primaryOrIndexedHumanSourcesPreferred : Bool
    reviewSnowballIsNavigationOnly : Bool
    reviewRepetitionCreatesIndependentReplication : Bool
    secondaryHistoricalRepetitionCreatesPrimaryReceipt : Bool

    nextSourceQuery : String

open ParetoSnowball public

canonicalParetoSnowball : ParetoSnowball
canonicalParetoSnowball = record
  { targetEngagementPriority = 5
  ; modernPerformancePriority = 4
  ; heatOxygenPriority = 3
  ; humanPKPriority = 2
  ; historicalUsePriority = 1
  ; targetEngagementWouldCollapseMechanismLeaf = true
  ; modernPerformanceWouldCollapseReplicationLeaf = true
  ; historicalControlledPerformanceEvidenceNowAcquired = true
  ; heatOxygenHistoricalHumanEvidenceNowAcquired = true
  ; humanPKHistoricalExposureEvidenceNowAcquired = true
  ; historicalUseFurtherAcquisitionChangesMechanismFrontier = false
  ; primaryOrIndexedHumanSourcesPreferred = true
  ; reviewSnowballIsNavigationOnly = true
  ; reviewRepetitionCreatesIndependentReplication = false
  ; secondaryHistoricalRepetitionCreatesPrimaryReceipt = false
  ; nextSourceQuery = "Acquire direct bemethyl target engagement or a causal molecular intervention. Historical controlled operator, heat/exertion, and human PK/excretion leaves are now source-paid at indexed-abstract level; next recover complete original methods and then seek modern independent same-compound replication."
  }

reviewRepetitionDoesNotIncreaseAuthority :
  reviewRepetitionCreatesIndependentReplication canonicalParetoSnowball ≡ false
reviewRepetitionDoesNotIncreaseAuthority = refl

historicalRepetitionDoesNotCreatePrimaryReceipt :
  secondaryHistoricalRepetitionCreatesPrimaryReceipt canonicalParetoSnowball ≡ false
historicalRepetitionDoesNotCreatePrimaryReceipt = refl
