module DASHI.Governance.BOMVersionedSameObjectCorrectionExact where

-- Abstract, source-typed correction contract for the 2026 BOM investigation.
-- Source-authentication and empirical claims are NOT supplied by these types.
-- Original archive staff, BOM and named auditors retain their source authorship.
-- DASHI reuses the canonical nonfactorability calculus.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
import DASHI.Core.IntersectionalNonFactorability as INF

data ObservedVariable : Set where
  maximumTemperature minimumTemperature rainfall : ObservedVariable

record ObservationKey : Set where
  constructor observation-key
  field
    stationID : String
    observationDate : String
    observedVariable : ObservedVariable

data SnapshotVersion : Set where
  may2026 october2026 : SnapshotVersion

-- A token is an encoded reading, not a temperature/rainfall quantity.
-- The external input decoder must supply its units and precision.
data RawToken : Set where
  absent : RawToken
  presentToken : Nat → RawToken

record SnapshotRow (key : ObservationKey) (v : SnapshotVersion) : Set where
  constructor snapshot-row
  field
    sourceSHA256 : String
    captureUTC : String
    sourceURL : String
    valueToken : RawToken

-- Both records have exactly the SAME key by construction. Hash strings
-- alone are untrusted metadata until checked against archived bytes.
record SameObjectChange (key : ObservationKey) : Set where
  constructor same-object-change
  field
    before : SnapshotRow key may2026
    after : SnapshotRow key october2026
    valuesDiffer :
      SnapshotRow.valueToken before ≡ SnapshotRow.valueToken after → ⊥

-- An original-record comparison is a SEPARATE, stronger obligation.
-- It does not follow from two published snapshot rows being different.
record PaperComparison (key : ObservationKey)
                       (change : SameObjectChange key) : Set where
  constructor paper-comparison
  field
    originalArchiveLocator : String
    originalArchiveSHA256 : String
    originalValueToken : RawToken
    correctedMatchesOriginal :
      SnapshotRow.valueToken (SameObjectChange.after change) ≡
      originalValueToken

-- Structural witness only. No real BOM data is encoded here.
exampleKey : ObservationKey
exampleKey = observation-key "SYNTHETIC" "1900-01-01" maximumTemperature

exampleBefore : SnapshotRow exampleKey may2026
exampleBefore = snapshot-row "synthetic" "synthetic" "synthetic" (presentToken 1)

exampleAfter : SnapshotRow exampleKey october2026
exampleAfter = snapshot-row "synthetic" "synthetic" "synthetic" absent

exampleValuesDiffer : presentToken 1 ≡ absent → ⊥
exampleValuesDiffer ()

exampleSameObjectRemoval : SameObjectChange exampleKey
exampleSameObjectRemoval =
  same-object-change exampleBefore exampleAfter exampleValuesDiffer

-- Stronger theorem: a raw anomaly flag cannot determine the downstream
-- trend effect. Two possible worlds agree on the flag but differ on outcome.
-- This is a finite logical counterexample, not a climate trend estimate.
data TrendWorld : Set where
  errorTrendStable errorTrendChanged : TrendWorld

data RawErrorFlag : Set where
  anomalyPresent : RawErrorFlag

data TrendEffect : Set where
  stableTrend changedTrend : TrendEffect

seenRawError : TrendWorld → RawErrorFlag
seenRawError _ = anomalyPresent

downstreamTrendEffect : TrendWorld → TrendEffect
downstreamTrendEffect errorTrendStable = stableTrend
downstreamTrendEffect errorTrendChanged = changedTrend

trendEffectsDiffer :
  downstreamTrendEffect errorTrendStable ≡
  downstreamTrendEffect errorTrendChanged → ⊥
trendEffectsDiffer ()

trendImpactNonidentifiableFromRawError :
  INF.NonFactorabilityWitness seenRawError downstreamTrendEffect
trendImpactNonidentifiableFromRawError =
  INF.nonFactorabilityWitness
    errorTrendStable errorTrendChanged refl trendEffectsDiffer

rawErrorCannotByItselfEstablishTrendImpact :
  INF.FactorsThrough seenRawError downstreamTrendEffect → ⊥
rawErrorCannotByItselfEstablishTrendImpact =
  INF.witnessRulesOutEveryFlatFactorisation
    trendImpactNonidentifiableFromRawError
