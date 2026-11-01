module DASHI.Geometry.ValuationConformalMetricCandidate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Agda.Builtin.String using (String)
open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Closure.ValuationVacuumEinsteinBoundary as Vacuum

------------------------------------------------------------------------
-- Conformal valuation interface and a constructive underdetermination result.
--
-- A scalar valuation profile can supply a local positive scale tag once a
-- reference metric is given.  It does not choose the reference metric or the
-- causal direction.  Two distinct 1+3 reference tables below consume the same
-- valuation profile.


data VacuumSite : Set where
  vacuumSite : VacuumSite

record ValuationProfile : Set where
  constructor mkValuationProfile
  field
    profileLabel : String
    valuationDepth : VacuumSite → Nat
    valuationCarrier : Vacuum.ValuationFieldCarrier

open ValuationProfile public

uniformSaturatedProfile : ValuationProfile
uniformSaturatedProfile =
  mkValuationProfile
    "uniform-saturated-valuation-profile"
    (λ _ → zero)
    Vacuum.saturatedVacuumValuation

MetricTable : Set
MetricTable = Flat.Axis4 → Flat.Axis4 → TriTruth

referenceMetricTimeLike : MetricTable
referenceMetricTimeLike = Flat.flatMetricEntry

referenceMetricXLike : MetricTable
referenceMetricXLike Flat.timeAxis Flat.timeAxis = tri-high
referenceMetricXLike Flat.timeAxis Flat.xAxis = tri-mid
referenceMetricXLike Flat.timeAxis Flat.yAxis = tri-mid
referenceMetricXLike Flat.timeAxis Flat.zAxis = tri-mid
referenceMetricXLike Flat.xAxis Flat.timeAxis = tri-mid
referenceMetricXLike Flat.xAxis Flat.xAxis = tri-low
referenceMetricXLike Flat.xAxis Flat.yAxis = tri-mid
referenceMetricXLike Flat.xAxis Flat.zAxis = tri-mid
referenceMetricXLike Flat.yAxis Flat.timeAxis = tri-mid
referenceMetricXLike Flat.yAxis Flat.xAxis = tri-mid
referenceMetricXLike Flat.yAxis Flat.yAxis = tri-high
referenceMetricXLike Flat.yAxis Flat.zAxis = tri-mid
referenceMetricXLike Flat.zAxis Flat.timeAxis = tri-mid
referenceMetricXLike Flat.zAxis Flat.xAxis = tri-mid
referenceMetricXLike Flat.zAxis Flat.yAxis = tri-mid
referenceMetricXLike Flat.zAxis Flat.zAxis = tri-high

record ScaledMetricEntry : Set where
  constructor mkScaledMetricEntry
  field
    referenceEntry : TriTruth
    positiveScaleDepth : Nat

open ScaledMetricEntry public

record ConformalMetricCandidate : Set where
  constructor mkConformalMetricCandidate
  field
    candidateLabel : String
    profile : ValuationProfile
    referenceMetric : MetricTable
    scaledEntry : VacuumSite → Flat.Axis4 → Flat.Axis4 → ScaledMetricEntry
    scaledEntryUsesReference :
      (site : VacuumSite) →
      (a b : Flat.Axis4) →
      referenceEntry (scaledEntry site a b) ≡ referenceMetric a b
    scaledEntryUsesPositiveDepth :
      (site : VacuumSite) →
      (a b : Flat.Axis4) →
      positiveScaleDepth (scaledEntry site a b)
      ≡ suc (valuationDepth profile site)
    candidateScope : String

open ConformalMetricCandidate public

makeConformalCandidate :
  String → ValuationProfile → MetricTable → ConformalMetricCandidate
makeConformalCandidate label valuation reference =
  mkConformalMetricCandidate
    label
    valuation
    reference
    (λ site a b →
      mkScaledMetricEntry
        (reference a b)
        (suc (valuationDepth valuation site)))
    (λ _ _ _ → refl)
    (λ _ _ _ → refl)
    "valuation supplies a positive scale tag only after a reference metric is supplied"

timeLikeConformalCandidate : ConformalMetricCandidate
timeLikeConformalCandidate =
  makeConformalCandidate
    "time-axis-reference-conformal-candidate"
    uniformSaturatedProfile
    referenceMetricTimeLike

xLikeConformalCandidate : ConformalMetricCandidate
xLikeConformalCandidate =
  makeConformalCandidate
    "x-axis-reference-conformal-candidate"
    uniformSaturatedProfile
    referenceMetricXLike

sameValuationProfile :
  profile timeLikeConformalCandidate ≡ profile xLikeConformalCandidate
sameValuationProfile = refl


data MetricEntryDifference : TriTruth → TriTruth → Set where
  lowHighDifference : MetricEntryDifference tri-low tri-high

sameValuationDifferentTimeEntry :
  MetricEntryDifference
    (referenceEntry
      (scaledEntry
        timeLikeConformalCandidate
        vacuumSite
        Flat.timeAxis
        Flat.timeAxis))
    (referenceEntry
      (scaledEntry
        xLikeConformalCandidate
        vacuumSite
        Flat.timeAxis
        Flat.timeAxis))
sameValuationDifferentTimeEntry = lowHighDifference

record ValuationMetricUnderdeterminationReceipt : Set where
  constructor mkValuationMetricUnderdeterminationReceipt
  field
    firstCandidate : ConformalMetricCandidate
    secondCandidate : ConformalMetricCandidate
    sharedProfileReceipt : profile firstCandidate ≡ profile secondCandidate
    distinctReferenceEntryReceipt :
      MetricEntryDifference
        (referenceEntry
          (scaledEntry
            firstCandidate
            vacuumSite
            Flat.timeAxis
            Flat.timeAxis))
        (referenceEntry
          (scaledEntry
            secondCandidate
            vacuumSite
            Flat.timeAxis
            Flat.timeAxis))
    receiptScope : String

open ValuationMetricUnderdeterminationReceipt public

valuationMetricUnderdeterminationReceipt :
  ValuationMetricUnderdeterminationReceipt
valuationMetricUnderdeterminationReceipt =
  mkValuationMetricUnderdeterminationReceipt
    timeLikeConformalCandidate
    xLikeConformalCandidate
    sameValuationProfile
    sameValuationDifferentTimeEntry
    "one scalar valuation profile admits distinct 1+3 reference metrics; causal structure requires extra admissibility data"
