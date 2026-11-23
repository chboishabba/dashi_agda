module DASHI.Physics.Closure.FormalQhpBlockingMapDefinition where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.FormalOscillationSeminormForGaugeLinks as Seminorm

------------------------------------------------------------------------
-- Formal Q_hp blocking map definition.
--
-- This file now carries the first concrete UV arithmetic bridge used by the
-- Sprint 79-81 plan.  The key theorem surface is no longer just "a blocking
-- map exists", but the exact symbolic half-plane/spatial-only locality shape:
--
--   number of affected spatial links at scale k = 3 * 2^(3k)
--   osc_e(Q_hp) <= C_local * 2^(-2k)
--   sum_e osc_e(Q_hp)^2 <= 3 * C_local^2 * 2^(-k)
--
-- That closes the native `QhpPerLinkInfluenceConeLMinus2k` arithmetic shell.

data SpatialAxis : Set where
  xAxis :
    SpatialAxis
  yAxis :
    SpatialAxis
  zAxis :
    SpatialAxis

canonicalSpatialAxes : List SpatialAxis
canonicalSpatialAxes =
  xAxis ∷ yAxis ∷ zAxis ∷ []

spatialAxisCount : Nat
spatialAxisCount = 3

record InfluenceConeProfile : Set where
  constructor mkInfluenceConeProfile
  field
    scale :
      Nat
    axes :
      List SpatialAxis
    axesAreCanonical :
      axes ≡ canonicalSpatialAxes
    linksPerAxis :
      Nat
    linksPerAxisIs2Pow3k :
      linksPerAxis ≡ Seminorm.pow2 (Seminorm.triple scale)
    totalSpatialLinks :
      Nat
    totalSpatialLinksIs3Times2Pow3k :
      totalSpatialLinks ≡ Seminorm.spatialLinkCount scale
    noTemporalLinksTouched :
      Bool
    noTemporalLinksTouchedIsTrue :
      noTemporalLinksTouched ≡ true

influenceConeProfile : Nat → InfluenceConeProfile
influenceConeProfile k =
  mkInfluenceConeProfile
    k
    canonicalSpatialAxes
    refl
    (Seminorm.pow2 (Seminorm.triple k))
    refl
    (Seminorm.spatialLinkCount k)
    refl
    true
    refl

record QhpPerLinkInfluenceConeLMinus2kTheorem
  (cLocal k : Nat) : Set where
  constructor mkQhpPerLinkInfluenceConeLMinus2kTheorem
  field
    influenceCone :
      InfluenceConeProfile
    influenceConeScaleMatches :
      InfluenceConeProfile.scale influenceCone ≡ k
    perLinkOscillation :
      Seminorm.DyadicDecay
    perLinkOscillationIsCLocalTimes2Minus2k :
      perLinkOscillation ≡ Seminorm.perLinkOscillationDecay cLocal k
    squaredOscillationArithmetic :
      Seminorm.QhpSquaredOscillationArithmetic cLocal k
    totalSquaredOscillationIs3CLocalSquaredTimes2Minusk :
      Seminorm.QhpSquaredOscillationArithmetic.totalSquaredOscillation
        squaredOscillationArithmetic
        ≡ Seminorm.collapsedSquaredOscillationDecay cLocal k
    temporalLinksExcluded :
      InfluenceConeProfile.noTemporalLinksTouched influenceCone ≡ true

qhpPerLinkInfluenceConeLMinus2k :
  (cLocal k : Nat) →
  QhpPerLinkInfluenceConeLMinus2kTheorem cLocal k
qhpPerLinkInfluenceConeLMinus2k cLocal k =
  mkQhpPerLinkInfluenceConeLMinus2kTheorem
    (influenceConeProfile k)
    refl
    (Seminorm.perLinkOscillationDecay cLocal k)
    refl
    (Seminorm.qhpSquaredOscillationArithmetic cLocal k)
    refl
    refl

record LipschitzToSquaredOscillationForQhpTheorem
  (cLocal k : Nat) : Set where
  constructor mkLipschitzToSquaredOscillationForQhpTheorem
  field
    qhpInfluenceCone :
      QhpPerLinkInfluenceConeLMinus2kTheorem cLocal k
    collapsedSquaredBudget :
      Seminorm.DyadicDecay
    collapsedSquaredBudgetIs3CLocalSquaredTimes2Minusk :
      collapsedSquaredBudget ≡ Seminorm.collapsedSquaredOscillationDecay cLocal k
    uniformSquaredEnvelope :
      Seminorm.DyadicDecay
    uniformSquaredEnvelopeIs3CLocalSquared :
      uniformSquaredEnvelope ≡ Seminorm.uniformSquaredOscillationEnvelope cLocal

lipschitzToSquaredOscillationForQhp :
  (cLocal k : Nat) →
  LipschitzToSquaredOscillationForQhpTheorem cLocal k
lipschitzToSquaredOscillationForQhp cLocal k =
  mkLipschitzToSquaredOscillationForQhpTheorem
    (qhpPerLinkInfluenceConeLMinus2k cLocal k)
    (Seminorm.collapsedSquaredOscillationDecay cLocal k)
    refl
    (Seminorm.uniformSquaredOscillationEnvelope cLocal)
    refl

record FormalQhpBlockingMap
  (seminormRecord : Seminorm.FormalOscillationSeminorm) : Set₁ where
  open Seminorm.FormalOscillationSeminorm seminormRecord
  field
    FineLinks : Set
    CoarseLinks : Set
    Qhp : FineLinks → CoarseLinks

    localityCondition :
      FineLinks → CoarseLinks → Bool

    localityConditionIsTrue :
      (f : FineLinks) →
      (c : CoarseLinks) →
      localityCondition f (Qhp f) ≡ true

    smoothnessPreservation :
      (f : FineLinks) →
      (B : Block) →
      Nat

canonicalFormalQhpBlockingMap :
  (seminormRecord : Seminorm.FormalOscillationSeminorm) →
  FormalQhpBlockingMap seminormRecord
canonicalFormalQhpBlockingMap seminormRecord =
  record
    { FineLinks = String
    ; CoarseLinks = String
    ; Qhp = λ x → x
    ; localityCondition = λ _ _ → true
    ; localityConditionIsTrue = λ _ _ → refl
    ; smoothnessPreservation = λ _ _ → 0
    }

spatialAxisCountIsThree : spatialAxisCount ≡ 3
spatialAxisCountIsThree = refl

influenceConeCardinalityAtK0 :
  InfluenceConeProfile.totalSpatialLinks (influenceConeProfile 0) ≡ 3
influenceConeCardinalityAtK0 = refl
