module DASHI.Empirical.SeamABExperiment where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_*_; _≤_)

-- Both solve directions are mandatory experiment lanes. The formal surface
-- does not prematurely promote either lane as globally canonical.

data Domain : Set where
  base : Domain
  rom : Domain

data Direction : Set where
  A-base-to-rom : Direction
  B-rom-to-base : Direction

record DirectedResult (Metric : Set) : Set where
  constructor result
  field
    nativeMetric : Metric
    transferredMetric : Metric

record ABExperiment (Metric : Set) : Set where
  constructor experiment
  field
    strategyA : DirectedResult Metric
    strategyB : DirectedResult Metric

source : Direction → Domain
source A-base-to-rom = base
source B-rom-to-base = rom

target : Direction → Domain
target A-base-to-rom = rom
target B-rom-to-base = base

A-source-is-base : source A-base-to-rom ≡ base
A-source-is-base = refl

A-target-is-rom : target A-base-to-rom ≡ rom
A-target-is-rom = refl

B-source-is-rom : source B-rom-to-base ≡ rom
B-source-is-rom = refl

B-target-is-base : target B-rom-to-base ≡ base
B-target-is-base = refl

-- Any selector must be supplied with an explicit policy. DASHI does not derive
-- a winner merely from the existence of the two lanes.

data Selection : Set where
  select-A : Selection
  select-B : Selection
  retain-both : Selection
  needs-human : Selection

record SelectionPolicy (Metric : Set) : Set₁ where
  field
    select : ABExperiment Metric → Selection

bothDirectionsPresent :
  {Metric : Set} →
  (e : ABExperiment Metric) →
  ABExperiment.strategyA e ≡ ABExperiment.strategyA e
bothDirectionsPresent e = refl

------------------------------------------------------------------------
-- Strategy 2 quantitative A/B comparison.
--
-- These values are counts or fixed-unit lengths. Ratios use an explicit
-- integer scale so acceptance remains exact and deterministic.
------------------------------------------------------------------------

record Strategy2ComparisonMetrics : Set where
  constructor strategy2-comparison-metrics
  field
    nativeEdgeCount : Nat
    transferredEdgeCount : Nat
    retainedEdgeCount : Nat
    collisionCount : Nat
    invalidTransferredEdgeCount : Nat
    nativeTotalLength : Nat
    transferredTotalLength : Nat

open Strategy2ComparisonMetrics public

record Strategy2Thresholds : Set where
  constructor strategy2-thresholds
  field
    scaleFactor : Nat
    scaleFactorPositive : 1 ≤ scaleFactor
    minimumEdgeRetentionScaled : Nat
    maximumCollisionScaled : Nat
    maximumInvalidMeshEdgeScaled : Nat
    minimumLengthRetentionScaled : Nat

open Strategy2Thresholds public

-- Basic metric coherence is separate from acceptance thresholds.
-- It prevents a bundle from paying a gate with impossible counts.

record Strategy2MetricWellFormed
    (metrics : Strategy2ComparisonMetrics) : Set where
  constructor strategy2-metric-well-formed
  field
    retainedEdgesComeFromNative :
      retainedEdgeCount metrics ≤ nativeEdgeCount metrics
    collisionsComeFromTransferred :
      collisionCount metrics ≤ transferredEdgeCount metrics
    invalidEdgesComeFromTransferred :
      invalidTransferredEdgeCount metrics ≤ transferredEdgeCount metrics

open Strategy2MetricWellFormed public

-- Keep the original result payload and attach one quantitative comparison.
-- Strategy A and Strategy B remain disjoint typed directions.

record Strategy2DirectedBundle (Metric : Set) : Set where
  constructor strategy2-directed-bundle
  field
    directedResult : DirectedResult Metric
    comparisonMetrics : Strategy2ComparisonMetrics

open Strategy2DirectedBundle public

record Strategy2Bundle (Metric : Set) : Set where
  constructor strategy2-bundle
  field
    strategyAQuantitative : Strategy2DirectedBundle Metric
    strategyBQuantitative : Strategy2DirectedBundle Metric

open Strategy2Bundle public

-- Four quantitative gates.
--
-- Edge retention:
--   retained/native >= minimum retention.
--
-- Collision:
--   collisions/transferred <= maximum collision rate.
--
-- Mesh-edge validity:
--   invalid/transferred <= maximum invalid-edge rate.
--
-- Length collapse:
--   transferred length/native length >= minimum retained length.
--
-- Cross multiplication avoids division and rounding.

record Strategy2DirectedAcceptance
    (thresholds : Strategy2Thresholds)
    {Metric : Set}
    (bundle : Strategy2DirectedBundle Metric) : Set where
  constructor strategy2-directed-accepted
  field
    metricsWellFormed :
      Strategy2MetricWellFormed (comparisonMetrics bundle)

    edgeRetentionAccepted :
      minimumEdgeRetentionScaled thresholds
        * nativeEdgeCount (comparisonMetrics bundle)
      ≤
      retainedEdgeCount (comparisonMetrics bundle)
        * scaleFactor thresholds

    collisionAccepted :
      collisionCount (comparisonMetrics bundle)
        * scaleFactor thresholds
      ≤
      maximumCollisionScaled thresholds
        * transferredEdgeCount (comparisonMetrics bundle)

    meshEdgeValidityAccepted :
      invalidTransferredEdgeCount (comparisonMetrics bundle)
        * scaleFactor thresholds
      ≤
      maximumInvalidMeshEdgeScaled thresholds
        * transferredEdgeCount (comparisonMetrics bundle)

    lengthCollapseAccepted :
      minimumLengthRetentionScaled thresholds
        * nativeTotalLength (comparisonMetrics bundle)
      ≤
      transferredTotalLength (comparisonMetrics bundle)
        * scaleFactor thresholds

open Strategy2DirectedAcceptance public

-- A Strategy 2 bundle is accepted only when both transfer directions pass.
-- This is the acceptance gate consumed by quantitative selectors.

record Strategy2Accepted
    (thresholds : Strategy2Thresholds)
    {Metric : Set}
    (bundle : Strategy2Bundle Metric) : Set where
  constructor strategy2-accepted
  field
    strategyAAccepted :
      Strategy2DirectedAcceptance
        thresholds
        (strategyAQuantitative bundle)

    strategyBAccepted :
      Strategy2DirectedAcceptance
        thresholds
        (strategyBQuantitative bundle)

open Strategy2Accepted public

strategy2AcceptanceGate :
  (thresholds : Strategy2Thresholds) →
  {Metric : Set} →
  Strategy2Bundle Metric →
  Set
strategy2AcceptanceGate thresholds bundle =
  Strategy2Accepted thresholds bundle

-- Selection cannot consume a Strategy 2 bundle without an acceptance proof.
-- This makes the comparison metrics active gates rather than passive telemetry.

record Strategy2SelectionPolicy
    (Metric : Set)
    (thresholds : Strategy2Thresholds) : Set₁ where
  field
    selectAccepted :
      (bundle : Strategy2Bundle Metric) →
      Strategy2Accepted thresholds bundle →
      Selection

open Strategy2SelectionPolicy public

bothQuantitativeDirectionsPresent :
  {Metric : Set} →
  (bundle : Strategy2Bundle Metric) →
  strategyAQuantitative bundle ≡ strategyAQuantitative bundle
bothQuantitativeDirectionsPresent bundle = refl
