{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityExperimentPortfolioExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Physics.ExoticGravity.AntigravitySameStateFourChannelDiscriminatorExact as FourChannel

------------------------------------------------------------------------
-- ANTIGRAVITY EXPERIMENT PORTFOLIO
--
-- This owner instantiates the existing master experiment-design interface.
-- It is a repository-authored discrimination language, not an external source
-- claim and not a truth/authority ranking.  The live sibling PRs #1163/#1165
-- motivated the conservation/same-stress discipline, but no sibling theorem is
-- imported as authority here.
------------------------------------------------------------------------

data AntigravityExperimentCandidate : Set where
  weightOnlyExperiment : AntigravityExperimentCandidate
  freeFallClockExperiment : AntigravityExperimentCandidate
  matchedFourChannelExperiment : AntigravityExperimentCandidate
  matchedFourChannelTTExperiment : AntigravityExperimentCandidate

record DiscriminationCoverage : Set where
  constructor discrimination-coverage
  field
    supportForceAnomaly : Bool
    metricVsNonmetric : Bool
    crossChannelMetricConsistency : Bool
    scalarVsPropagatingTT : Bool
    ordinaryNuisanceClosure : Bool
    sameCandidateBinding : Bool
    replicationSurface : Bool

open DiscriminationCoverage public

coverage : AntigravityExperimentCandidate → DiscriminationCoverage
coverage weightOnlyExperiment =
  discrimination-coverage true false false false false true true
coverage freeFallClockExperiment =
  discrimination-coverage true true false false true true true
coverage matchedFourChannelExperiment =
  discrimination-coverage true true true false true true true
coverage matchedFourChannelTTExperiment =
  discrimination-coverage true true true true true true true

record CoverageRefines
    (strong weak : DiscriminationCoverage) : Set where
  constructor coverage-refines
  field
    preservesSupport :
      supportForceAnomaly weak ≡ true → supportForceAnomaly strong ≡ true
    preservesMetricDiscrimination :
      metricVsNonmetric weak ≡ true → metricVsNonmetric strong ≡ true
    preservesCrossChannelConsistency :
      crossChannelMetricConsistency weak ≡ true →
      crossChannelMetricConsistency strong ≡ true
    preservesTTDiscrimination :
      scalarVsPropagatingTT weak ≡ true →
      scalarVsPropagatingTT strong ≡ true
    preservesNuisanceClosure :
      ordinaryNuisanceClosure weak ≡ true →
      ordinaryNuisanceClosure strong ≡ true
    preservesSameCandidateBinding :
      sameCandidateBinding weak ≡ true → sameCandidateBinding strong ≡ true
    preservesReplicationSurface :
      replicationSurface weak ≡ true → replicationSurface strong ≡ true

open CoverageRefines public

matchedFourChannelRefinesWeightOnly :
  CoverageRefines
    (coverage matchedFourChannelExperiment)
    (coverage weightOnlyExperiment)
matchedFourChannelRefinesWeightOnly =
  coverage-refines
    (λ _ → refl)
    (λ ())
    (λ ())
    (λ ())
    (λ ())
    (λ _ → refl)
    (λ _ → refl)

matchedFourChannelTTRefinesMatchedFourChannel :
  CoverageRefines
    (coverage matchedFourChannelTTExperiment)
    (coverage matchedFourChannelExperiment)
matchedFourChannelTTRefinesMatchedFourChannel =
  coverage-refines
    (λ _ → refl)
    (λ _ → refl)
    (λ _ → refl)
    (λ ())
    (λ _ → refl)
    (λ _ → refl)
    (λ _ → refl)

antigravityExperimentDesign :
  Robust.ExperimentDesign AntigravityExperimentCandidate DiscriminationCoverage
antigravityExperimentDesign =
  Robust.experimentDesign
    coverage
    (λ stronger weaker → CoverageRefines (coverage stronger) (coverage weaker))
    Bool

matchedFourChannelCoversMetricDiscrimination :
  metricVsNonmetric (coverage matchedFourChannelExperiment) ≡ true
matchedFourChannelCoversMetricDiscrimination = refl

matchedFourChannelCoversCrossChannelConsistency :
  crossChannelMetricConsistency (coverage matchedFourChannelExperiment) ≡ true
matchedFourChannelCoversCrossChannelConsistency = refl

weightOnlyDoesNotCoverMetricDiscrimination :
  metricVsNonmetric (coverage weightOnlyExperiment) ≡ false
weightOnlyDoesNotCoverMetricDiscrimination = refl

weightOnlyDoesNotCoverCrossChannelConsistency :
  crossChannelMetricConsistency (coverage weightOnlyExperiment) ≡ false
weightOnlyDoesNotCoverCrossChannelConsistency = refl

matchedFourChannelTTSeparatesScalarFromTT :
  scalarVsPropagatingTT (coverage matchedFourChannelTTExperiment) ≡ true
matchedFourChannelTTSeparatesScalarFromTT = refl

ttOptionRequiresP4 : Bool
ttOptionRequiresP4 = true

fourChannelScalarRouteRequiresP4 : Bool
fourChannelScalarRouteRequiresP4 = false

scalarMetricDoesNotSupplyTTReceipt : Bool
scalarMetricDoesNotSupplyTTReceipt =
  FourChannel.scalarMetricPerturbationIsNotTTMode

experimentCoverageCreatesTruth : Bool
experimentCoverageCreatesTruth = false

experimentCoverageCreatesMechanismIdentity : Bool
experimentCoverageCreatesMechanismIdentity = false

siblingPR1163ImportedAsTheoremAuthority : Bool
siblingPR1163ImportedAsTheoremAuthority = false

siblingPR1165ImportedAsTheoremAuthority : Bool
siblingPR1165ImportedAsTheoremAuthority = false

record ExperimentPortfolioBoundary : Set where
  constructor experiment-portfolio-boundary
  field
    weightOnlyIsMetricDiscriminator : Bool
    fourChannelAddsMetricDiscrimination : Bool
    fourChannelAddsCrossChannelConsistency : Bool
    ttDiscriminationRequiresOptionalExtension : Bool
    experimentDesignCreatesScientificTruth : Bool
    experimentDesignCreatesMechanismIdentity : Bool

canonicalExperimentPortfolioBoundary : ExperimentPortfolioBoundary
canonicalExperimentPortfolioBoundary =
  experiment-portfolio-boundary false true true true false false
