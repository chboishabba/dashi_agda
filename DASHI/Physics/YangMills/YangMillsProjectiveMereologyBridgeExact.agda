{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsProjectiveMereologyBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)\nopen import Agda.Primitive using (Set₁)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Core.MereologyCoreExact as Mereology
import DASHI.Core.ConsumerRelativeMereologyExact as Consumer
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476
import DASHI.Physics.YangMills.YangMillsPhysicalProjectiveCylinderRepresentationRound535Exact as R535
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.BalabanLiteralWilsonMarkedLocalizationSourceExact as Marked
import DASHI.Physics.YangMills.BalabanWilsonMarkedClusterDifferentiationExact as Diff
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.YangMillsRationalAbsoluteCovarianceExtensionRound575Exact as R575

------------------------------------------------------------------------
-- YM PROJECTIVE MEREOLOGY BRIDGE
--
-- This bridge does not add a new measure theorem.  It states the exact
-- part/whole reading already enforced by R534/R535:
--
--   finite cylinder levels = local parts;
--   the complete projective family = declared part family;
--   projective/event/continuity laws = compatibility/descent data;
--   the represented continuum measure = reconstructed whole.
--
-- In particular, a selected finite cutoff is not promoted to the whole.
------------------------------------------------------------------------

record YMProjectiveMereologyReceipt
    (Configuration Event : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    (inputs :
      R535.PhysicalProjectiveCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    : Set₁ where
  field
    reconstructedWhole :
      R476.SourceLimitRepresentation
        (Configuration → ℝ)
        (Limit.limitExpectation family)

    reconstructedWholeIsCanonical :
      reconstructedWhole ≡ R535.asSourceLimitRepresentation inputs

    wholeProjectiveFamilyRequired :
      Bool

    wholeProjectiveFamilyRequiredIsTrue :
      wholeProjectiveFamilyRequired ≡ true

    selectedCutoffSuffices :
      Bool

    selectedCutoffSufficesIsFalse :
      selectedCutoffSuffices ≡ false

open YMProjectiveMereologyReceipt public

projectiveInputsToMereologyReceipt :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family}
    (inputs :
      R535.PhysicalProjectiveCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family) →
  YMProjectiveMereologyReceipt
    Configuration Event
    limitLaws quotient division family inputs
projectiveInputsToMereologyReceipt inputs = record
  { reconstructedWhole = R535.asSourceLimitRepresentation inputs
  ; reconstructedWholeIsCanonical = refl
  ; wholeProjectiveFamilyRequired = true
  ; wholeProjectiveFamilyRequiredIsTrue = refl
  ; selectedCutoffSuffices = false
  ; selectedCutoffSufficesIsFalse = refl
  }

------------------------------------------------------------------------
-- WEXT / MARKED-CLUSTER CONSUMER-CONDITIONED MEREOLOGY
--
-- The covariance consumer retains exactly the clusters touching both marked
-- supports.  This is a projection of the local cluster family, not a claim
-- that every local cluster is part of the terminal two-point observable.
------------------------------------------------------------------------

consumerRelevantClusters :
  ∀ {Measure Observable Scale Volume Root Source Cluster dataSet laws}
    (source :
      Marked.LiteralWilsonMarkedLocalizationSource
        {Measure = Measure}
        {Observable = Observable}
        {Scale = Scale}
        {Volume = Volume}
        {Root = Root}
        {Source = Source}
        {Cluster = Cluster}
        dataSet laws)
    (cutoff : Nat)
    (left right : Observable) →
  List Cluster
consumerRelevantClusters source cutoff left right =
  let expansion = Marked.markedExpansion source cutoff left right
      locality = Diff.supportLocality expansion
  in
  Diff.filterTwoSupport
    (Diff.touchesLeft locality)
    (Diff.touchesRight locality)
    (Diff.clusters expansion)

consumerRelevantClustersAreLiteralTwoSupportFilter :
  ∀ {Measure Observable Scale Volume Root Source Cluster dataSet laws}
    (source :
      Marked.LiteralWilsonMarkedLocalizationSource
        {Measure = Measure}
        {Observable = Observable}
        {Scale = Scale}
        {Volume = Volume}
        {Root = Root}
        {Source = Source}
        {Cluster = Cluster}
        dataSet laws)
    (cutoff : Nat)
    (left right : Observable) →
  consumerRelevantClusters source cutoff left right
  ≡
  let expansion = Marked.markedExpansion source cutoff left right
      locality = Diff.supportLocality expansion
  in
  Diff.filterTwoSupport
    (Diff.touchesLeft locality)
    (Diff.touchesRight locality)
    (Diff.clusters expansion)
consumerRelevantClustersAreLiteralTwoSupportFilter source cutoff left right = refl

------------------------------------------------------------------------
-- STATUS: this is a cross-cut theorem/architecture bridge only.
------------------------------------------------------------------------

ymProjectiveMereologyBridgeCreatesClayCompletion : Bool
ymProjectiveMereologyBridgeCreatesClayCompletion = false

ymProjectiveMereologyBridgeCreatesClayCompletionIsFalse :
  ymProjectiveMereologyBridgeCreatesClayCompletion ≡ false
ymProjectiveMereologyBridgeCreatesClayCompletionIsFalse = refl
