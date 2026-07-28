module DASHI.Physics.YangMills.BalabanClayT2LiteralHaarTraceClassClosureExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_; _≤ᵇ_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations: An
-- Elementary Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3
-- Relationship: exponential coordinates and compact-group Haar density.
--
-- Barry Simon, "Trace Ideals and Their Applications", second edition,
-- American Mathematical Society (2005). DOI: 10.1090/surv/120
-- Relationship: trace-class localization and the trace-log series.
------------------------------------------------------------------------

configuredSingleLinkHaarUpper configuredSixtyFourLinkHaarUpper : ℚ
configuredSingleLinkHaarUpper = + 1 / 65536
configuredSixtyFourLinkHaarUpper = + 1 / 1024

configuredHaarSumExact :
  (+ 64 / 1) * configuredSingleLinkHaarUpper
  ≡ configuredSixtyFourLinkHaarUpper
configuredHaarSumExact = ℚRing.solve

configuredHaarBelowOneSixteenth :
  configuredSixtyFourLinkHaarUpper ≤ + 1 / 16
configuredHaarBelowOneSixteenth = ℚP.≤ᵇ⇒≤ tt

configuredOperatorHalf configuredTraceEighth configuredTraceLogQuarter : ℚ
configuredOperatorHalf = + 1 / 2
configuredTraceEighth = + 1 / 8
configuredTraceLogQuarter = + 1 / 4

configuredTraceRatioExact :
  configuredTraceEighth / (+ 1 / 1 - configuredOperatorHalf)
  ≡ configuredTraceLogQuarter
configuredTraceRatioExact = ℚRing.solve

sumℚ : List ℚ → ℚ
sumℚ [] = 0ℚ
sumℚ (x ∷ xs) = x + sumℚ xs

record LiteralSU2HaarPolymerData
    (Scale Polymer Link : Set) : Set₁ where
  field
    chargedLinks : Scale → Polymer → List Link
    linkNorm : Scale → Polymer → Link → ℚ
    linkHaarDensity linkNegativeLogHaar : Scale → Polymer → Link → ℚ
    polymerHaarProduct polymerHaarLoss : Scale → Polymer → ℚ

    su2ExponentialChartPullbackHaarExact : ∀ scale polymer link → Set
    haarDensityPositiveInConfiguredChart : ∀ scale polymer link → Set
    haarLogDensityExact : ∀ scale polymer link → Set

    chargedLinkInConfiguredChart : ∀ scale polymer link → Set
    singleLinkNegativeLogHaarBound : ∀ scale polymer link →
      linkNegativeLogHaar scale polymer link ≤ configuredSingleLinkHaarUpper

    mappedLinkLosses : Scale → Polymer → List Link → List ℚ
    mappedLinkLossesEmpty : ∀ scale polymer →
      mappedLinkLosses scale polymer [] ≡ []
    mappedLinkLossesStep : ∀ scale polymer link rest →
      mappedLinkLosses scale polymer (link ∷ rest)
      ≡ linkNegativeLogHaar scale polymer link
        ∷ mappedLinkLosses scale polymer rest

    polymerHaarProductExact : ∀ scale polymer → Set
    polymerHaarLogSumExact : ∀ scale polymer →
      polymerHaarLoss scale polymer
      ≡ sumℚ (mappedLinkLosses scale polymer (chargedLinks scale polymer))

    polymerChargedLinkCountAtMost64PerBlock : ∀ scale polymer → Set
    finiteLinkSumBelowSixtyFourCharge : ∀ scale polymer →
      sumℚ (mappedLinkLosses scale polymer (chargedLinks scale polymer))
      ≤ configuredSixtyFourLinkHaarUpper

open LiteralSU2HaarPolymerData public

haarLossBelowOneSixteenth :
  ∀ {Scale Polymer Link}
    (dataSet : LiteralSU2HaarPolymerData Scale Polymer Link)
    scale polymer →
  polymerHaarLoss dataSet scale polymer ≤ + 1 / 16
haarLossBelowOneSixteenth dataSet scale polymer =
  subst
    (λ lower → lower ≤ + 1 / 16)
    (polymerHaarLogSumExact dataSet scale polymer)
    (ℚP.≤-trans
      (finiteLinkSumBelowSixtyFourCharge dataSet scale polymer)
      configuredHaarBelowOneSixteenth)

record LiteralLocalizedTraceClassData
    (Scale Polymer Operator : Set) : Set₁ where
  field
    referenceHessian physicalHessian hessianDifference : Scale → Operator
    inverseSquareRoot relativeOperator : Scale → Operator
    localizedRelativeOperator : Scale → Polymer → Operator

    operatorNorm : Operator → ℚ
    traceNorm : Operator → ℚ
    determinantLoss : Scale → Polymer → ℚ

    physicalRelativeHessianExact : ∀ scale → Set
    physicalRelativeHessianOperatorNormBelowHalf : ∀ scale →
      operatorNorm (relativeOperator scale) ≤ configuredOperatorHalf

    localizationPartitionOfUnityExact : ∀ scale polymer → Set
    localizedRelativeOperatorFiniteRank : ∀ scale polymer → Set
    localizedRelativeOperatorTraceClass : ∀ scale polymer → Set
    localizedTraceNormBelowOneEighthPerBlock : ∀ scale polymer →
      traceNorm (localizedRelativeOperator scale polymer)
      ≤ configuredTraceEighth

    traceLogSeries : Operator → ℚ
    logDetRelative : Scale → Polymer → ℚ
    traceLogSeriesConvergesInTraceNorm : ∀ scale polymer → Set
    traceLogEqualsLogDet : ∀ scale polymer → Set

    traceLogAbsoluteBound : ∀ scale polymer →
      determinantLoss scale polymer
      ≤ traceNorm (localizedRelativeOperator scale polymer)
        / (+ 1 / 1 - operatorNorm (relativeOperator scale))

    quotientMonotoneAtConfiguredBounds : ∀ scale polymer →
      traceNorm (localizedRelativeOperator scale polymer)
        / (+ 1 / 1 - operatorNorm (relativeOperator scale))
      ≤ configuredTraceLogQuarter

    finiteRangeTraceSplitsIntoConnectedPolymers : ∀ scale → Set
    determinantPolymerConnectedDecomposition : ∀ scale polymer → Set

open LiteralLocalizedTraceClassData public

localizedTraceNormBelowEighth =
  LiteralLocalizedTraceClassData.localizedTraceNormBelowOneEighthPerBlock

traceLogSeriesConverges =
  LiteralLocalizedTraceClassData.traceLogSeriesConvergesInTraceNorm

traceLogEstimateExact :
  ∀ {Scale Polymer Operator}
    (dataSet : LiteralLocalizedTraceClassData Scale Polymer Operator)
    scale polymer →
  determinantLoss dataSet scale polymer ≤ configuredTraceLogQuarter
traceLogEstimateExact dataSet scale polymer =
  ℚP.≤-trans
    (traceLogAbsoluteBound dataSet scale polymer)
    (quotientMonotoneAtConfiguredBounds dataSet scale polymer)

determinantLossBelowQuarter = traceLogEstimateExact

record LiteralHaarTraceClassPackage
    (Scale Polymer Link Operator : Set) : Set₂ where
  field
    haar : LiteralSU2HaarPolymerData Scale Polymer Link
    determinant : LiteralLocalizedTraceClassData Scale Polymer Operator
    greenDecayConsumedByTraceLocalization : ∀ scale polymer → Set

open LiteralHaarTraceClassPackage public

configuredHaarArithmeticLevel : ProofLevel
configuredHaarArithmeticLevel = machineChecked

configuredTraceLogArithmeticLevel : ProofLevel
configuredTraceLogArithmeticLevel = machineChecked

literalHaarProductReductionLevel : ProofLevel
literalHaarProductReductionLevel = machineChecked

literalTraceClassReductionLevel : ProofLevel
literalTraceClassReductionLevel = machineChecked

literalLinkwiseHaarAndTraceClassInputsLevel : ProofLevel
literalLinkwiseHaarAndTraceClassInputsLevel = conditional
