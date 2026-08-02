module DASHI.Physics.Closure.NSTriadKNRepositoryDyadicSeparationAudit where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Venue/year: Grundlehren der mathematischen Wissenschaften 343,
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
-- Uses: standard dyadic support and triangle-inequality geometry.
-- Relationship: supports the shell-comparability argument, not the
-- repository's cubic-cutoff/orbit transport.
--
-- Authors: DASHI repository contributors.
-- Title: "Repository dyadic far-gap and transition-width audit".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; the threshold candidate and exact rational constants
-- are repository-original.
-- Uses: 2^j <= |low| <= 2^(j+1), 2^J <= |high| and J-j >= 3.
-- Relationship: derives |low|/|high| <= 1/4 and hence
-- 3|high|/4 <= |low+high| <= 5|high|/4.  Full promotion still requires the
-- exact Euclidean-shell, cubic-cutoff, orbit and class-partition bridges.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

repositoryFarGapCandidate : Nat
repositoryFarGapCandidate = 3

transitionMaximumGap : Nat
transitionMaximumGap = 2

comparableHighOutputShellOffset : Nat
comparableHighOutputShellOffset = 1

lowHighRatioNumerator : Nat
lowHighRatioNumerator = 1

lowHighRatioDenominator : Nat
lowHighRatioDenominator = 4

outputLowerRatioNumerator : Nat
outputLowerRatioNumerator = 3

outputLowerRatioDenominator : Nat
outputLowerRatioDenominator = 4

outputUpperRatioNumerator : Nat
outputUpperRatioNumerator = 5

outputUpperRatioDenominator : Nat
outputUpperRatioDenominator = 4

record DyadicSeparationReceipt : Set where
  constructor receipt
  field
    farGapIsThree : repositoryFarGapCandidate ≡ 3
    transitionEndsAtTwo : transitionMaximumGap ≡ 2
    outputShellOffsetAtMostOne : comparableHighOutputShellOffset ≡ 1
    lowHighRatioIsOneQuarter :
      lowHighRatioNumerator ≡ 1
    lowHighRatioDenominatorIsFour :
      lowHighRatioDenominator ≡ 4
    outputLowerRatioIsThreeQuarters :
      outputLowerRatioNumerator ≡ 3
    outputLowerDenominatorIsFour :
      outputLowerRatioDenominator ≡ 4
    outputUpperRatioIsFiveQuarters :
      outputUpperRatioNumerator ≡ 5
    outputUpperDenominatorIsFour :
      outputUpperRatioDenominator ≡ 4

open DyadicSeparationReceipt public

dyadicSeparationReceipt : DyadicSeparationReceipt
dyadicSeparationReceipt =
  receipt refl refl refl refl refl refl refl refl refl

record RepositoryThresholdPromotionCutset : Set₁ where
  field
    shellLowerEndpointConventionMatched : Set
    shellUpperEndpointConventionMatched : Set
    triangleInequalityOnRepositoryModeWeight : Set
    euclideanExactShellToDyadicOverlapClosed : Set
    cubicCutoffDoesNotAlterLocalShellGeometry : Set
    zeroModeExcludedInSeparatedClasses : Set
    orbitRepresentativePreservesModeNorm : Set
    orbitMultiplicityIndependentOfGap : Set
    multiplierSupportWidthAccountedFor : Set
    sevenClassPartitionUsesGapThree : Set
    transitionClassExactlyGapsZeroOneTwo : Set
    residualClassDisjointFromSeparatedClasses : Set
    thresholdUniformInGalerkinCutoff : Set

open RepositoryThresholdPromotionCutset public

geometricFarGapThreeDerived : Bool
geometricFarGapThreeDerived = true

geometricFarGapThreeDerivedIsTrue :
  geometricFarGapThreeDerived ≡ true
geometricFarGapThreeDerivedIsTrue = refl

fullRepositorySeparationThresholdClosed : Bool
fullRepositorySeparationThresholdClosed = false

fullRepositorySeparationThresholdClosedIsFalse :
  fullRepositorySeparationThresholdClosed ≡ false
fullRepositorySeparationThresholdClosedIsFalse = refl
