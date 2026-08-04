module DASHI.Physics.YangMills.BalabanPublishedSourceTheoremRegression where

import DASHI.Physics.YangMills.BalabanPublishedAnalyticAuthorities as Published
import DASHI.Physics.YangMills.BalabanPublishedSourceTheoremAuthorities as Source

------------------------------------------------------------------------
-- One-point regressions for the source-faithful theorem records and their
-- conversion to the convenience authority layer.  These exercise the exact
-- hypothesis-bearing record construction without asserting any new analysis.
------------------------------------------------------------------------

data One : Set where
  one : One

data Holds : Set where
  holds : Holds

always : One → Set
always value = Holds

always2 : One → One → Set
always2 left right = Holds

always3 : One → One → One → Set
always3 first second third = Holds

oneBinary : One → One → One
oneBinary left right = one

propagatorSource :
  Source.PublishedPropagatorTheorems31And33 One One One One One
propagatorSource = record
  { M = one
  ; M1 = one
  ; epsilon0 = one
  ; a0 = one
  ; beta = one
  ; beta0 = one
  ; LessEqual = λ left right → Holds
  ; StrictLess = λ left right → Holds
  ; DomainSequenceSatisfies21And22 = always
  ; BackgroundSatisfiesRegularity35 = always
  ; MAtLeastM1 = always
  ; MEpsilon0BelowA0 = always
  ; BetaInAdmissibleRange = always
  ; ExactPropagatorHypotheses = always
  ; hypothesesContainDomainSequence = λ index hypotheses → holds
  ; hypothesesContainBackgroundRegularity =
      λ index hypotheses → holds
  ; hypothesesContainMThreshold = λ index hypotheses → holds
  ; hypothesesContainSmallness = λ index hypotheses → holds
  ; hypothesesContainBetaRange = λ index hypotheses → holds
  ; greenPrime = λ index source → one
  ; green = λ index source → one
  ; gradientGreen = λ index source → one
  ; secondGradientGreen = λ index source → one
  ; sourceNorm = λ source → one
  ; propagatedStateNorm = λ state → one
  ; multiply = oneBinary
  ; CG = one
  ; CGradG = one
  ; CSecondG = one
  ; theorem31GreenPrimeBound =
      λ index source hypotheses → holds
  ; theorem33GreenBound = λ index source hypotheses → holds
  ; theorem33GradientGreenBound =
      λ index source hypotheses → holds
  ; theorem33SecondGradientGreenBound =
      λ index source hypotheses → holds
  ; greenKernel = λ index → one
  ; gradientKernel = λ index → one
  ; secondGradientKernel = λ index → one
  ; KernelExponentialDecay = always
  ; theorem33GreenKernelDecay = λ index hypotheses → holds
  ; theorem33GradientKernelDecay = λ index hypotheses → holds
  ; theorem33SecondGradientKernelDecay =
      λ index hypotheses → holds
  ; GaugeCovariant = λ operator → Holds
  ; theorem33GaugeCovariance = holds
  ; AnalyticInBackground = λ operator → Holds
  ; publishedBackgroundAnalyticity = holds
  ; publishedGradientBackgroundAnalyticity = holds
  ; publishedSecondGradientBackgroundAnalyticity = holds
  }

propagatorAuthority :
  Published.PublishedBackgroundPropagatorAuthority One One One One
propagatorAuthority =
  Source.propagatorTheorems31And33ToAuthority propagatorSource

propagatorSourceConversionRegression : Holds
propagatorSourceConversionRegression =
  Published.theorem31GreenBound propagatorAuthority one one holds

variationalSource :
  Source.PublishedVariationalTheorem1Exact One One One One
variationalSource = record
  { epsilon0 = one
  ; epsilon1 = one
  ; a0 = one
  ; a1 = one
  ; B3 = one
  ; LessEqual = λ left right → Holds
  ; StrictLess = λ left right → Holds
  ; NestedDomainGeometry = always
  ; CoarseRegularityCondition7 = always2
  ; Epsilon1BelowA1 = Holds
  ; B3Epsilon1BelowEpsilon0 = Holds
  ; Epsilon0BelowA0 = Holds
  ; epsilon1BelowA1 = holds
  ; b3Epsilon1BelowEpsilon0 = holds
  ; epsilon0BelowA0 = holds
  ; ExactVariationalHypotheses = always2
  ; hypothesesContainNestedGeometry =
      λ index coarse hypotheses → holds
  ; hypothesesContainCoarseRegularity =
      λ index coarse hypotheses → holds
  ; backgroundFluctuation = λ index coarse → one
  ; Critical = always3
  ; Minimizer = always3
  ; GaugeEquivalent = always2
  ; theorem1BackgroundCritical =
      λ index coarse hypotheses → holds
  ; theorem1BackgroundMinimizes =
      λ index coarse hypotheses → holds
  ; theorem1BackgroundUniqueModuloGauge =
      λ index coarse fluctuation hypotheses critical → holds
  ; AnalyticBackgroundMap = Holds
  ; ExponentiallyLocalBackgroundMap = Holds
  ; BackgroundDerivativeExponentiallyDecays = Holds
  ; theorem1BackgroundAnalytic = holds
  ; theorem1BackgroundExponentiallyLocal = holds
  ; theorem1BackgroundDerivativeDecay = holds
  ; norm = λ fluctuation → one
  ; radius = one
  ; backgroundInsideUniformRadius =
      λ index coarse hypotheses → holds
  }

variationalAuthority :
  Published.PublishedVariationalBackgroundAuthority One One One One
variationalAuthority = Source.variationalTheorem1ToAuthority variationalSource

variationalSourceConversionRegression : Holds
variationalSourceConversionRegression =
  Published.theorem1BackgroundCritical variationalAuthority one one holds

smallFieldSource :
  Source.PublishedSmallFieldTheorems1And3Exact One One One One
smallFieldSource = record
  { coupling = λ scale → one
  ; gamma = one
  ; absCoupling = λ coupling → one
  ; LessEqual = λ left right → Holds
  ; StrictLess = λ left right → Holds
  ; DimensionIsFour = Holds
  ; GaugeGroupCompactSemisimpleSubgroupOfUnitary = Holds
  ; RenormalizationTransformationsAreSmallField = Holds
  ; EffectiveCouplingsInZeroGamma = Holds
  ; dimensionIsFour = holds
  ; gaugeGroupCompactSemisimpleSubgroupOfUnitary = holds
  ; renormalizationTransformationsAreSmallField = holds
  ; effectiveCouplingsInZeroGamma = holds
  ; CouplingPositive = always
  ; couplingPositive = λ scale → holds
  ; couplingBelowGamma = λ scale → holds
  ; effectiveAction = λ scale → one
  ; InductiveAssumptions11Through122 = always2
  ; theorem3InductiveControl = λ scale → holds
  }

smallFieldAuthority : Published.PublishedSmallFieldRGAuthority One One One One
smallFieldAuthority = Source.smallFieldTheorems1And3ToAuthority smallFieldSource

smallFieldSourceConversionRegression : Holds
smallFieldSourceConversionRegression =
  Published.theorem1And3SmallFieldControl smallFieldAuthority one
