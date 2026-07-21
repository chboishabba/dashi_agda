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
  { Source.M = one
  ; Source.M1 = one
  ; Source.epsilon0 = one
  ; Source.a0 = one
  ; Source.beta = one
  ; Source.beta0 = one
  ; Source.LessEqual = λ left right → Holds
  ; Source.StrictLess = λ left right → Holds
  ; Source.DomainSequenceSatisfies21And22 = always
  ; Source.BackgroundSatisfiesRegularity35 = always
  ; Source.MAtLeastM1 = always
  ; Source.MEpsilon0BelowA0 = always
  ; Source.BetaInAdmissibleRange = always
  ; Source.ExactPropagatorHypotheses = always
  ; Source.hypothesesContainDomainSequence = λ index hypotheses → holds
  ; Source.hypothesesContainBackgroundRegularity =
      λ index hypotheses → holds
  ; Source.hypothesesContainMThreshold = λ index hypotheses → holds
  ; Source.hypothesesContainSmallness = λ index hypotheses → holds
  ; Source.hypothesesContainBetaRange = λ index hypotheses → holds
  ; Source.greenPrime = λ index source → one
  ; Source.green = λ index source → one
  ; Source.gradientGreen = λ index source → one
  ; Source.secondGradientGreen = λ index source → one
  ; Source.sourceNorm = λ source → one
  ; Source.propagatedStateNorm = λ state → one
  ; Source.multiply = oneBinary
  ; Source.CG = one
  ; Source.CGradG = one
  ; Source.CSecondG = one
  ; Source.theorem31GreenPrimeBound =
      λ index source hypotheses → holds
  ; Source.theorem33GreenBound = λ index source hypotheses → holds
  ; Source.theorem33GradientGreenBound =
      λ index source hypotheses → holds
  ; Source.theorem33SecondGradientGreenBound =
      λ index source hypotheses → holds
  ; Source.greenKernel = λ index → one
  ; Source.gradientKernel = λ index → one
  ; Source.secondGradientKernel = λ index → one
  ; Source.KernelExponentialDecay = always
  ; Source.theorem33GreenKernelDecay = λ index hypotheses → holds
  ; Source.theorem33GradientKernelDecay = λ index hypotheses → holds
  ; Source.theorem33SecondGradientKernelDecay =
      λ index hypotheses → holds
  ; Source.GaugeCovariant = λ operator → Holds
  ; Source.theorem33GaugeCovariance = holds
  ; Source.AnalyticInBackground = λ operator → Holds
  ; Source.publishedBackgroundAnalyticity = holds
  ; Source.publishedGradientBackgroundAnalyticity = holds
  ; Source.publishedSecondGradientBackgroundAnalyticity = holds
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
  { Source.epsilon0 = one
  ; Source.epsilon1 = one
  ; Source.a0 = one
  ; Source.a1 = one
  ; Source.B3 = one
  ; Source.LessEqual = λ left right → Holds
  ; Source.StrictLess = λ left right → Holds
  ; Source.NestedDomainGeometry = always
  ; Source.CoarseRegularityCondition7 = always2
  ; Source.Epsilon1BelowA1 = Holds
  ; Source.B3Epsilon1BelowEpsilon0 = Holds
  ; Source.Epsilon0BelowA0 = Holds
  ; Source.epsilon1BelowA1 = holds
  ; Source.b3Epsilon1BelowEpsilon0 = holds
  ; Source.epsilon0BelowA0 = holds
  ; Source.ExactVariationalHypotheses = always2
  ; Source.hypothesesContainNestedGeometry =
      λ index coarse hypotheses → holds
  ; Source.hypothesesContainCoarseRegularity =
      λ index coarse hypotheses → holds
  ; Source.backgroundFluctuation = λ index coarse → one
  ; Source.Critical = always3
  ; Source.Minimizer = always3
  ; Source.GaugeEquivalent = always2
  ; Source.theorem1BackgroundCritical =
      λ index coarse hypotheses → holds
  ; Source.theorem1BackgroundMinimizes =
      λ index coarse hypotheses → holds
  ; Source.theorem1BackgroundUniqueModuloGauge =
      λ index coarse fluctuation hypotheses critical → holds
  ; Source.AnalyticBackgroundMap = Holds
  ; Source.ExponentiallyLocalBackgroundMap = Holds
  ; Source.BackgroundDerivativeExponentiallyDecays = Holds
  ; Source.theorem1BackgroundAnalytic = holds
  ; Source.theorem1BackgroundExponentiallyLocal = holds
  ; Source.theorem1BackgroundDerivativeDecay = holds
  ; Source.norm = λ fluctuation → one
  ; Source.radius = one
  ; Source.backgroundInsideUniformRadius =
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
  { Source.coupling = λ scale → one
  ; Source.gamma = one
  ; Source.absCoupling = λ coupling → one
  ; Source.LessEqual = λ left right → Holds
  ; Source.StrictLess = λ left right → Holds
  ; Source.DimensionIsFour = Holds
  ; Source.GaugeGroupCompactSemisimpleSubgroupOfUnitary = Holds
  ; Source.RenormalizationTransformationsAreSmallField = Holds
  ; Source.EffectiveCouplingsInZeroGamma = Holds
  ; Source.dimensionIsFour = holds
  ; Source.gaugeGroupCompactSemisimpleSubgroupOfUnitary = holds
  ; Source.renormalizationTransformationsAreSmallField = holds
  ; Source.effectiveCouplingsInZeroGamma = holds
  ; Source.CouplingPositive = always
  ; Source.couplingPositive = λ scale → holds
  ; Source.couplingBelowGamma = λ scale → holds
  ; Source.effectiveAction = λ scale → one
  ; Source.InductiveAssumptions11Through122 = always2
  ; Source.theorem3InductiveControl = λ scale → holds
  }

smallFieldAuthority : Published.PublishedSmallFieldRGAuthority One One One One
smallFieldAuthority = Source.smallFieldTheorems1And3ToAuthority smallFieldSource

smallFieldSourceConversionRegression : Holds
smallFieldSourceConversionRegression =
  Published.theorem1And3SmallFieldControl smallFieldAuthority one
