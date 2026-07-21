module DASHI.Physics.YangMills.BalabanExactPublishedCarrierMatchingRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanPublishedAnalyticAuthorities as Published
import DASHI.Physics.YangMills.BalabanExactPublishedCarrierMatching as Exact

------------------------------------------------------------------------
-- A finite one-point regression instantiates every exact matching lane.  It is
-- deliberately mathematically trivial; its role is to exercise projection
-- resolution, rewrite orientation and record construction in the generic
-- transport code.
------------------------------------------------------------------------

data One : Set where
  one : One

data Holds : Set where
  holds : Holds

oneBinary : One → One → One
oneBinary left right = one

always : One → Set
always value = Holds

always2 : One → One → Set
always2 left right = Holds

always3 : One → One → One → Set
always3 first second third = Holds

publishedPropagator :
  Published.PublishedBackgroundPropagatorAuthority One One One One
publishedPropagator = record
  { Published.RegularBackground = always
  ; Published.green = λ index source → one
  ; Published.gradientGreen = λ index source → one
  ; Published.secondGradientGreen = λ index source → one
  ; Published.sourceNorm = λ source → one
  ; Published.stateNorm = λ state → one
  ; Published.multiply = oneBinary
  ; Published.LessEqual = λ left right → Holds
  ; Published.CG = one
  ; Published.CGradG = one
  ; Published.CSecondG = one
  ; Published.theorem31GreenBound = λ index source regular → holds
  ; Published.theorem31GradientGreenBound = λ index source regular → holds
  ; Published.theorem31SecondGradientGreenBound =
      λ index source regular → holds
  ; Published.Kernel = One
  ; Published.greenKernel = λ index → one
  ; Published.gradientKernel = λ index → one
  ; Published.secondGradientKernel = λ index → one
  ; Published.KernelExponentialDecay = always
  ; Published.theorem31GreenKernelDecay = λ index regular → holds
  ; Published.theorem31GradientKernelDecay = λ index regular → holds
  ; Published.theorem31SecondGradientKernelDecay = λ index regular → holds
  ; Published.GaugeCovariant = λ operator → Holds
  ; Published.theorem31GaugeCovariance = holds
  ; Published.AnalyticInBackground = λ operator → Holds
  ; Published.theorem34GreenAnalytic = holds
  ; Published.theorem34GradientGreenAnalytic = holds
  ; Published.theorem34SecondGradientGreenAnalytic = holds
  }

exactPropagatorMatch :
  Exact.ExactPropagatorCarrierMatch
    {Lattice = One}
    {BondField = One}
    {GaugeAction = One}
    {Operator = One}
    {PatchGeometry = One}
    publishedPropagator always
exactPropagatorMatch = record
  { Exact.dashiPeriodicLattice = λ index → one
  ; Exact.balabanPeriodicLattice = λ index → one
  ; Exact.dashiPeriodicLatticeMatchesBalabanLattice = λ index → refl
  ; Exact.dashiBondField = λ index → one
  ; Exact.balabanOneForm = λ index → one
  ; Exact.dashiBondFieldMatchesBalabanOneForm = λ index → refl
  ; Exact.dashiGaugeAction = one
  ; Exact.balabanGaugeAction = one
  ; Exact.dashiGaugeActionMatchesBalabanGaugeAction = refl
  ; Exact.dashiReferenceOperator = λ index → one
  ; Exact.balabanReferenceOperator = λ index → one
  ; Exact.dashiReferenceOperatorMatchesBalabanOperator = λ index → refl
  ; Exact.dashiFullHessian = λ index → one
  ; Exact.balabanBackgroundHessian = λ index → one
  ; Exact.dashiFullHessianMatchesBalabanBackgroundHessian = λ index → refl
  ; Exact.repositoryGreen = λ index source → one
  ; Exact.repositoryGradientGreen = λ index source → one
  ; Exact.repositorySecondGradientGreen = λ index source → one
  ; Exact.dashiGreenMatchesBalabanPropagator = λ index source → refl
  ; Exact.dashiGradientGreenMatchesBalabanGradientPropagator =
      λ index source → refl
  ; Exact.dashiSecondGradientGreenMatchesBalabanSecondGradientPropagator =
      λ index source → refl
  ; Exact.repositorySourceNorm = λ source → one
  ; Exact.repositoryStateNorm = λ state → one
  ; Exact.dashiWeightedNormMatchesBalabanWeightedNorm = λ source → refl
  ; Exact.dashiDerivativeNormMatchesBalabanDerivativeNorm = λ state → refl
  ; Exact.dashiSecondDerivativeNormMatchesBalabanSecondDerivativeNorm =
      λ state → refl
  ; Exact.dashiPatchGeometry = λ index → one
  ; Exact.balabanPatchGeometry = λ index → one
  ; Exact.dashiPatchGeometryImpliesBalabanDomainHypotheses =
      λ index admissible → refl
  ; Exact.dashiSmallFieldImpliesBalabanSmallField =
      λ index admissible → holds
  }

propagatorCertificate :
  Exact.RepositoryUniformPropagatorCertificate One One One One
propagatorCertificate =
  Exact.publishedPropagatorAppliesToDashi
    publishedPropagator always exactPropagatorMatch

propagatorBoundRegression : Holds
propagatorBoundRegression =
  Exact.RepositoryUniformPropagatorCertificate.greenBound
    propagatorCertificate one one holds

publishedVariational :
  Published.PublishedVariationalBackgroundAuthority One One One One
publishedVariational = record
  { Published.AdmissibleCoarseField = λ index coarse → Holds
  ; Published.backgroundFluctuation = λ index coarse → one
  ; Published.Critical = always3
  ; Published.Minimizer = always3
  ; Published.GaugeEquivalent = always2
  ; Published.theorem1BackgroundCritical =
      λ index coarse admissible → holds
  ; Published.theorem1BackgroundMinimizes =
      λ index coarse admissible → holds
  ; Published.theorem1BackgroundUniqueModuloGauge =
      λ index coarse fluctuation admissible critical → holds
  ; Published.AnalyticBackgroundMap = Holds
  ; Published.ExponentiallyLocalBackgroundMap = Holds
  ; Published.BackgroundDerivativeExponentiallyDecays = Holds
  ; Published.backgroundAnalytic = holds
  ; Published.backgroundExponentiallyLocal = holds
  ; Published.backgroundDerivativeDecay = holds
  ; Published.norm = λ fluctuation → one
  ; Published.radius = one
  ; Published.LessEqual = λ left right → Holds
  ; Published.backgroundInsideUniformRadius =
      λ index coarse admissible → holds
  }

exactVariationalMatch :
  Exact.ExactVariationalCarrierMatch
    {BackgroundMap = One}
    {RGCoordinates = One}
    publishedVariational
    (λ index coarse → Holds)
    always3
    always3
    always2
exactVariationalMatch = record
  { Exact.dashiBackgroundMap = one
  ; Exact.balabanVariationalBackgroundMap = one
  ; Exact.dashiBackgroundMapMatchesBalabanVariationalBackground = refl
  ; Exact.dashiRGCoordinates = one
  ; Exact.balabanRGCoordinates = one
  ; Exact.dashiRGCoordinatesMatchBalabanRGCoordinates = refl
  ; Exact.repositoryBackgroundFluctuation = λ index coarse → one
  ; Exact.dashiBackgroundFluctuationMatchesPublished =
      λ index coarse → refl
  ; Exact.dashiAdmissibleImpliesBalabanAdmissible =
      λ index coarse admissible → holds
  ; Exact.publishedCriticalImpliesRepositoryCritical =
      λ index coarse fluctuation critical → holds
  ; Exact.repositoryCriticalImpliesPublishedCritical =
      λ index coarse fluctuation critical → holds
  ; Exact.publishedMinimizerImpliesRepositoryMinimizer =
      λ index coarse fluctuation minimizer → holds
  ; Exact.publishedGaugeEquivalentImpliesRepositoryGaugeEquivalent =
      λ left right equivalent → holds
  }

finiteBackgroundCertificate :
  Exact.RepositoryFiniteBackgroundCertificate One One One
finiteBackgroundCertificate =
  Exact.publishedVariationalBackgroundAppliesToDashi
    publishedVariational
    (λ index coarse → Holds)
    always3
    always3
    always2
    exactVariationalMatch

backgroundCriticalRegression : Holds
backgroundCriticalRegression =
  Exact.RepositoryFiniteBackgroundCertificate.backgroundCritical
    finiteBackgroundCertificate one one holds

publishedRG : Published.PublishedSmallFieldRGAuthority One One One One
publishedRG = record
  { Published.coupling = λ scale → one
  ; Published.smallCouplingThreshold = one
  ; Published.absCoupling = λ coupling → one
  ; Published.LessEqual = λ left right → Holds
  ; Published.RunningCouplingsRemainSmall = Holds
  ; Published.runningCouplingsRemainSmall = holds
  ; Published.couplingBelowThreshold = λ scale → holds
  ; Published.effectiveAction = λ scale → one
  ; Published.SmallFieldEffectiveActionControlled =
      λ scale action → Holds
  ; Published.theorem1And3SmallFieldControl = λ scale → holds
  }

exactRGMatch :
  Exact.ExactSmallFieldRGCarrierMatch
    {RGCoordinates = One}
    publishedRG
    (λ scale action → Holds)
exactRGMatch = record
  { Exact.dashiRGCoordinates = one
  ; Exact.balabanRGCoordinates = one
  ; Exact.dashiRGCoordinatesMatchBalabanRGCoordinates = refl
  ; Exact.repositoryEffectiveAction = λ scale → one
  ; Exact.repositoryEffectiveActionMatchesPublished = λ scale → refl
  ; Exact.publishedControlImpliesRepositoryControl =
      λ scale action controlled → holds
  }

smallFieldRGRegression : Holds
smallFieldRGRegression =
  Exact.publishedSmallFieldRGAppliesToDashi
    publishedRG
    (λ scale action → Holds)
    exactRGMatch
    one
