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
  { RegularBackground = always
  ; green = λ index source → one
  ; gradientGreen = λ index source → one
  ; secondGradientGreen = λ index source → one
  ; sourceNorm = λ source → one
  ; stateNorm = λ state → one
  ; multiply = oneBinary
  ; LessEqual = λ left right → Holds
  ; CG = one
  ; CGradG = one
  ; CSecondG = one
  ; theorem31GreenBound = λ index source regular → holds
  ; theorem31GradientGreenBound = λ index source regular → holds
  ; theorem31SecondGradientGreenBound =
      λ index source regular → holds
  ; Kernel = One
  ; greenKernel = λ index → one
  ; gradientKernel = λ index → one
  ; secondGradientKernel = λ index → one
  ; KernelExponentialDecay = always
  ; theorem31GreenKernelDecay = λ index regular → holds
  ; theorem31GradientKernelDecay = λ index regular → holds
  ; theorem31SecondGradientKernelDecay = λ index regular → holds
  ; GaugeCovariant = λ operator → Holds
  ; theorem31GaugeCovariance = holds
  ; AnalyticInBackground = λ operator → Holds
  ; theorem34GreenAnalytic = holds
  ; theorem34GradientGreenAnalytic = holds
  ; theorem34SecondGradientGreenAnalytic = holds
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
  { dashiPeriodicLattice = λ index → one
  ; balabanPeriodicLattice = λ index → one
  ; dashiPeriodicLatticeMatchesBalabanLattice = λ index → refl
  ; dashiBondField = λ index → one
  ; balabanOneForm = λ index → one
  ; dashiBondFieldMatchesBalabanOneForm = λ index → refl
  ; dashiGaugeAction = one
  ; balabanGaugeAction = one
  ; dashiGaugeActionMatchesBalabanGaugeAction = refl
  ; dashiReferenceOperator = λ index → one
  ; balabanReferenceOperator = λ index → one
  ; dashiReferenceOperatorMatchesBalabanOperator = λ index → refl
  ; dashiFullHessian = λ index → one
  ; balabanBackgroundHessian = λ index → one
  ; dashiFullHessianMatchesBalabanBackgroundHessian = λ index → refl
  ; repositoryGreen = λ index source → one
  ; repositoryGradientGreen = λ index source → one
  ; repositorySecondGradientGreen = λ index source → one
  ; dashiGreenMatchesBalabanPropagator = λ index source → refl
  ; dashiGradientGreenMatchesBalabanGradientPropagator =
      λ index source → refl
  ; dashiSecondGradientGreenMatchesBalabanSecondGradientPropagator =
      λ index source → refl
  ; repositorySourceNorm = λ source → one
  ; repositoryStateNorm = λ state → one
  ; dashiWeightedNormMatchesBalabanWeightedNorm = λ source → refl
  ; dashiDerivativeNormMatchesBalabanDerivativeNorm = λ state → refl
  ; dashiSecondDerivativeNormMatchesBalabanSecondDerivativeNorm =
      λ state → refl
  ; dashiPatchGeometry = λ index → one
  ; balabanPatchGeometry = λ index → one
  ; dashiPatchGeometryImpliesBalabanDomainHypotheses =
      λ index admissible → refl
  ; dashiSmallFieldImpliesBalabanSmallField =
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
  { AdmissibleCoarseField = λ index coarse → Holds
  ; backgroundFluctuation = λ index coarse → one
  ; Critical = always3
  ; Minimizer = always3
  ; GaugeEquivalent = always2
  ; theorem1BackgroundCritical =
      λ index coarse admissible → holds
  ; theorem1BackgroundMinimizes =
      λ index coarse admissible → holds
  ; theorem1BackgroundUniqueModuloGauge =
      λ index coarse fluctuation admissible critical → holds
  ; AnalyticBackgroundMap = Holds
  ; ExponentiallyLocalBackgroundMap = Holds
  ; BackgroundDerivativeExponentiallyDecays = Holds
  ; backgroundAnalytic = holds
  ; backgroundExponentiallyLocal = holds
  ; backgroundDerivativeDecay = holds
  ; norm = λ fluctuation → one
  ; radius = one
  ; LessEqual = λ left right → Holds
  ; backgroundInsideUniformRadius =
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
  { dashiBackgroundMap = one
  ; balabanVariationalBackgroundMap = one
  ; dashiBackgroundMapMatchesBalabanVariationalBackground = refl
  ; dashiRGCoordinates = one
  ; balabanRGCoordinates = one
  ; dashiRGCoordinatesMatchBalabanRGCoordinates = refl
  ; repositoryBackgroundFluctuation = λ index coarse → one
  ; dashiBackgroundFluctuationMatchesPublished =
      λ index coarse → refl
  ; dashiAdmissibleImpliesBalabanAdmissible =
      λ index coarse admissible → holds
  ; publishedCriticalImpliesRepositoryCritical =
      λ index coarse fluctuation critical → holds
  ; repositoryCriticalImpliesPublishedCritical =
      λ index coarse fluctuation critical → holds
  ; publishedMinimizerImpliesRepositoryMinimizer =
      λ index coarse fluctuation minimizer → holds
  ; publishedGaugeEquivalentImpliesRepositoryGaugeEquivalent =
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
  { coupling = λ scale → one
  ; smallCouplingThreshold = one
  ; absCoupling = λ coupling → one
  ; LessEqual = λ left right → Holds
  ; RunningCouplingsRemainSmall = Holds
  ; runningCouplingsRemainSmall = holds
  ; couplingBelowThreshold = λ scale → holds
  ; effectiveAction = λ scale → one
  ; SmallFieldEffectiveActionControlled =
      λ scale action → Holds
  ; theorem1And3SmallFieldControl = λ scale → holds
  }

exactRGMatch :
  Exact.ExactSmallFieldRGCarrierMatch
    {RGCoordinates = One}
    publishedRG
    (λ scale action → Holds)
exactRGMatch = record
  { dashiRGCoordinates = one
  ; balabanRGCoordinates = one
  ; dashiRGCoordinatesMatchBalabanRGCoordinates = refl
  ; repositoryEffectiveAction = λ scale → one
  ; repositoryEffectiveActionMatchesPublished = λ scale → refl
  ; publishedControlImpliesRepositoryControl =
      λ scale action controlled → holds
  }

smallFieldRGRegression : Holds
smallFieldRGRegression =
  Exact.publishedSmallFieldRGAppliesToDashi
    publishedRG
    (λ scale action → Holds)
    exactRGMatch
    one
