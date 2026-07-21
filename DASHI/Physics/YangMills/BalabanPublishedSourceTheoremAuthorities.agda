module DASHI.Physics.YangMills.BalabanPublishedSourceTheoremAuthorities where

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPublishedAnalyticAuthorities

------------------------------------------------------------------------
-- Source-faithful theorem statements.
--
-- Propagator source:
--   T. Bałaban, Commun. Math. Phys. 99 (1985), 389--434,
--   Theorems 3.1 and 3.3.
--
-- Variational source:
--   T. Bałaban, Commun. Math. Phys. 102 (1985), 277--309,
--   Theorem 1.
--
-- Small-field RG source:
--   T. Bałaban, Commun. Math. Phys. 109 (1987), 249--301,
--   Theorems 1 and 3.  The running-coupling Theorem 2 is expressly deferred
--   to a separate perturbative paper and is not included here.
--
-- These records retain the source hypotheses that were compressed by the
-- earlier convenience authorities.  The conversion functions below show that
-- the convenience authorities are legitimate only after every source
-- hypothesis has been supplied.
------------------------------------------------------------------------

record PublishedPropagatorTheorems31And33
    (Index Source State Bound Kernel : Set) : Set₁ where
  field
    -- Parameters and source hypotheses.
    M M1 epsilon0 a0 beta beta0 : Bound
    LessEqual StrictLess : Bound → Bound → Set

    DomainSequenceSatisfies21And22 : Index → Set
    BackgroundSatisfiesRegularity35 : Index → Set
    MAtLeastM1 : Index → Set
    MEpsilon0BelowA0 : Index → Set
    BetaInAdmissibleRange : Index → Set

    ExactPropagatorHypotheses : Index → Set
    hypothesesContainDomainSequence : ∀ index →
      ExactPropagatorHypotheses index →
      DomainSequenceSatisfies21And22 index
    hypothesesContainBackgroundRegularity : ∀ index →
      ExactPropagatorHypotheses index →
      BackgroundSatisfiesRegularity35 index
    hypothesesContainMThreshold : ∀ index →
      ExactPropagatorHypotheses index → MAtLeastM1 index
    hypothesesContainSmallness : ∀ index →
      ExactPropagatorHypotheses index → MEpsilon0BelowA0 index
    hypothesesContainBetaRange : ∀ index →
      ExactPropagatorHypotheses index → BetaInAdmissibleRange index

    -- Operators and norms.  `greenPrime` is Theorem 3.1; `green` is Theorem
    -- 3.3.  The repository completion lane consumes the latter.
    greenPrime green gradientGreen secondGradientGreen :
      Index → Source → State
    sourceNorm stateNorm : Source → Bound
    propagatedStateNorm : State → Bound
    multiply : Bound → Bound → Bound
    CG CGradG CSecondG : Bound

    theorem31GreenPrimeBound : ∀ index source →
      ExactPropagatorHypotheses index →
      LessEqual (propagatedStateNorm (greenPrime index source))
        (multiply CG (sourceNorm source))

    theorem33GreenBound : ∀ index source →
      ExactPropagatorHypotheses index →
      LessEqual (propagatedStateNorm (green index source))
        (multiply CG (sourceNorm source))

    theorem33GradientGreenBound : ∀ index source →
      ExactPropagatorHypotheses index →
      LessEqual (propagatedStateNorm (gradientGreen index source))
        (multiply CGradG (sourceNorm source))

    theorem33SecondGradientGreenBound : ∀ index source →
      ExactPropagatorHypotheses index →
      LessEqual (propagatedStateNorm (secondGradientGreen index source))
        (multiply CSecondG (sourceNorm source))

    greenKernel gradientKernel secondGradientKernel : Index → Kernel
    KernelExponentialDecay : Kernel → Set

    theorem33GreenKernelDecay : ∀ index →
      ExactPropagatorHypotheses index →
      KernelExponentialDecay (greenKernel index)
    theorem33GradientKernelDecay : ∀ index →
      ExactPropagatorHypotheses index →
      KernelExponentialDecay (gradientKernel index)
    theorem33SecondGradientKernelDecay : ∀ index →
      ExactPropagatorHypotheses index →
      KernelExponentialDecay (secondGradientKernel index)

    GaugeCovariant : (Index → Source → State) → Set
    theorem33GaugeCovariance : GaugeCovariant green

    AnalyticInBackground : (Index → Source → State) → Set
    publishedBackgroundAnalyticity : AnalyticInBackground green
    publishedGradientBackgroundAnalyticity :
      AnalyticInBackground gradientGreen
    publishedSecondGradientBackgroundAnalyticity :
      AnalyticInBackground secondGradientGreen

open PublishedPropagatorTheorems31And33 public

propagatorTheorems31And33ToAuthority :
  ∀ {Index Source State Bound Kernel} →
  PublishedPropagatorTheorems31And33 Index Source State Bound Kernel →
  PublishedBackgroundPropagatorAuthority Index Source State Bound
propagatorTheorems31And33ToAuthority source = record
  { RegularBackground = ExactPropagatorHypotheses source
  ; green = green source
  ; gradientGreen = gradientGreen source
  ; secondGradientGreen = secondGradientGreen source
  ; sourceNorm = sourceNorm source
  ; stateNorm = propagatedStateNorm source
  ; multiply = multiply source
  ; LessEqual = LessEqual source
  ; CG = CG source
  ; CGradG = CGradG source
  ; CSecondG = CSecondG source
  ; theorem31GreenBound = theorem33GreenBound source
  ; theorem31GradientGreenBound = theorem33GradientGreenBound source
  ; theorem31SecondGradientGreenBound = theorem33SecondGradientGreenBound source
  ; Kernel = _
  ; greenKernel = greenKernel source
  ; gradientKernel = gradientKernel source
  ; secondGradientKernel = secondGradientKernel source
  ; KernelExponentialDecay = KernelExponentialDecay source
  ; theorem31GreenKernelDecay = theorem33GreenKernelDecay source
  ; theorem31GradientKernelDecay = theorem33GradientKernelDecay source
  ; theorem31SecondGradientKernelDecay = theorem33SecondGradientKernelDecay source
  ; GaugeCovariant = GaugeCovariant source
  ; theorem31GaugeCovariance = theorem33GaugeCovariance source
  ; AnalyticInBackground = AnalyticInBackground source
  ; theorem34GreenAnalytic = publishedBackgroundAnalyticity source
  ; theorem34GradientGreenAnalytic = publishedGradientBackgroundAnalyticity source
  ; theorem34SecondGradientGreenAnalytic =
      publishedSecondGradientBackgroundAnalyticity source
  }

------------------------------------------------------------------------
-- Variational Theorem 1.
------------------------------------------------------------------------

record PublishedVariationalTheorem1Exact
    (Index Coarse Fluctuation Bound : Set) : Set₁ where
  field
    epsilon0 epsilon1 a0 a1 B3 : Bound
    LessEqual StrictLess : Bound → Bound → Set

    NestedDomainGeometry : Index → Set
    CoarseRegularityCondition7 : Index → Coarse → Set
    Epsilon1BelowA1 : Set
    B3Epsilon1BelowEpsilon0 : Set
    Epsilon0BelowA0 : Set

    ExactVariationalHypotheses : Index → Coarse → Set
    hypothesesContainNestedGeometry : ∀ index coarse →
      ExactVariationalHypotheses index coarse → NestedDomainGeometry index
    hypothesesContainCoarseRegularity : ∀ index coarse →
      ExactVariationalHypotheses index coarse →
      CoarseRegularityCondition7 index coarse

    backgroundFluctuation : Index → Coarse → Fluctuation
    Critical Minimizer : Index → Coarse → Fluctuation → Set
    GaugeEquivalent : Fluctuation → Fluctuation → Set

    theorem1BackgroundCritical : ∀ index coarse →
      ExactVariationalHypotheses index coarse →
      Critical index coarse (backgroundFluctuation index coarse)

    theorem1BackgroundMinimizes : ∀ index coarse →
      ExactVariationalHypotheses index coarse →
      Minimizer index coarse (backgroundFluctuation index coarse)

    theorem1BackgroundUniqueModuloGauge : ∀ index coarse fluctuation →
      ExactVariationalHypotheses index coarse →
      Critical index coarse fluctuation →
      GaugeEquivalent fluctuation (backgroundFluctuation index coarse)

    AnalyticBackgroundMap ExponentiallyLocalBackgroundMap
      BackgroundDerivativeExponentiallyDecays : Set
    theorem1BackgroundAnalytic : AnalyticBackgroundMap
    theorem1BackgroundExponentiallyLocal : ExponentiallyLocalBackgroundMap
    theorem1BackgroundDerivativeDecay :
      BackgroundDerivativeExponentiallyDecays

    norm : Fluctuation → Bound
    radius : Bound
    backgroundInsideUniformRadius : ∀ index coarse →
      ExactVariationalHypotheses index coarse →
      LessEqual (norm (backgroundFluctuation index coarse)) radius

open PublishedVariationalTheorem1Exact public

variationalTheorem1ToAuthority :
  ∀ {Index Coarse Fluctuation Bound} →
  PublishedVariationalTheorem1Exact Index Coarse Fluctuation Bound →
  PublishedVariationalBackgroundAuthority Index Coarse Fluctuation Bound
variationalTheorem1ToAuthority source = record
  { AdmissibleCoarseField = ExactVariationalHypotheses source
  ; backgroundFluctuation = backgroundFluctuation source
  ; Critical = Critical source
  ; Minimizer = Minimizer source
  ; GaugeEquivalent = GaugeEquivalent source
  ; theorem1BackgroundCritical = theorem1BackgroundCritical source
  ; theorem1BackgroundMinimizes = theorem1BackgroundMinimizes source
  ; theorem1BackgroundUniqueModuloGauge =
      theorem1BackgroundUniqueModuloGauge source
  ; AnalyticBackgroundMap = AnalyticBackgroundMap source
  ; ExponentiallyLocalBackgroundMap = ExponentiallyLocalBackgroundMap source
  ; BackgroundDerivativeExponentiallyDecays =
      BackgroundDerivativeExponentiallyDecays source
  ; backgroundAnalytic = theorem1BackgroundAnalytic source
  ; backgroundExponentiallyLocal = theorem1BackgroundExponentiallyLocal source
  ; backgroundDerivativeDecay = theorem1BackgroundDerivativeDecay source
  ; norm = norm source
  ; radius = radius source
  ; LessEqual = LessEqual source
  ; backgroundInsideUniformRadius = backgroundInsideUniformRadius source
  }

------------------------------------------------------------------------
-- Four-dimensional small-field RG Theorems 1 and 3.
------------------------------------------------------------------------

record PublishedSmallFieldTheorems1And3Exact
    (Scale Coupling EffectiveAction Bound : Set) : Set₁ where
  field
    coupling : Scale → Coupling
    gamma : Bound
    absCoupling : Coupling → Bound
    LessEqual StrictLess : Bound → Bound → Set

    DimensionIsFour : Set
    GaugeGroupCompactSemisimpleSubgroupOfUnitary : Set
    RenormalizationTransformationsAreSmallField : Set
    EffectiveCouplingsInZeroGamma : Set

    couplingPositive : ∀ scale → Set
    couplingBelowGamma : ∀ scale →
      LessEqual (absCoupling (coupling scale)) gamma

    effectiveAction : Scale → EffectiveAction
    InductiveAssumptions11Through122 : Scale → EffectiveAction → Set

    theorem3InductiveControl : ∀ scale →
      InductiveAssumptions11Through122 scale (effectiveAction scale)

open PublishedSmallFieldTheorems1And3Exact public

smallFieldTheorems1And3ToAuthority :
  ∀ {Scale Coupling EffectiveAction Bound} →
  PublishedSmallFieldTheorems1And3Exact
    Scale Coupling EffectiveAction Bound →
  PublishedSmallFieldRGAuthority Scale Coupling EffectiveAction Bound
smallFieldTheorems1And3ToAuthority source = record
  { coupling = coupling source
  ; smallCouplingThreshold = gamma source
  ; absCoupling = absCoupling source
  ; LessEqual = LessEqual source
  ; RunningCouplingsRemainSmall = EffectiveCouplingsInZeroGamma source
  ; runningCouplingsRemainSmall = EffectiveCouplingsInZeroGamma source
  ; couplingBelowThreshold = couplingBelowGamma source
  ; effectiveAction = effectiveAction source
  ; SmallFieldEffectiveActionControlled =
      InductiveAssumptions11Through122 source
  ; theorem1And3SmallFieldControl = theorem3InductiveControl source
  }

publishedSourceTheoremStatementLevel : ProofLevel
publishedSourceTheoremStatementLevel = standardImported

publishedSourceAuthorityConversionLevel : ProofLevel
publishedSourceAuthorityConversionLevel = machineChecked
