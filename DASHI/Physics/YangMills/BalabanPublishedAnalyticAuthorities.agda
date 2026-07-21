module DASHI.Physics.YangMills.BalabanPublishedAnalyticAuthorities where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Source-faithful external theorem boundaries.
--
-- This module does not treat a citation as an Agda proof.  It records the exact
-- mathematical conclusions that may legitimately be imported from the published
-- Bałaban propagator, variational-background and small-field RG papers, while
-- keeping the four-dimensional running-coupling, continuum OS and mass-gap
-- conclusions outside that imported boundary.
--
-- Propagator source: T. Bałaban, "Propagators for lattice gauge theories in a
-- background field", CMP 99 (1985), Theorems 3.1--3.4.
-- Variational source: T. Bałaban, "The variational problem and background fields
-- in renormalization group method for lattice gauge theories", CMP 102 (1985),
-- Theorem 1 and its contraction/locality proof.
-- Small-field RG source: T. Bałaban, "Renormalization group approach to lattice
-- gauge field theories", CMP 109 (1987), Theorems 1 and 3.  Its four-dimensional
-- running-coupling Theorem 2 explicitly defers the perturbative proof to another
-- paper, so it is not imported here as a completed authority.
------------------------------------------------------------------------

record PublishedBackgroundPropagatorAuthority
    (Index Source State Bound : Set) : Set₁ where
  field
    RegularBackground : Index → Set

    green gradientGreen secondGradientGreen : Index → Source → State
    sourceNorm : Source → Bound
    stateNorm : State → Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    CG CGradG CSecondG : Bound

    -- Global weighted bounds corresponding to the local and global estimates in
    -- Theorems 3.1 and 3.3.  One constant family works for every admissible
    -- localization-domain sequence satisfying the source hypotheses.
    theorem31GreenBound : ∀ index source →
      RegularBackground index →
      LessEqual (stateNorm (green index source))
        (multiply CG (sourceNorm source))

    theorem31GradientGreenBound : ∀ index source →
      RegularBackground index →
      LessEqual (stateNorm (gradientGreen index source))
        (multiply CGradG (sourceNorm source))

    theorem31SecondGradientGreenBound : ∀ index source →
      RegularBackground index →
      LessEqual (stateNorm (secondGradientGreen index source))
        (multiply CSecondG (sourceNorm source))

    Kernel : Set
    greenKernel gradientKernel secondGradientKernel : Index → Kernel

    KernelExponentialDecay : Kernel → Set
    theorem31GreenKernelDecay : ∀ index →
      RegularBackground index →
      KernelExponentialDecay (greenKernel index)
    theorem31GradientKernelDecay : ∀ index →
      RegularBackground index →
      KernelExponentialDecay (gradientKernel index)
    theorem31SecondGradientKernelDecay : ∀ index →
      RegularBackground index →
      KernelExponentialDecay (secondGradientKernel index)

    GaugeCovariant : (Index → Source → State) → Set
    theorem31GaugeCovariance : GaugeCovariant green

    AnalyticInBackground : (Index → Source → State) → Set
    theorem34GreenAnalytic : AnalyticInBackground green
    theorem34GradientGreenAnalytic : AnalyticInBackground gradientGreen
    theorem34SecondGradientGreenAnalytic :
      AnalyticInBackground secondGradientGreen

open PublishedBackgroundPropagatorAuthority public

record PublishedVariationalBackgroundAuthority
    (Index Coarse Fluctuation Bound : Set) : Set₁ where
  field
    AdmissibleCoarseField : Index → Coarse → Set
    backgroundFluctuation : Index → Coarse → Fluctuation

    Critical : Index → Coarse → Fluctuation → Set
    Minimizer : Index → Coarse → Fluctuation → Set
    GaugeEquivalent : Fluctuation → Fluctuation → Set

    theorem1BackgroundCritical : ∀ index coarse →
      AdmissibleCoarseField index coarse →
      Critical index coarse (backgroundFluctuation index coarse)

    theorem1BackgroundMinimizes : ∀ index coarse →
      AdmissibleCoarseField index coarse →
      Minimizer index coarse (backgroundFluctuation index coarse)

    theorem1BackgroundUniqueModuloGauge : ∀ index coarse fluctuation →
      AdmissibleCoarseField index coarse →
      Critical index coarse fluctuation →
      GaugeEquivalent fluctuation (backgroundFluctuation index coarse)

    AnalyticBackgroundMap : Set
    ExponentiallyLocalBackgroundMap : Set
    BackgroundDerivativeExponentiallyDecays : Set

    backgroundAnalytic : AnalyticBackgroundMap
    backgroundExponentiallyLocal : ExponentiallyLocalBackgroundMap
    backgroundDerivativeDecay : BackgroundDerivativeExponentiallyDecays

    norm : Fluctuation → Bound
    radius : Bound
    LessEqual : Bound → Bound → Set
    backgroundInsideUniformRadius : ∀ index coarse →
      AdmissibleCoarseField index coarse →
      LessEqual (norm (backgroundFluctuation index coarse)) radius

open PublishedVariationalBackgroundAuthority public

record PublishedSmallFieldRGAuthority
    (Scale Coupling EffectiveAction Bound : Set) : Set₁ where
  field
    coupling : Scale → Coupling
    smallCouplingThreshold : Bound
    absCoupling : Coupling → Bound
    LessEqual : Bound → Bound → Set
    RunningCouplingsRemainSmall : Set

    runningCouplingsRemainSmall : RunningCouplingsRemainSmall
    couplingBelowThreshold : ∀ scale →
      LessEqual (absCoupling (coupling scale)) smallCouplingThreshold

    effectiveAction : Scale → EffectiveAction
    SmallFieldEffectiveActionControlled : Scale → EffectiveAction → Set

    -- Theorems 1 and 3: conditional on the running couplings remaining in a fixed
    -- sufficiently small interval, every small-field effective action has the
    -- stated localized representation and uniform irrelevant-term bounds.
    theorem1And3SmallFieldControl : ∀ scale →
      SmallFieldEffectiveActionControlled scale (effectiveAction scale)

open PublishedSmallFieldRGAuthority public

------------------------------------------------------------------------
-- What the historical sources do and do not discharge.
------------------------------------------------------------------------

publishedBackgroundPropagatorLevel : ProofLevel
publishedBackgroundPropagatorLevel = standardImported

publishedVariationalBackgroundLevel : ProofLevel
publishedVariationalBackgroundLevel = standardImported

publishedSmallFieldRGConditionalLevel : ProofLevel
publishedSmallFieldRGConditionalLevel = standardImported

-- The published small-field theorem assumes the complete four-dimensional
-- running-coupling sequence remains small.  Supplying that sequence uniformly,
-- together with the large-field, continuum OS and positive-gap limits required by
-- the Clay problem, is not discharged merely by importing the theorems above.

fourDimensionalRunningCouplingClosureLevel : ProofLevel
fourDimensionalRunningCouplingClosureLevel = conditional

largeFieldAllScaleClosureLevel : ProofLevel
largeFieldAllScaleClosureLevel = conditional

continuumOSUniquenessAndInteractionLevel : ProofLevel
continuumOSUniquenessAndInteractionLevel = conjectural

uniformPhysicalMassGapProductionLevel : ProofLevel
uniformPhysicalMassGapProductionLevel = conjectural
