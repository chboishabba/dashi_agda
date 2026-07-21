module DASHI.Physics.YangMills.BalabanExactPublishedCarrierMatching where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPublishedAnalyticAuthorities

------------------------------------------------------------------------
-- Exact definition and hypothesis matching for the published Bałaban
-- propagator, variational-background and small-field RG authorities.
--
-- The earlier adapter layer only required an admissibility implication.  This
-- module records the concrete equalities that must be checked before a source
-- theorem may be applied to the repository carrier.  The analytic conclusions
-- are transported by rewriting; no duplicate estimate or replacement
-- assumption is introduced here.
------------------------------------------------------------------------

record ExactPropagatorCarrierMatch
    {Index Source State Bound Lattice BondField GaugeAction Operator
      PatchGeometry : Set}
    (authority : PublishedBackgroundPropagatorAuthority
      Index Source State Bound)
    (RepositoryAdmissible : Index → Set) : Set₁ where
  field
    dashiPeriodicLattice balabanPeriodicLattice : Index → Lattice
    dashiPeriodicLatticeMatchesBalabanLattice : ∀ index →
      dashiPeriodicLattice index ≡ balabanPeriodicLattice index

    dashiBondField balabanOneForm : Index → BondField
    dashiBondFieldMatchesBalabanOneForm : ∀ index →
      dashiBondField index ≡ balabanOneForm index

    dashiGaugeAction balabanGaugeAction : GaugeAction
    dashiGaugeActionMatchesBalabanGaugeAction :
      dashiGaugeAction ≡ balabanGaugeAction

    dashiReferenceOperator balabanReferenceOperator : Index → Operator
    dashiReferenceOperatorMatchesBalabanOperator : ∀ index →
      dashiReferenceOperator index ≡ balabanReferenceOperator index

    dashiFullHessian balabanBackgroundHessian : Index → Operator
    dashiFullHessianMatchesBalabanBackgroundHessian : ∀ index →
      dashiFullHessian index ≡ balabanBackgroundHessian index

    repositoryGreen repositoryGradientGreen repositorySecondGradientGreen :
      Index → Source → State

    dashiGreenMatchesBalabanPropagator : ∀ index source →
      repositoryGreen index source ≡ green authority index source
    dashiGradientGreenMatchesBalabanGradientPropagator : ∀ index source →
      repositoryGradientGreen index source ≡
        gradientGreen authority index source
    dashiSecondGradientGreenMatchesBalabanSecondGradientPropagator :
      ∀ index source →
      repositorySecondGradientGreen index source ≡
        secondGradientGreen authority index source

    repositorySourceNorm : Source → Bound
    repositoryStateNorm : State → Bound

    dashiWeightedNormMatchesBalabanWeightedNorm : ∀ source →
      repositorySourceNorm source ≡ sourceNorm authority source
    dashiDerivativeNormMatchesBalabanDerivativeNorm : ∀ state →
      repositoryStateNorm state ≡ stateNorm authority state
    dashiSecondDerivativeNormMatchesBalabanSecondDerivativeNorm : ∀ state →
      repositoryStateNorm state ≡ stateNorm authority state

    dashiPatchGeometry balabanPatchGeometry : Index → PatchGeometry
    dashiPatchGeometryImpliesBalabanDomainHypotheses : ∀ index →
      RepositoryAdmissible index →
      dashiPatchGeometry index ≡ balabanPatchGeometry index

    dashiSmallFieldImpliesBalabanSmallField : ∀ index →
      RepositoryAdmissible index → RegularBackground authority index

open ExactPropagatorCarrierMatch public

record RepositoryUniformPropagatorCertificate
    (Index Source State Bound : Set) : Set₁ where
  field
    RepositoryAdmissible : Index → Set
    green gradientGreen secondGradientGreen : Index → Source → State
    sourceNorm : Source → Bound
    stateNorm : State → Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    CG CGradG CSecondG : Bound

    greenBound : ∀ index source →
      RepositoryAdmissible index →
      LessEqual (stateNorm (green index source))
        (multiply CG (sourceNorm source))

    gradientGreenBound : ∀ index source →
      RepositoryAdmissible index →
      LessEqual (stateNorm (gradientGreen index source))
        (multiply CGradG (sourceNorm source))

    secondGradientGreenBound : ∀ index source →
      RepositoryAdmissible index →
      LessEqual (stateNorm (secondGradientGreen index source))
        (multiply CSecondG (sourceNorm source))

open RepositoryUniformPropagatorCertificate public

publishedPropagatorAppliesToDashi :
  ∀ {Index Source State Bound Lattice BondField GaugeAction Operator
      PatchGeometry}
  (authority : PublishedBackgroundPropagatorAuthority
    Index Source State Bound)
  (RepositoryAdmissible : Index → Set) →
  ExactPropagatorCarrierMatch
    {Lattice = Lattice}
    {BondField = BondField}
    {GaugeAction = GaugeAction}
    {Operator = Operator}
    {PatchGeometry = PatchGeometry}
    authority RepositoryAdmissible →
  RepositoryUniformPropagatorCertificate Index Source State Bound
publishedPropagatorAppliesToDashi authority RepositoryAdmissible match = record
  { RepositoryAdmissible = RepositoryAdmissible
  ; green = repositoryGreen match
  ; gradientGreen = repositoryGradientGreen match
  ; secondGradientGreen = repositorySecondGradientGreen match
  ; sourceNorm = repositorySourceNorm match
  ; stateNorm = repositoryStateNorm match
  ; multiply = multiply authority
  ; LessEqual = LessEqual authority
  ; CG = CG authority
  ; CGradG = CGradG authority
  ; CSecondG = CSecondG authority
  ; greenBound = λ index source admissible →
      transportGreen index source admissible
  ; gradientGreenBound = λ index source admissible →
      transportGradient index source admissible
  ; secondGradientGreenBound = λ index source admissible →
      transportSecondGradient index source admissible
  }
  where
    transportGreen : ∀ index source → RepositoryAdmissible index →
      LessEqual authority
        (repositoryStateNorm match (repositoryGreen match index source))
        (multiply authority (CG authority) (repositorySourceNorm match source))
    transportGreen index source admissible
      rewrite dashiGreenMatchesBalabanPropagator match index source
            | dashiDerivativeNormMatchesBalabanDerivativeNorm match
                (green authority index source)
            | dashiWeightedNormMatchesBalabanWeightedNorm match source =
      theorem31GreenBound authority index source
        (dashiSmallFieldImpliesBalabanSmallField match index admissible)

    transportGradient : ∀ index source → RepositoryAdmissible index →
      LessEqual authority
        (repositoryStateNorm match
          (repositoryGradientGreen match index source))
        (multiply authority (CGradG authority)
          (repositorySourceNorm match source))
    transportGradient index source admissible
      rewrite dashiGradientGreenMatchesBalabanGradientPropagator match
                index source
            | dashiDerivativeNormMatchesBalabanDerivativeNorm match
                (gradientGreen authority index source)
            | dashiWeightedNormMatchesBalabanWeightedNorm match source =
      theorem31GradientGreenBound authority index source
        (dashiSmallFieldImpliesBalabanSmallField match index admissible)

    transportSecondGradient : ∀ index source → RepositoryAdmissible index →
      LessEqual authority
        (repositoryStateNorm match
          (repositorySecondGradientGreen match index source))
        (multiply authority (CSecondG authority)
          (repositorySourceNorm match source))
    transportSecondGradient index source admissible
      rewrite dashiSecondGradientGreenMatchesBalabanSecondGradientPropagator
                match index source
            | dashiSecondDerivativeNormMatchesBalabanSecondDerivativeNorm match
                (secondGradientGreen authority index source)
            | dashiWeightedNormMatchesBalabanWeightedNorm match source =
      theorem31SecondGradientGreenBound authority index source
        (dashiSmallFieldImpliesBalabanSmallField match index admissible)

------------------------------------------------------------------------
-- Exact variational-background matching.
------------------------------------------------------------------------

record ExactVariationalCarrierMatch
    {Index Coarse Fluctuation Bound BackgroundMap RGCoordinates : Set}
    (authority : PublishedVariationalBackgroundAuthority
      Index Coarse Fluctuation Bound)
    (RepositoryAdmissible : Index → Coarse → Set)
    (RepositoryCritical RepositoryMinimizer :
      Index → Coarse → Fluctuation → Set)
    (RepositoryGaugeEquivalent : Fluctuation → Fluctuation → Set) : Set₁ where
  field
    dashiBackgroundMap balabanVariationalBackgroundMap : BackgroundMap
    dashiBackgroundMapMatchesBalabanVariationalBackground :
      dashiBackgroundMap ≡ balabanVariationalBackgroundMap

    dashiRGCoordinates balabanRGCoordinates : RGCoordinates
    dashiRGCoordinatesMatchBalabanRGCoordinates :
      dashiRGCoordinates ≡ balabanRGCoordinates

    repositoryBackgroundFluctuation : Index → Coarse → Fluctuation
    dashiBackgroundFluctuationMatchesPublished : ∀ index coarse →
      repositoryBackgroundFluctuation index coarse ≡
        backgroundFluctuation authority index coarse

    dashiAdmissibleImpliesBalabanAdmissible : ∀ index coarse →
      RepositoryAdmissible index coarse →
      AdmissibleCoarseField authority index coarse

    publishedCriticalImpliesRepositoryCritical : ∀ index coarse fluctuation →
      Critical authority index coarse fluctuation →
      RepositoryCritical index coarse fluctuation

    publishedMinimizerImpliesRepositoryMinimizer : ∀ index coarse fluctuation →
      Minimizer authority index coarse fluctuation →
      RepositoryMinimizer index coarse fluctuation

    publishedGaugeEquivalentImpliesRepositoryGaugeEquivalent :
      ∀ left right →
      GaugeEquivalent authority left right →
      RepositoryGaugeEquivalent left right

open ExactVariationalCarrierMatch public

record RepositoryFiniteBackgroundCertificate
    (Index Coarse Fluctuation : Set) : Set₁ where
  field
    RepositoryAdmissible : Index → Coarse → Set
    backgroundFluctuation : Index → Coarse → Fluctuation
    Critical : Index → Coarse → Fluctuation → Set
    Minimizer : Index → Coarse → Fluctuation → Set
    GaugeEquivalent : Fluctuation → Fluctuation → Set

    backgroundCritical : ∀ index coarse →
      RepositoryAdmissible index coarse →
      Critical index coarse (backgroundFluctuation index coarse)

    backgroundMinimizes : ∀ index coarse →
      RepositoryAdmissible index coarse →
      Minimizer index coarse (backgroundFluctuation index coarse)

    backgroundUniqueModuloGauge : ∀ index coarse fluctuation →
      RepositoryAdmissible index coarse →
      Critical index coarse fluctuation →
      GaugeEquivalent fluctuation (backgroundFluctuation index coarse)

open RepositoryFiniteBackgroundCertificate public

publishedVariationalBackgroundAppliesToDashi :
  ∀ {Index Coarse Fluctuation Bound BackgroundMap RGCoordinates}
  (authority : PublishedVariationalBackgroundAuthority
    Index Coarse Fluctuation Bound)
  (RepositoryAdmissible : Index → Coarse → Set)
  (RepositoryCritical RepositoryMinimizer :
    Index → Coarse → Fluctuation → Set)
  (RepositoryGaugeEquivalent : Fluctuation → Fluctuation → Set) →
  ExactVariationalCarrierMatch
    {BackgroundMap = BackgroundMap}
    {RGCoordinates = RGCoordinates}
    authority RepositoryAdmissible RepositoryCritical RepositoryMinimizer
      RepositoryGaugeEquivalent →
  RepositoryFiniteBackgroundCertificate Index Coarse Fluctuation
publishedVariationalBackgroundAppliesToDashi authority RepositoryAdmissible
    RepositoryCritical RepositoryMinimizer RepositoryGaugeEquivalent match = record
  { RepositoryAdmissible = RepositoryAdmissible
  ; backgroundFluctuation = repositoryBackgroundFluctuation match
  ; Critical = RepositoryCritical
  ; Minimizer = RepositoryMinimizer
  ; GaugeEquivalent = RepositoryGaugeEquivalent
  ; backgroundCritical = λ index coarse admissible →
      transportCritical index coarse admissible
  ; backgroundMinimizes = λ index coarse admissible →
      transportMinimizer index coarse admissible
  ; backgroundUniqueModuloGauge = λ index coarse fluctuation admissible critical →
      transportUnique index coarse fluctuation admissible critical
  }
  where
    transportCritical : ∀ index coarse → RepositoryAdmissible index coarse →
      RepositoryCritical index coarse
        (repositoryBackgroundFluctuation match index coarse)
    transportCritical index coarse admissible
      rewrite dashiBackgroundFluctuationMatchesPublished match index coarse =
      publishedCriticalImpliesRepositoryCritical match index coarse
        (backgroundFluctuation authority index coarse)
        (theorem1BackgroundCritical authority index coarse
          (dashiAdmissibleImpliesBalabanAdmissible match index coarse admissible))

    transportMinimizer : ∀ index coarse → RepositoryAdmissible index coarse →
      RepositoryMinimizer index coarse
        (repositoryBackgroundFluctuation match index coarse)
    transportMinimizer index coarse admissible
      rewrite dashiBackgroundFluctuationMatchesPublished match index coarse =
      publishedMinimizerImpliesRepositoryMinimizer match index coarse
        (backgroundFluctuation authority index coarse)
        (theorem1BackgroundMinimizes authority index coarse
          (dashiAdmissibleImpliesBalabanAdmissible match index coarse admissible))

    transportUnique : ∀ index coarse fluctuation →
      RepositoryAdmissible index coarse →
      RepositoryCritical index coarse fluctuation →
      RepositoryGaugeEquivalent fluctuation
        (repositoryBackgroundFluctuation match index coarse)
    transportUnique index coarse fluctuation admissible repositoryCritical
      rewrite dashiBackgroundFluctuationMatchesPublished match index coarse =
      publishedGaugeEquivalentImpliesRepositoryGaugeEquivalent match
        fluctuation (backgroundFluctuation authority index coarse)
        (theorem1BackgroundUniqueModuloGauge authority index coarse fluctuation
          (dashiAdmissibleImpliesBalabanAdmissible match index coarse admissible)
          (repositoryCriticalImpliesPublished index coarse fluctuation
            repositoryCritical))

    -- Uniqueness requires the repository critical predicate to imply the exact
    -- published critical equation as well as the forward transport used above.
    -- This converse is intentionally exposed as the sole additional obligation
    -- of the uniqueness lane.
    repositoryCriticalImpliesPublished : ∀ index coarse fluctuation →
      RepositoryCritical index coarse fluctuation →
      Critical authority index coarse fluctuation
    repositoryCriticalImpliesPublished =
      repositoryCriticalImpliesPublishedCritical match

------------------------------------------------------------------------
-- The converse critical-equation match is split out so the main record remains
-- usable for existence/minimization even when uniqueness is not yet transported.
------------------------------------------------------------------------

record ExactVariationalCriticalConverse
    {Index Coarse Fluctuation Bound BackgroundMap RGCoordinates : Set}
    {authority : PublishedVariationalBackgroundAuthority
      Index Coarse Fluctuation Bound}
    {RepositoryAdmissible : Index → Coarse → Set}
    {RepositoryCritical RepositoryMinimizer :
      Index → Coarse → Fluctuation → Set}
    {RepositoryGaugeEquivalent : Fluctuation → Fluctuation → Set}
    (match : ExactVariationalCarrierMatch
      {BackgroundMap = BackgroundMap}
      {RGCoordinates = RGCoordinates}
      authority RepositoryAdmissible RepositoryCritical RepositoryMinimizer
        RepositoryGaugeEquivalent) : Set₁ where
  field
    repositoryCriticalImpliesPublishedCritical : ∀ index coarse fluctuation →
      RepositoryCritical index coarse fluctuation →
      Critical authority index coarse fluctuation

open ExactVariationalCriticalConverse public

------------------------------------------------------------------------
-- Exact small-field RG matching.
------------------------------------------------------------------------

record ExactSmallFieldRGCarrierMatch
    {Scale Coupling EffectiveAction Bound RGCoordinates : Set}
    (authority : PublishedSmallFieldRGAuthority
      Scale Coupling EffectiveAction Bound)
    (RepositorySmallFieldControl : Scale → EffectiveAction → Set) : Set₁ where
  field
    dashiRGCoordinates balabanRGCoordinates : RGCoordinates
    dashiRGCoordinatesMatchBalabanRGCoordinates :
      dashiRGCoordinates ≡ balabanRGCoordinates

    repositoryEffectiveAction : Scale → EffectiveAction
    repositoryEffectiveActionMatchesPublished : ∀ scale →
      repositoryEffectiveAction scale ≡ effectiveAction authority scale

    publishedControlImpliesRepositoryControl : ∀ scale action →
      SmallFieldEffectiveActionControlled authority scale action →
      RepositorySmallFieldControl scale action

open ExactSmallFieldRGCarrierMatch public

publishedSmallFieldRGAppliesToDashi :
  ∀ {Scale Coupling EffectiveAction Bound RGCoordinates}
  (authority : PublishedSmallFieldRGAuthority
    Scale Coupling EffectiveAction Bound)
  (RepositorySmallFieldControl : Scale → EffectiveAction → Set) →
  ExactSmallFieldRGCarrierMatch
    {RGCoordinates = RGCoordinates}
    authority RepositorySmallFieldControl →
  ∀ scale →
  RepositorySmallFieldControl scale
    (repositoryEffectiveAction _)
publishedSmallFieldRGAppliesToDashi authority RepositorySmallFieldControl
    match scale
  rewrite repositoryEffectiveActionMatchesPublished match scale =
  publishedControlImpliesRepositoryControl match scale
    (effectiveAction authority scale)
    (theorem1And3SmallFieldControl authority scale)

exactPublishedCarrierAdapterAssemblyLevel : ProofLevel
exactPublishedCarrierAdapterAssemblyLevel = machineChecked

exactPublishedCarrierMatchingLevel : ProofLevel
exactPublishedCarrierMatchingLevel = conditional
