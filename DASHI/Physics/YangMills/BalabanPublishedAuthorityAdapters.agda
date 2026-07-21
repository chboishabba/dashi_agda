module DASHI.Physics.YangMills.BalabanPublishedAuthorityAdapters where

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPublishedAnalyticAuthorities

------------------------------------------------------------------------
-- Machine-checked adapters from published theorem packages to the exact carrier
-- selected by the repository.  The only remaining obligations in this lane are
-- the definition/hypothesis matching proofs; the analytic estimates themselves
-- are not duplicated as fresh conditional fields.
------------------------------------------------------------------------

record PropagatorCarrierMatch
    {Index Source State Bound : Set}
    (authority : PublishedBackgroundPropagatorAuthority
      Index Source State Bound)
    (AdmissibleIndex : Index → Set) : Set₁ where
  field
    admissibleImpliesPublishedRegular : ∀ index →
      AdmissibleIndex index → RegularBackground authority index

open PropagatorCarrierMatch public

record UniformPropagatorCertificate
    (Index Source State Bound : Set) : Set₁ where
  field
    AdmissibleIndex : Index → Set
    green gradientGreen secondGradientGreen : Index → Source → State
    sourceNorm : Source → Bound
    stateNorm : State → Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    CG CGradG CSecondG : Bound

    greenBound : ∀ index source →
      AdmissibleIndex index →
      LessEqual (stateNorm (green index source))
        (multiply CG (sourceNorm source))

    gradientGreenBound : ∀ index source →
      AdmissibleIndex index →
      LessEqual (stateNorm (gradientGreen index source))
        (multiply CGradG (sourceNorm source))

    secondGradientGreenBound : ∀ index source →
      AdmissibleIndex index →
      LessEqual (stateNorm (secondGradientGreen index source))
        (multiply CSecondG (sourceNorm source))

open UniformPropagatorCertificate public

publishedPropagatorCertificate :
  ∀ {Index Source State Bound}
  (authority : PublishedBackgroundPropagatorAuthority
    Index Source State Bound)
  (AdmissibleIndex : Index → Set) →
  PropagatorCarrierMatch authority AdmissibleIndex →
  UniformPropagatorCertificate Index Source State Bound
publishedPropagatorCertificate authority AdmissibleIndex match = record
  { AdmissibleIndex = AdmissibleIndex
  ; green = green authority
  ; gradientGreen = gradientGreen authority
  ; secondGradientGreen = secondGradientGreen authority
  ; sourceNorm = sourceNorm authority
  ; stateNorm = stateNorm authority
  ; multiply = multiply authority
  ; LessEqual = LessEqual authority
  ; CG = CG authority
  ; CGradG = CGradG authority
  ; CSecondG = CSecondG authority
  ; greenBound = λ index source admissible →
      theorem31GreenBound authority index source
        (admissibleImpliesPublishedRegular match index admissible)
  ; gradientGreenBound = λ index source admissible →
      theorem31GradientGreenBound authority index source
        (admissibleImpliesPublishedRegular match index admissible)
  ; secondGradientGreenBound = λ index source admissible →
      theorem31SecondGradientGreenBound authority index source
        (admissibleImpliesPublishedRegular match index admissible)
  }

record VariationalCarrierMatch
    {Index Coarse Fluctuation Bound : Set}
    (authority : PublishedVariationalBackgroundAuthority
      Index Coarse Fluctuation Bound)
    (RepositoryAdmissible : Index → Coarse → Set) : Set₁ where
  field
    repositoryAdmissibleImpliesPublishedAdmissible : ∀ index coarse →
      RepositoryAdmissible index coarse →
      AdmissibleCoarseField authority index coarse

open VariationalCarrierMatch public

record FiniteBackgroundCertificate
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

open FiniteBackgroundCertificate public

publishedFiniteBackgroundCertificate :
  ∀ {Index Coarse Fluctuation Bound}
  (authority : PublishedVariationalBackgroundAuthority
    Index Coarse Fluctuation Bound)
  (RepositoryAdmissible : Index → Coarse → Set) →
  VariationalCarrierMatch authority RepositoryAdmissible →
  FiniteBackgroundCertificate Index Coarse Fluctuation
publishedFiniteBackgroundCertificate authority RepositoryAdmissible match = record
  { RepositoryAdmissible = RepositoryAdmissible
  ; backgroundFluctuation = backgroundFluctuation authority
  ; Critical = Critical authority
  ; Minimizer = Minimizer authority
  ; GaugeEquivalent = GaugeEquivalent authority
  ; backgroundCritical = λ index coarse admissible →
      theorem1BackgroundCritical authority index coarse
        (repositoryAdmissibleImpliesPublishedAdmissible match index coarse admissible)
  ; backgroundMinimizes = λ index coarse admissible →
      theorem1BackgroundMinimizes authority index coarse
        (repositoryAdmissibleImpliesPublishedAdmissible match index coarse admissible)
  ; backgroundUniqueModuloGauge = λ index coarse fluctuation admissible critical →
      theorem1BackgroundUniqueModuloGauge authority index coarse fluctuation
        (repositoryAdmissibleImpliesPublishedAdmissible match index coarse admissible)
        critical
  }

record RGCarrierMatch
    {Scale Coupling EffectiveAction Bound : Set}
    (authority : PublishedSmallFieldRGAuthority
      Scale Coupling EffectiveAction Bound)
    (RepositorySmallFieldControl : Scale → EffectiveAction → Set) : Set₁ where
  field
    publishedControlImpliesRepositoryControl : ∀ scale action →
      SmallFieldEffectiveActionControlled authority scale action →
      RepositorySmallFieldControl scale action

open RGCarrierMatch public

publishedSmallFieldRGControl :
  ∀ {Scale Coupling EffectiveAction Bound}
  (authority : PublishedSmallFieldRGAuthority
    Scale Coupling EffectiveAction Bound)
  (RepositorySmallFieldControl : Scale → EffectiveAction → Set) →
  RGCarrierMatch authority RepositorySmallFieldControl →
  ∀ scale → RepositorySmallFieldControl scale (effectiveAction authority scale)
publishedSmallFieldRGControl authority RepositorySmallFieldControl match scale =
  publishedControlImpliesRepositoryControl match scale
    (effectiveAction authority scale)
    (theorem1And3SmallFieldControl authority scale)

publishedAuthorityAdapterAssemblyLevel : ProofLevel
publishedAuthorityAdapterAssemblyLevel = machineChecked

-- These are exact definition/hypothesis equivalence proofs, not new analytic
-- estimates.  They must be supplied before the published theorems can discharge
-- the repository's finite-background and small-field obligations.
publishedCarrierMatchingLevel : ProofLevel
publishedCarrierMatchingLevel = conditional
