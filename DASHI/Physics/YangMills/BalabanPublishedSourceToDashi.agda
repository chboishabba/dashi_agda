module DASHI.Physics.YangMills.BalabanPublishedSourceToDashi where

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPublishedAnalyticAuthorities
open import DASHI.Physics.YangMills.BalabanPublishedSourceTheoremAuthorities
open import DASHI.Physics.YangMills.BalabanExactPublishedCarrierMatching

------------------------------------------------------------------------
-- One-step composition from source-faithful published theorem statements to
-- repository certificates.  This ensures that a convenience authority cannot
-- bypass the exact source hypotheses.
------------------------------------------------------------------------

publishedSourcePropagatorAppliesToDashi :
  ∀ {Index Source State Bound Kernel Lattice BondField GaugeAction Operator
      PatchGeometry}
  (source : PublishedPropagatorTheorems31And33
    Index Source State Bound Kernel)
  (RepositoryAdmissible : Index → Set) →
  ExactPropagatorCarrierMatch
    {Lattice = Lattice}
    {BondField = BondField}
    {GaugeAction = GaugeAction}
    {Operator = Operator}
    {PatchGeometry = PatchGeometry}
    (propagatorTheorems31And33ToAuthority source)
    RepositoryAdmissible →
  RepositoryUniformPropagatorCertificate Index Source State Bound
publishedSourcePropagatorAppliesToDashi source RepositoryAdmissible match =
  publishedPropagatorAppliesToDashi
    (propagatorTheorems31And33ToAuthority source)
    RepositoryAdmissible
    match

publishedSourceVariationalBackgroundAppliesToDashi :
  ∀ {Index Coarse Fluctuation Bound BackgroundMap RGCoordinates}
  (source : PublishedVariationalTheorem1Exact
    Index Coarse Fluctuation Bound)
  (RepositoryAdmissible : Index → Coarse → Set)
  (RepositoryCritical RepositoryMinimizer :
    Index → Coarse → Fluctuation → Set)
  (RepositoryGaugeEquivalent : Fluctuation → Fluctuation → Set) →
  ExactVariationalCarrierMatch
    {BackgroundMap = BackgroundMap}
    {RGCoordinates = RGCoordinates}
    (variationalTheorem1ToAuthority source)
    RepositoryAdmissible
    RepositoryCritical
    RepositoryMinimizer
    RepositoryGaugeEquivalent →
  RepositoryFiniteBackgroundCertificate Index Coarse Fluctuation
publishedSourceVariationalBackgroundAppliesToDashi source
    RepositoryAdmissible RepositoryCritical RepositoryMinimizer
    RepositoryGaugeEquivalent match =
  publishedVariationalBackgroundAppliesToDashi
    (variationalTheorem1ToAuthority source)
    RepositoryAdmissible
    RepositoryCritical
    RepositoryMinimizer
    RepositoryGaugeEquivalent
    match

publishedSourceSmallFieldRGAppliesToDashi :
  ∀ {Scale Coupling EffectiveAction Bound RGCoordinates}
  (source : PublishedSmallFieldTheorems1And3Exact
    Scale Coupling EffectiveAction Bound)
  (RepositorySmallFieldControl : Scale → EffectiveAction → Set)
  (match : ExactSmallFieldRGCarrierMatch
    {RGCoordinates = RGCoordinates}
    (smallFieldTheorems1And3ToAuthority source)
    RepositorySmallFieldControl) →
  ∀ scale →
  RepositorySmallFieldControl scale
    (repositoryEffectiveAction match scale)
publishedSourceSmallFieldRGAppliesToDashi source RepositorySmallFieldControl
    match scale =
  publishedSmallFieldRGAppliesToDashi
    (smallFieldTheorems1And3ToAuthority source)
    RepositorySmallFieldControl
    match
    scale

publishedSourceToDashiAssemblyLevel : ProofLevel
publishedSourceToDashiAssemblyLevel = machineChecked

publishedSourceToDashiMatchingLevel : ProofLevel
publishedSourceToDashiMatchingLevel = conditional
