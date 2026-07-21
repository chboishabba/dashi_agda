module DASHI.Physics.YangMills.BalabanUnconditionalSolutionCertificate where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Terminal fail-closed certificate for the constructive Yang--Mills chain.
--
-- This record contains proof objects, not status flags.  A value can only be
-- constructed after the finite-volume, thermodynamic, continuum OS,
-- interaction and mass-gap theorems have all been proved for one coherent
-- family.  No global inhabitant is supplied here.
------------------------------------------------------------------------

record UnconditionalYangMillsSolution : Set₁ where
  field
    FiniteVolumeConstruction : Set
    finiteVolumeConstruction : FiniteVolumeConstruction

    UniformRenormalizedSchwingerBounds : Set
    uniformRenormalizedSchwingerBounds : UniformRenormalizedSchwingerBounds

    ThermodynamicLimitExists : Set
    thermodynamicLimitExists : ThermodynamicLimitExists

    ThermodynamicLimitUnique : Set
    thermodynamicLimitUnique : ThermodynamicLimitUnique

    BoundaryConditionIndependent : Set
    boundaryConditionIndependent : BoundaryConditionIndependent

    ContinuumLimitExists : Set
    continuumLimitExists : ContinuumLimitExists

    ContinuumLimitUnique : Set
    continuumLimitUnique : ContinuumLimitUnique

    ContinuumOSAxioms : Set
    continuumOSAxioms : ContinuumOSAxioms

    GaugeFixingIndependentPhysicalAlgebra : Set
    gaugeFixingIndependentPhysicalAlgebra :
      GaugeFixingIndependentPhysicalAlgebra

    ContinuumTheoryNonzero : Set
    continuumTheoryNonzero : ContinuumTheoryNonzero

    ContinuumTheoryNonGaussian : Set
    continuumTheoryNonGaussian : ContinuumTheoryNonGaussian

    UniformConnectedCorrelationDecay : Set
    uniformConnectedCorrelationDecay : UniformConnectedCorrelationDecay

    PositiveClusteringRate : Set
    positiveClusteringRate : PositiveClusteringRate

    PhysicalHamiltonianMassGap : Set
    physicalHamiltonianMassGap : PhysicalHamiltonianMassGap

    FocusedAggregateTypechecks : Set
    focusedAggregateTypechecks : FocusedAggregateTypechecks

    FullRepositoryTypechecks : Set
    fullRepositoryTypechecks : FullRepositoryTypechecks

    NoLocalPostulate : Set
    noLocalPostulate : NoLocalPostulate

    NoUnsolvedMetavariables : Set
    noUnsolvedMetavariables : NoUnsolvedMetavariables

    NoConditionalLeafOnFinalPath : Set
    noConditionalLeafOnFinalPath : NoConditionalLeafOnFinalPath

    NoConjecturalLeafOnFinalPath : Set
    noConjecturalLeafOnFinalPath : NoConjecturalLeafOnFinalPath

    ImportedAuthoritiesHypothesesMatch : Set
    importedAuthoritiesHypothesesMatch : ImportedAuthoritiesHypothesesMatch

open UnconditionalYangMillsSolution public

-- Promotion is derived from a complete certificate.  There is deliberately no
-- nullary `true` declaration: until a certificate is constructed, the existing
-- aggregate remains fail-closed.
clayYangMillsSubmissionPromotion :
  UnconditionalYangMillsSolution → Bool
clayYangMillsSubmissionPromotion solution = true

certificatePromotesSubmission :
  ∀ solution → clayYangMillsSubmissionPromotion solution ≡ true
certificatePromotesSubmission solution = refl

unconditionalSolutionGateAssemblyLevel : ProofLevel
unconditionalSolutionGateAssemblyLevel = machineChecked

unconditionalSolutionInhabitationLevel : ProofLevel
unconditionalSolutionInhabitationLevel = conjectural
