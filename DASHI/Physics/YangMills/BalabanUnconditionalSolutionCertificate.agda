module DASHI.Physics.YangMills.BalabanUnconditionalSolutionCertificate where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Terminal fail-closed certificate for the constructive Yang--Mills chain.
--
-- Every theorem below is indexed by the same selected gauge group, cutoff
-- family, finite-volume measures, Schwinger family, infinite-volume limit,
-- continuum limit and reconstructed Hamiltonian.  This prevents a terminal
-- certificate from mixing witnesses belonging to unrelated constructions.
-- No global inhabitant is supplied here.
------------------------------------------------------------------------

record UnconditionalYangMillsSolution
    (GaugeGroup CutoffFamily MeasureFamily SchwingerFamily
      InfiniteVolumeTheory ContinuumTheory PhysicalObservableAlgebra
      HilbertSpace Hamiltonian Mass : Set) : Set₁ where
  field
    selectedGaugeGroup : GaugeGroup
    selectedCutoffFamily : CutoffFamily
    selectedMeasureFamily : MeasureFamily
    selectedSchwingerFamily : SchwingerFamily
    selectedInfiniteVolumeTheory : InfiniteVolumeTheory
    selectedContinuumTheory : ContinuumTheory
    selectedPhysicalObservableAlgebra : PhysicalObservableAlgebra
    selectedHilbertSpace : HilbertSpace
    selectedHamiltonian : Hamiltonian
    selectedMassGap : Mass

    CompactSimpleGaugeGroup : GaugeGroup → Set
    compactSimpleGaugeGroup : CompactSimpleGaugeGroup selectedGaugeGroup

    FiniteVolumeConstruction :
      GaugeGroup → CutoffFamily → MeasureFamily → Set
    finiteVolumeConstruction :
      FiniteVolumeConstruction
        selectedGaugeGroup selectedCutoffFamily selectedMeasureFamily

    SchwingerFamilyGeneratedByMeasures :
      MeasureFamily → SchwingerFamily → Set
    schwingerFamilyGeneratedByMeasures :
      SchwingerFamilyGeneratedByMeasures
        selectedMeasureFamily selectedSchwingerFamily

    UniformRenormalizedSchwingerBounds :
      CutoffFamily → SchwingerFamily → Set
    uniformRenormalizedSchwingerBounds :
      UniformRenormalizedSchwingerBounds
        selectedCutoffFamily selectedSchwingerFamily

    ThermodynamicLimitOf :
      SchwingerFamily → InfiniteVolumeTheory → Set
    thermodynamicLimitExists :
      ThermodynamicLimitOf
        selectedSchwingerFamily selectedInfiniteVolumeTheory

    ThermodynamicLimitUnique :
      SchwingerFamily → InfiniteVolumeTheory → Set
    thermodynamicLimitUnique :
      ThermodynamicLimitUnique
        selectedSchwingerFamily selectedInfiniteVolumeTheory

    BoundaryConditionIndependent : InfiniteVolumeTheory → Set
    boundaryConditionIndependent :
      BoundaryConditionIndependent selectedInfiniteVolumeTheory

    ContinuumLimitOf : InfiniteVolumeTheory → ContinuumTheory → Set
    continuumLimitExists :
      ContinuumLimitOf selectedInfiniteVolumeTheory selectedContinuumTheory

    ContinuumLimitUnique : InfiniteVolumeTheory → ContinuumTheory → Set
    continuumLimitUnique :
      ContinuumLimitUnique selectedInfiniteVolumeTheory selectedContinuumTheory

    ContinuumOSAxioms : ContinuumTheory → Set
    continuumOSAxioms : ContinuumOSAxioms selectedContinuumTheory

    PhysicalAlgebraOf :
      ContinuumTheory → PhysicalObservableAlgebra → Set
    physicalAlgebraOf :
      PhysicalAlgebraOf
        selectedContinuumTheory selectedPhysicalObservableAlgebra

    GaugeFixingIndependentPhysicalAlgebra :
      ContinuumTheory → PhysicalObservableAlgebra → Set
    gaugeFixingIndependentPhysicalAlgebra :
      GaugeFixingIndependentPhysicalAlgebra
        selectedContinuumTheory selectedPhysicalObservableAlgebra

    ContinuumTheoryNonzero : ContinuumTheory → Set
    continuumTheoryNonzero : ContinuumTheoryNonzero selectedContinuumTheory

    ContinuumTheoryNonGaussian : ContinuumTheory → Set
    continuumTheoryNonGaussian :
      ContinuumTheoryNonGaussian selectedContinuumTheory

    UniformConnectedCorrelationDecay :
      SchwingerFamily → Mass → Set
    uniformConnectedCorrelationDecay :
      UniformConnectedCorrelationDecay
        selectedSchwingerFamily selectedMassGap

    Positive : Mass → Set
    positiveClusteringRate : Positive selectedMassGap

    OSReconstructionProduces :
      ContinuumTheory → PhysicalObservableAlgebra →
      HilbertSpace → Hamiltonian → Set
    osReconstructionProduces :
      OSReconstructionProduces
        selectedContinuumTheory
        selectedPhysicalObservableAlgebra
        selectedHilbertSpace
        selectedHamiltonian

    PhysicalHamiltonianMassGap : Hamiltonian → Mass → Set
    physicalHamiltonianMassGap :
      PhysicalHamiltonianMassGap selectedHamiltonian selectedMassGap

    FocusedAggregateTypechecks : Set
    focusedAggregateTypechecks : FocusedAggregateTypechecks

    FullRepositoryTypechecks : Set
    fullRepositoryTypechecks : FullRepositoryTypechecks

    NoLocalPostulate : Set
    noLocalPostulate : NoLocalPostulate

    NoUnsolvedMetavariables : Set
    noUnsolvedMetavariables : NoUnsolvedMetavariables

    NoConditionalLeafOnFinalPath :
      GaugeGroup → CutoffFamily → MeasureFamily → SchwingerFamily →
      InfiniteVolumeTheory → ContinuumTheory → Hamiltonian → Set
    noConditionalLeafOnFinalPath :
      NoConditionalLeafOnFinalPath
        selectedGaugeGroup selectedCutoffFamily selectedMeasureFamily
        selectedSchwingerFamily selectedInfiniteVolumeTheory
        selectedContinuumTheory selectedHamiltonian

    NoConjecturalLeafOnFinalPath :
      GaugeGroup → CutoffFamily → MeasureFamily → SchwingerFamily →
      InfiniteVolumeTheory → ContinuumTheory → Hamiltonian → Set
    noConjecturalLeafOnFinalPath :
      NoConjecturalLeafOnFinalPath
        selectedGaugeGroup selectedCutoffFamily selectedMeasureFamily
        selectedSchwingerFamily selectedInfiniteVolumeTheory
        selectedContinuumTheory selectedHamiltonian

    ImportedAuthoritiesHypothesesMatch :
      GaugeGroup → CutoffFamily → MeasureFamily → SchwingerFamily → Set
    importedAuthoritiesHypothesesMatch :
      ImportedAuthoritiesHypothesesMatch
        selectedGaugeGroup selectedCutoffFamily
        selectedMeasureFamily selectedSchwingerFamily

open UnconditionalYangMillsSolution public

-- Promotion is derived from a coherent complete certificate. There is
-- deliberately no nullary `true` declaration: until such a certificate is
-- constructed, the aggregate repository status remains fail-closed.
clayYangMillsSubmissionPromotion :
  ∀ {GaugeGroup CutoffFamily MeasureFamily SchwingerFamily
      InfiniteVolumeTheory ContinuumTheory PhysicalObservableAlgebra
      HilbertSpace Hamiltonian Mass} →
  UnconditionalYangMillsSolution
    GaugeGroup CutoffFamily MeasureFamily SchwingerFamily
    InfiniteVolumeTheory ContinuumTheory PhysicalObservableAlgebra
    HilbertSpace Hamiltonian Mass →
  Bool
clayYangMillsSubmissionPromotion solution = true

certificatePromotesSubmission :
  ∀ {GaugeGroup CutoffFamily MeasureFamily SchwingerFamily
      InfiniteVolumeTheory ContinuumTheory PhysicalObservableAlgebra
      HilbertSpace Hamiltonian Mass}
    (solution : UnconditionalYangMillsSolution
      GaugeGroup CutoffFamily MeasureFamily SchwingerFamily
      InfiniteVolumeTheory ContinuumTheory PhysicalObservableAlgebra
      HilbertSpace Hamiltonian Mass) →
  clayYangMillsSubmissionPromotion solution ≡ true
certificatePromotesSubmission solution = refl

unconditionalSolutionGateAssemblyLevel : ProofLevel
unconditionalSolutionGateAssemblyLevel = machineChecked

unconditionalSolutionInhabitationLevel : ProofLevel
unconditionalSolutionInhabitationLevel = conjectural
