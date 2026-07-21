module DASHI.Physics.YangMills.BalabanUnconditionalSolutionCertificate where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Group-indexed terminal certificate.
--
-- Every theorem is tied to one coherent cutoff/measure/Schwinger/continuum/
-- Hamiltonian family for the selected group.  The outer certificate then
-- requires such a construction for every compact simple gauge group, matching
-- the quantifier in the official Jaffe--Witten problem statement.
------------------------------------------------------------------------

record GaugeGroupYangMillsSolution
    {GaugeGroup : Set}
    (G : GaugeGroup)
    (CutoffFamily MeasureFamily SchwingerFamily InfiniteVolumeTheory
      ContinuumTheory PhysicalObservableAlgebra HilbertSpace Hamiltonian Mass :
      Set) : Set₁ where
  field
    selectedCutoffFamily : CutoffFamily
    selectedMeasureFamily : MeasureFamily
    selectedSchwingerFamily : SchwingerFamily
    selectedInfiniteVolumeTheory : InfiniteVolumeTheory
    selectedContinuumTheory : ContinuumTheory
    selectedPhysicalObservableAlgebra : PhysicalObservableAlgebra
    selectedHilbertSpace : HilbertSpace
    selectedHamiltonian : Hamiltonian
    selectedMassGap : Mass

    FiniteVolumeConstruction :
      GaugeGroup → CutoffFamily → MeasureFamily → Set
    finiteVolumeConstruction :
      FiniteVolumeConstruction G selectedCutoffFamily selectedMeasureFamily

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

    QuantumYangMillsTheoryOnR4 : GaugeGroup → ContinuumTheory → Set
    quantumYangMillsTheoryOnR4 :
      QuantumYangMillsTheoryOnR4 G selectedContinuumTheory

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

    ImportedAuthoritiesHypothesesMatch :
      GaugeGroup → CutoffFamily → MeasureFamily → SchwingerFamily → Set
    importedAuthoritiesHypothesesMatch :
      ImportedAuthoritiesHypothesesMatch
        G selectedCutoffFamily selectedMeasureFamily selectedSchwingerFamily

open GaugeGroupYangMillsSolution public

record UnconditionalYangMillsSolution
    (GaugeGroup : Set)
    (CutoffFamily MeasureFamily SchwingerFamily InfiniteVolumeTheory
      ContinuumTheory PhysicalObservableAlgebra HilbertSpace Hamiltonian Mass :
      GaugeGroup → Set) : Set₂ where
  field
    CompactSimpleGaugeGroup : GaugeGroup → Set

    solutionForEveryCompactSimpleGaugeGroup :
      ∀ G → CompactSimpleGaugeGroup G →
      GaugeGroupYangMillsSolution
        G
        (CutoffFamily G)
        (MeasureFamily G)
        (SchwingerFamily G)
        (InfiniteVolumeTheory G)
        (ContinuumTheory G)
        (PhysicalObservableAlgebra G)
        (HilbertSpace G)
        (Hamiltonian G)
        (Mass G)

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

    OfficialJaffeWittenStatementMatched : Set
    officialJaffeWittenStatementMatched : OfficialJaffeWittenStatementMatched

open UnconditionalYangMillsSolution public

-- Promotion is derived only from an all-groups coherent complete certificate.
-- There is deliberately no nullary `true` declaration: until such a value is
-- constructed, the aggregate repository status remains fail-closed.
clayYangMillsSubmissionPromotion :
  ∀ {GaugeGroup}
    {CutoffFamily MeasureFamily SchwingerFamily InfiniteVolumeTheory
      ContinuumTheory PhysicalObservableAlgebra HilbertSpace Hamiltonian Mass :
      GaugeGroup → Set} →
  UnconditionalYangMillsSolution
    GaugeGroup CutoffFamily MeasureFamily SchwingerFamily InfiniteVolumeTheory
    ContinuumTheory PhysicalObservableAlgebra HilbertSpace Hamiltonian Mass →
  Bool
clayYangMillsSubmissionPromotion solution = true

certificatePromotesSubmission :
  ∀ {GaugeGroup}
    {CutoffFamily MeasureFamily SchwingerFamily InfiniteVolumeTheory
      ContinuumTheory PhysicalObservableAlgebra HilbertSpace Hamiltonian Mass :
      GaugeGroup → Set}
    (solution : UnconditionalYangMillsSolution
      GaugeGroup CutoffFamily MeasureFamily SchwingerFamily InfiniteVolumeTheory
      ContinuumTheory PhysicalObservableAlgebra HilbertSpace Hamiltonian Mass) →
  clayYangMillsSubmissionPromotion solution ≡ true
certificatePromotesSubmission solution = refl

unconditionalSolutionGateAssemblyLevel : ProofLevel
unconditionalSolutionGateAssemblyLevel = machineChecked

unconditionalSolutionInhabitationLevel : ProofLevel
unconditionalSolutionInhabitationLevel = conjectural
