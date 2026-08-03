module DASHI.Physics.YangMills.YangMillsSubmissionTypedLimitEndpointExact where

------------------------------------------------------------------------
-- Typed replacements for the string-valued thermodynamic, continuum and
-- OS/Wightman endpoint packages currently used by the lightweight assembly
-- surface.  These records do not assert the analytic leaves; they ensure that
-- each leaf has a mathematical carrier, predicate and witness type rather than
-- being represented by an explanatory String.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Level; _⊔_; lsuc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record TypedThermodynamicLimitPackage
    {v b o s fm im : Level}
    (Volume : Set v)
    (BoundaryCondition : Set b)
    (Observable : Set o)
    (Scalar : Set s)
    (FiniteVolumeMeasure : Set fm)
    (InfiniteVolumeMeasure : Set im)
    : Set (lsuc (v ⊔ b ⊔ o ⊔ s ⊔ fm ⊔ im)) where
  field
    finiteVolumeMeasure :
      Volume → BoundaryCondition → FiniteVolumeMeasure

    ExponentialMomentBound :
      FiniteVolumeMeasure → Observable → Scalar → Set

    TightFamily :
      (Volume → BoundaryCondition → FiniteVolumeMeasure) → Set

    IsSubsequentialLimit :
      (Volume → BoundaryCondition → FiniteVolumeMeasure) →
      InfiniteVolumeMeasure → Set

    DLRConsistent : InfiniteVolumeMeasure → Set
    UniqueLimit : InfiniteVolumeMeasure → Set
    BoundaryIndependent : InfiniteVolumeMeasure → Set
    ReflectionPositive : InfiniteVolumeMeasure → Set
    GaugeInvariant : InfiniteVolumeMeasure → Set
    ExponentiallyClustering : InfiniteVolumeMeasure → Set
    HasInfiniteVolumeMassGap : InfiniteVolumeMeasure → Set

    observableMomentScale :
      Volume → BoundaryCondition → Observable → Scalar

    uniformExponentialMomentBounds :
      ∀ volume boundary observable →
      ExponentialMomentBound
        (finiteVolumeMeasure volume boundary)
        observable
        (observableMomentScale volume boundary observable)

    finiteVolumeFamilyTight :
      TightFamily finiteVolumeMeasure

    infiniteVolumeLimit : InfiniteVolumeMeasure

    subsequentialLimitExists :
      IsSubsequentialLimit finiteVolumeMeasure infiniteVolumeLimit

    subsequentialLimitDLRConsistent :
      DLRConsistent infiniteVolumeLimit

    infiniteVolumeLimitUnique :
      UniqueLimit infiniteVolumeLimit

    infiniteVolumeBoundaryIndependent :
      BoundaryIndependent infiniteVolumeLimit

    reflectionPositivityPreserved :
      ReflectionPositive infiniteVolumeLimit

    gaugeInvariancePreserved :
      GaugeInvariant infiniteVolumeLimit

    exponentialClusteringPreserved :
      ExponentiallyClustering infiniteVolumeLimit

    massGapSurvivesThermodynamicLimit :
      HasInfiniteVolumeMassGap infiniteVolumeLimit

open TypedThermodynamicLimitPackage public

record TypedContinuumLimitPackage
    {a r sf ct ps : Level}
    (LatticeSpacing : Set a)
    (RenormalizedObservable : Set r)
    (SchwingerFamily : Set sf)
    (ContinuumTheory : Set ct)
    (PhysicalScale : Set ps)
    : Set (lsuc (a ⊔ r ⊔ sf ⊔ ct ⊔ ps)) where
  field
    latticeSpacingSequence : Nat → LatticeSpacing
    LatticeSpacingTendsToZero : (Nat → LatticeSpacing) → Set
    spacingTendsToZero :
      LatticeSpacingTendsToZero latticeSpacingSequence

    RunningCouplingTuned : (Nat → LatticeSpacing) → Set
    runningCouplingTuned :
      RunningCouplingTuned latticeSpacingSequence

    UniformRenormalizedControl : RenormalizedObservable → Set
    uniformRenormalizedControl :
      ∀ observable → UniformRenormalizedControl observable

    CutoffSchwingerFamily : Nat → SchwingerFamily
    ContinuumTight : (Nat → SchwingerFamily) → Set
    continuumTightness : ContinuumTight CutoffSchwingerFamily

    IsContinuumSubsequentialLimit :
      (Nat → SchwingerFamily) → SchwingerFamily → Set

    continuumSchwingerFamily : SchwingerFamily
    continuumSubsequenceExists :
      IsContinuumSubsequentialLimit
        CutoffSchwingerFamily
        continuumSchwingerFamily

    RGCauchyUnique : SchwingerFamily → Set
    continuumLimitUnique :
      RGCauchyUnique continuumSchwingerFamily

    BlockingIndependent : SchwingerFamily → Set
    continuumBlockingIndependent :
      BlockingIndependent continuumSchwingerFamily

    ReflectionPositive : SchwingerFamily → Set
    TranslationInvariant : SchwingerFamily → Set
    EuclideanO4Covariant : SchwingerFamily → Set
    WardIdentitiesHold : SchwingerFamily → Set
    SymanzikDecompositionHolds : SchwingerFamily → Set
    AnisotropicCoefficientsVanish : SchwingerFamily → Set
    TriangularMixingExcluded : SchwingerFamily → Set
    InsertionsIntegrable : SchwingerFamily → Set
    OSRegular : SchwingerFamily → Set
    Nontrivial : SchwingerFamily → Set
    ExponentiallyClusteringAtPhysicalScale :
      SchwingerFamily → PhysicalScale → Set
    PositivePhysicalScale : PhysicalScale → Set

    reflectionPositivityPreserved :
      ReflectionPositive continuumSchwingerFamily
    translationInvarianceRestored :
      TranslationInvariant continuumSchwingerFamily
    euclideanO4CovarianceRestored :
      EuclideanO4Covariant continuumSchwingerFamily
    wardIdentityControl :
      WardIdentitiesHold continuumSchwingerFamily
    symanzikDecomposition :
      SymanzikDecompositionHolds continuumSchwingerFamily
    anisotropicCoefficientsVanish :
      AnisotropicCoefficientsVanish continuumSchwingerFamily
    triangularMixingExcluded :
      TriangularMixingExcluded continuumSchwingerFamily
    insertionIntegrability :
      InsertionsIntegrable continuumSchwingerFamily
    osRegularityAndGrowth :
      OSRegular continuumSchwingerFamily
    continuumTheoryNontrivial :
      Nontrivial continuumSchwingerFamily

    continuumTheory : ContinuumTheory
    physicalMassScale : PhysicalScale
    physicalMassScalePositive : PositivePhysicalScale physicalMassScale
    physicalScaleClustering :
      ExponentiallyClusteringAtPhysicalScale
        continuumSchwingerFamily
        physicalMassScale

open TypedContinuumLimitPackage public

record TypedOSWightmanEndpointPackage
    {e h ham w g : Level}
    (EuclideanTheory : Set e)
    (HilbertSpace : Set h)
    (Hamiltonian : Set ham)
    (WightmanTheory : Set w)
    (PhysicalMassGap : Set g)
    : Set (lsuc (e ⊔ h ⊔ ham ⊔ w ⊔ g)) where
  field
    euclideanTheory : EuclideanTheory

    OS0Regular : EuclideanTheory → Set
    OS1EuclideanInvariant : EuclideanTheory → Set
    OS2ReflectionPositive : EuclideanTheory → Set
    OS3Symmetric : EuclideanTheory → Set
    OS4Clustered : EuclideanTheory → Set
    OSAnalyticGrowth : EuclideanTheory → Set
    GaugeInvariantObservableDomain : EuclideanTheory → Set

    os0 : OS0Regular euclideanTheory
    os1 : OS1EuclideanInvariant euclideanTheory
    os2 : OS2ReflectionPositive euclideanTheory
    os3 : OS3Symmetric euclideanTheory
    os4 : OS4Clustered euclideanTheory
    osGrowth : OSAnalyticGrowth euclideanTheory
    gaugeInvariantDomain :
      GaugeInvariantObservableDomain euclideanTheory

    NullQuotientConstructed : EuclideanTheory → Set
    HilbertCompletionConstructed : EuclideanTheory → HilbertSpace → Set
    TimeTranslationSemigroupConstructed : HilbertSpace → Set
    PositiveSelfAdjointHamiltonian : HilbertSpace → Hamiltonian → Set
    UniqueVacuum : HilbertSpace → Hamiltonian → Set

    nullQuotient : NullQuotientConstructed euclideanTheory
    hilbertSpace : HilbertSpace
    hilbertCompletion :
      HilbertCompletionConstructed euclideanTheory hilbertSpace
    timeTranslationSemigroup :
      TimeTranslationSemigroupConstructed hilbertSpace
    hamiltonian : Hamiltonian
    positiveSelfAdjointHamiltonian :
      PositiveSelfAdjointHamiltonian hilbertSpace hamiltonian
    vacuumExistenceAndUniqueness :
      UniqueVacuum hilbertSpace hamiltonian

    wightmanTheory : WightmanTheory
    WightmanReconstruction :
      EuclideanTheory → HilbertSpace → Hamiltonian → WightmanTheory → Set
    PoincareCovariant : WightmanTheory → Set
    SpectrumCondition : WightmanTheory → Set
    LocalGaugeInvariantFields : WightmanTheory → Set
    NontrivialYangMillsTheory : WightmanTheory → Set

    wightmanReconstruction :
      WightmanReconstruction
        euclideanTheory hilbertSpace hamiltonian wightmanTheory
    poincareCovariance : PoincareCovariant wightmanTheory
    spectrumCondition : SpectrumCondition wightmanTheory
    locality : LocalGaugeInvariantFields wightmanTheory
    nontrivialYangMills : NontrivialYangMillsTheory wightmanTheory

    massGap : PhysicalMassGap
    ExponentialClusteringImpliesHamiltonianGap :
      EuclideanTheory → Hamiltonian → PhysicalMassGap → Set
    StrictlyPositivePhysicalGap : PhysicalMassGap → Set
    ClayMassGapStatement : WightmanTheory → PhysicalMassGap → Set

    clusteringToHamiltonianGap :
      ExponentialClusteringImpliesHamiltonianGap
        euclideanTheory hamiltonian massGap
    physicalGapStrictlyPositive :
      StrictlyPositivePhysicalGap massGap
    clayMassGapIdentification :
      ClayMassGapStatement wightmanTheory massGap

open TypedOSWightmanEndpointPackage public

typedThermodynamicLimitDefinitionLevel : ProofLevel
typedThermodynamicLimitDefinitionLevel = machineChecked

typedContinuumLimitDefinitionLevel : ProofLevel
typedContinuumLimitDefinitionLevel = machineChecked

typedOSWightmanEndpointDefinitionLevel : ProofLevel
typedOSWightmanEndpointDefinitionLevel = machineChecked

typedLimitEndpointInhabitantsLevel : ProofLevel
typedLimitEndpointInhabitantsLevel = conditional
