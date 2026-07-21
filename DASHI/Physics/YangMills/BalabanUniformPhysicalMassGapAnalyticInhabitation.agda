module DASHI.Physics.YangMills.BalabanUniformPhysicalMassGapAnalyticInhabitation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Osterwalder--Schrader reconstruction surface.
------------------------------------------------------------------------

record OSReconstructionAnalyticInputs
    (SchwingerSystem Hilbert Vector Hamiltonian Algebra : Set) : Set₁ where
  field
    system : SchwingerSystem
    reconstructedHilbertSpace : Hilbert
    reconstructedVacuum : Vector
    reconstructedHamiltonian : Hamiltonian
    reconstructedObservableAlgebra : Algebra

    OSAxioms : SchwingerSystem → Set
    VacuumVector : Hilbert → Vector → Set
    SelfAdjoint Nonnegative : Hamiltonian → Set
    PhysicalObservableAlgebra : Algebra → Set
    VacuumFor : Hamiltonian → Vector → Set
    EqualVector : Vector → Vector → Set

    osAxiomsReconstructHilbertSpaceInput :
      OSAxioms system
    reconstructedVacuumExistsInput :
      VacuumVector reconstructedHilbertSpace reconstructedVacuum
    reconstructedHamiltonianSelfAdjointInput :
      SelfAdjoint reconstructedHamiltonian
    reconstructedHamiltonianNonnegativeInput :
      Nonnegative reconstructedHamiltonian
    physicalObservableAlgebraReconstructedInput :
      PhysicalObservableAlgebra reconstructedObservableAlgebra
    reconstructedVacuumIsVacuumInput :
      VacuumFor reconstructedHamiltonian reconstructedVacuum
    vacuumUniqueInput : ∀ candidate →
      VacuumFor reconstructedHamiltonian candidate →
      EqualVector candidate reconstructedVacuum

open OSReconstructionAnalyticInputs public

osAxiomsReconstructHilbertSpace = osAxiomsReconstructHilbertSpaceInput
reconstructedVacuumExists = reconstructedVacuumExistsInput
reconstructedHamiltonianSelfAdjoint = reconstructedHamiltonianSelfAdjointInput
reconstructedHamiltonianNonnegative = reconstructedHamiltonianNonnegativeInput
physicalObservableAlgebraReconstructed = physicalObservableAlgebraReconstructedInput
vacuumUnique = vacuumUniqueInput

------------------------------------------------------------------------
-- Physical mass-gap certificate.
------------------------------------------------------------------------

record PhysicalMassGapCertificate (Hamiltonian Bound : Set) : Set₁ where
  field
    hamiltonian : Hamiltonian
    gap : Bound
    Positive : Bound → Set
    gapPositive : Positive gap
    SpectrumSeparatedBy : Hamiltonian → Bound → Set
    spectrumSeparated : SpectrumSeparatedBy hamiltonian gap
open PhysicalMassGapCertificate public

------------------------------------------------------------------------
-- Route A: uniform connected clustering to spectral gap.
------------------------------------------------------------------------

record RouteAClusteringGapInputs
    (Observable Time Scalar Bound Hamiltonian : Set) : Set₁ where
  field
    connectedCorrelation : Observable → Observable → Time → Scalar
    absoluteValue : Scalar → Bound
    multiply : Bound → Bound → Bound
    exponentialDecay : Bound → Time → Bound
    LessEqual : Bound → Bound → Set
    correlationConstant : Observable → Observable → Bound

    hamiltonian : Hamiltonian
    mStar : Bound
    Positive : Bound → Set
    mStarPositiveInput : Positive mStar

    uniformConnectedCorrelationDecayInput : ∀ A B t →
      LessEqual
        (absoluteValue (connectedCorrelation A B t))
        (multiply (correlationConstant A B) (exponentialDecay mStar t))

    PhysicalObservableVectorsDenseInVacuumOrthogonalSpace
      ObservableAlgebraCyclicForVacuum : Set
    physicalObservableVectorsDenseInVacuumOrthogonalSpaceInput :
      PhysicalObservableVectorsDenseInVacuumOrthogonalSpace
    observableAlgebraCyclicForVacuumInput : ObservableAlgebraCyclicForVacuum

    HamiltonianTimeClustering : Hamiltonian → Bound → Set
    euclideanClusteringImpliesHamiltonianTimeClusteringInput :
      (∀ A B t →
        LessEqual
          (absoluteValue (connectedCorrelation A B t))
          (multiply (correlationConstant A B) (exponentialDecay mStar t))) →
      HamiltonianTimeClustering hamiltonian mStar

    SpectrumSeparatedBy : Hamiltonian → Bound → Set
    exponentialSemigroupDecayImpliesSpectralSupportAboveInput :
      HamiltonianTimeClustering hamiltonian mStar →
      PhysicalObservableVectorsDenseInVacuumOrthogonalSpace →
      ObservableAlgebraCyclicForVacuum →
      SpectrumSeparatedBy hamiltonian mStar

open RouteAClusteringGapInputs public

uniformConnectedCorrelationDecay = uniformConnectedCorrelationDecayInput
mStarPositive = mStarPositiveInput
physicalObservableVectorsDenseInVacuumOrthogonalSpace =
  physicalObservableVectorsDenseInVacuumOrthogonalSpaceInput
observableAlgebraCyclicForVacuum = observableAlgebraCyclicForVacuumInput

euclideanClusteringImpliesHamiltonianTimeClustering :
  ∀ {Observable Time Scalar Bound Hamiltonian} →
  (d : RouteAClusteringGapInputs Observable Time Scalar Bound Hamiltonian) →
  HamiltonianTimeClustering d (hamiltonian d) (mStar d)
euclideanClusteringImpliesHamiltonianTimeClustering d =
  euclideanClusteringImpliesHamiltonianTimeClusteringInput d
    (uniformConnectedCorrelationDecayInput d)

exponentialSemigroupDecayImpliesSpectralSupportAbove :
  ∀ {Observable Time Scalar Bound Hamiltonian} →
  (d : RouteAClusteringGapInputs Observable Time Scalar Bound Hamiltonian) →
  SpectrumSeparatedBy d (hamiltonian d) (mStar d)
exponentialSemigroupDecayImpliesSpectralSupportAbove d =
  exponentialSemigroupDecayImpliesSpectralSupportAboveInput d
    (euclideanClusteringImpliesHamiltonianTimeClustering d)
    (physicalObservableVectorsDenseInVacuumOrthogonalSpaceInput d)
    (observableAlgebraCyclicForVacuumInput d)

exponentialTimeClusteringImpliesSpectrumGap :
  ∀ {Observable Time Scalar Bound Hamiltonian} →
  (d : RouteAClusteringGapInputs Observable Time Scalar Bound Hamiltonian) →
  PhysicalMassGapCertificate Hamiltonian Bound
exponentialTimeClusteringImpliesSpectrumGap d = record
  { hamiltonian = hamiltonian d
  ; gap = mStar d
  ; Positive = Positive d
  ; gapPositive = mStarPositiveInput d
  ; SpectrumSeparatedBy = SpectrumSeparatedBy d
  ; spectrumSeparated = exponentialSemigroupDecayImpliesSpectralSupportAbove d
  }

------------------------------------------------------------------------
-- Route B: finite-cutoff transfer Hamiltonians and no spectral pollution.
------------------------------------------------------------------------

record RouteBCutoffGapInputs
    (Cutoff TransferOperator Hamiltonian Projection Bound : Set) : Set₁ where
  field
    transferOperator : Cutoff → TransferOperator
    cutoffHamiltonian : Cutoff → Hamiltonian
    continuumHamiltonian : Hamiltonian
    cutoffVacuumProjection : Cutoff → Projection
    continuumVacuumProjection : Projection
    cutoffGap : Cutoff → Bound
    mStar : Bound

    Positive : Bound → Set
    LessEqual : Bound → Bound → Set
    mStarPositiveInput : Positive mStar

    TransferOperatorPositive : TransferOperator → Set
    TransferOperatorSelfAdjoint : TransferOperator → Set
    HamiltonianDefinedFrom : TransferOperator → Hamiltonian → Set
    VacuumExists : Hamiltonian → Set

    finiteCutoffTransferOperatorPositiveInput : ∀ cutoff →
      TransferOperatorPositive (transferOperator cutoff)
    finiteCutoffTransferOperatorSelfAdjointInput : ∀ cutoff →
      TransferOperatorSelfAdjoint (transferOperator cutoff)
    finiteCutoffHamiltonianDefinedInput : ∀ cutoff →
      HamiltonianDefinedFrom (transferOperator cutoff) (cutoffHamiltonian cutoff)
    finiteCutoffVacuumExistsInput : ∀ cutoff →
      VacuumExists (cutoffHamiltonian cutoff)

    SpectrumSeparatedBy : Hamiltonian → Bound → Set
    finiteCutoffSpectrumSeparatedInput : ∀ cutoff →
      SpectrumSeparatedBy (cutoffHamiltonian cutoff) (cutoffGap cutoff)
    uniformPositiveCutoffGapInput : ∀ cutoff →
      LessEqual mStar (cutoffGap cutoff)

    StrongResolventConvergesTo :
      (Cutoff → Hamiltonian) → Hamiltonian → Set
    cutoffHamiltoniansConvergeStrongResolventInput :
      StrongResolventConvergesTo cutoffHamiltonian continuumHamiltonian

    VacuumProjectionsConvergeTo :
      (Cutoff → Projection) → Projection → Set
    cutoffVacuumProjectionsConvergeInput :
      VacuumProjectionsConvergeTo
        cutoffVacuumProjection continuumVacuumProjection

    VacuumMultiplicityStable : Set
    vacuumMultiplicityStableInput : VacuumMultiplicityStable

    strongResolventUniformGapTransferInput :
      StrongResolventConvergesTo cutoffHamiltonian continuumHamiltonian →
      VacuumProjectionsConvergeTo cutoffVacuumProjection continuumVacuumProjection →
      VacuumMultiplicityStable →
      (∀ cutoff → SpectrumSeparatedBy
        (cutoffHamiltonian cutoff) (cutoffGap cutoff)) →
      (∀ cutoff → LessEqual mStar (cutoffGap cutoff)) →
      SpectrumSeparatedBy continuumHamiltonian mStar

open RouteBCutoffGapInputs public

finiteCutoffTransferOperatorPositive = finiteCutoffTransferOperatorPositiveInput
finiteCutoffTransferOperatorSelfAdjoint =
  finiteCutoffTransferOperatorSelfAdjointInput
finiteCutoffHamiltonianDefined = finiteCutoffHamiltonianDefinedInput
finiteCutoffVacuumExists = finiteCutoffVacuumExistsInput
finiteCutoffSpectrumSeparated = finiteCutoffSpectrumSeparatedInput
uniformPositiveCutoffGap = uniformPositiveCutoffGapInput
cutoffHamiltoniansConvergeStrongResolvent =
  cutoffHamiltoniansConvergeStrongResolventInput
cutoffVacuumProjectionsConverge = cutoffVacuumProjectionsConvergeInput
vacuumMultiplicityStable = vacuumMultiplicityStableInput

strongResolventUniformGapTransfer :
  ∀ {Cutoff TransferOperator Hamiltonian Projection Bound} →
  (d : RouteBCutoffGapInputs
    Cutoff TransferOperator Hamiltonian Projection Bound) →
  SpectrumSeparatedBy d (continuumHamiltonian d) (mStar d)
strongResolventUniformGapTransfer d =
  strongResolventUniformGapTransferInput d
    (cutoffHamiltoniansConvergeStrongResolventInput d)
    (cutoffVacuumProjectionsConvergeInput d)
    (vacuumMultiplicityStableInput d)
    (finiteCutoffSpectrumSeparatedInput d)
    (uniformPositiveCutoffGapInput d)

strongResolventLimitPreservesUniformGap = strongResolventUniformGapTransfer

continuumSpectrumSeparated :
  ∀ {Cutoff TransferOperator Hamiltonian Projection Bound} →
  (d : RouteBCutoffGapInputs
    Cutoff TransferOperator Hamiltonian Projection Bound) →
  PhysicalMassGapCertificate Hamiltonian Bound
continuumSpectrumSeparated d = record
  { hamiltonian = continuumHamiltonian d
  ; gap = mStar d
  ; Positive = Positive d
  ; gapPositive = mStarPositiveInput d
  ; SpectrumSeparatedBy = SpectrumSeparatedBy d
  ; spectrumSeparated = strongResolventUniformGapTransfer d
  }

continuumSpectrumSeparatedViaSurvivalBridge = continuumSpectrumSeparated

------------------------------------------------------------------------
-- Coherent route owner.  A submission may use either route, but all witnesses
-- in a selected route belong to one continuum system/cutoff family.
------------------------------------------------------------------------

data MassGapRoute
    (Observable Time Scalar Cutoff TransferOperator Hamiltonian Projection Bound : Set)
    : Set₁ where
  clusteringRoute :
    RouteAClusteringGapInputs Observable Time Scalar Bound Hamiltonian →
    MassGapRoute Observable Time Scalar Cutoff TransferOperator Hamiltonian Projection Bound
  cutoffRoute :
    RouteBCutoffGapInputs Cutoff TransferOperator Hamiltonian Projection Bound →
    MassGapRoute Observable Time Scalar Cutoff TransferOperator Hamiltonian Projection Bound

massGapFromSelectedRoute :
  ∀ {Observable Time Scalar Cutoff TransferOperator Hamiltonian Projection Bound} →
  MassGapRoute Observable Time Scalar Cutoff TransferOperator Hamiltonian Projection Bound →
  PhysicalMassGapCertificate Hamiltonian Bound
massGapFromSelectedRoute (clusteringRoute d) =
  exponentialTimeClusteringImpliesSpectrumGap d
massGapFromSelectedRoute (cutoffRoute d) = continuumSpectrumSeparated d

osReconstructionAuthorityLevel : ProofLevel
osReconstructionAuthorityLevel = standardImported

osReconstructionExtractionLevel : ProofLevel
osReconstructionExtractionLevel = machineChecked

routeAAssemblyLevel : ProofLevel
routeAAssemblyLevel = machineChecked

uniformConnectedClusteringInputLevel : ProofLevel
uniformConnectedClusteringInputLevel = conjectural

routeASpectralTransferLevel : ProofLevel
routeASpectralTransferLevel = standardImported

routeBAssemblyLevel : ProofLevel
routeBAssemblyLevel = machineChecked

finiteCutoffGapInputLevel : ProofLevel
finiteCutoffGapInputLevel = conjectural

strongResolventInputLevel : ProofLevel
strongResolventInputLevel = conjectural

noSpectralPollutionTransferLevel : ProofLevel
noSpectralPollutionTransferLevel = standardImported
