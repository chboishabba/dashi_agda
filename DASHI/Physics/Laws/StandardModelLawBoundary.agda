module DASHI.Physics.Laws.StandardModelLawBoundary where

open import DASHI.Physics.Laws.GaugeInteractionLaws
open import DASHI.Physics.Laws.QuantumFieldLaws

-- The Standard Model surface separates gauge-group and representation content,
-- anomaly cancellation, symmetry breaking, flavour structure, running, and
-- measured parameters.  Finite bookkeeping does not prove uniqueness.
data StandardModelGaugeFactor : Set where
  colourSU3       : StandardModelGaugeFactor
  weakSU2         : StandardModelGaugeFactor
  hyperchargeU1   : StandardModelGaugeFactor

data FermionSector : Set where
  quarkSector  : FermionSector
  leptonSector : FermionSector
  neutrinoSector : FermionSector

data Chirality : Set where
  leftHanded  : Chirality
  rightHanded : Chirality

record StandardModelRepresentationTable : Set₁ where
  field
    Multiplet      : Set
    Representation : Set
    Hypercharge    : Set
    Generation     : Set

    gaugeRepresentation : Multiplet → StandardModelGaugeFactor → Representation
    hypercharge         : Multiplet → Hypercharge
    generation          : Multiplet → Generation
    chirality           : Multiplet → Chirality
    sector              : Multiplet → FermionSector

    AnomalyCoefficient  : Set
    anomalyCoefficient  : Multiplet → AnomalyCoefficient
    GaugeAnomaliesCancel : Set
    MixedAnomaliesCancel : Set
    GravitationalAnomalyCancels : Set

record HiggsElectroweakLaw : Set₁ where
  field
    HiggsField      : Set
    Vacuum          : Set
    Potential       : Set
    GaugeBoson      : Set
    Mass            : Set
    Coupling        : Set

    potential       : HiggsField → Potential
    vacuum          : Potential → Vacuum
    gaugeMass       : Vacuum → Coupling → GaugeBoson → Mass
    SymmetryBroken  : Vacuum → Set
    VacuumStable    : Vacuum → Set

record YukawaFlavourLaw : Set₁ where
  field
    Fermion        : Set
    Generation     : Set
    YukawaMatrix   : Set
    MassMatrix     : Set
    MixingMatrix   : Set
    Phase          : Set

    yukawa         : Fermion → YukawaMatrix
    massMatrix     : YukawaMatrix → MassMatrix
    diagonalise    : MassMatrix → MixingMatrix
    ckmMatrix      : MixingMatrix
    pmnsMatrix     : MixingMatrix
    cpPhase        : MixingMatrix → Phase

    UnitaryMixing  : MixingMatrix → Set

record GaugeCouplingRunning : Set₁ where
  field
    Scale       : Set
    Coupling    : Set
    BetaFunction : Set
    Scheme      : Set

    couplingAt  : Scheme → Scale → StandardModelGaugeFactor → Coupling
    beta        : Scheme → StandardModelGaugeFactor → BetaFunction
    renormalisationGroupEquation : Scheme → StandardModelGaugeFactor → Set

record StandardModelObservableBridge : Set₁ where
  field
    QFTModel      : Set
    Process       : Set
    Amplitude     : Set
    CrossSection  : Set
    DecayRate     : Set
    Dataset       : Set
    Uncertainty   : Set

    amplitude     : QFTModel → Process → Amplitude
    crossSection  : Amplitude → CrossSection
    decayRate     : Amplitude → DecayRate
    CompareToData : CrossSection → Dataset → Uncertainty → Set

record StandardModelLawSurface : Set₁ where
  field
    gaugeGeometry : GaugeFieldGeometry
    quantumFields : RelativisticQuantumField
    representations : StandardModelRepresentationTable
    higgsSector     : HiggsElectroweakLaw
    flavourSector   : YukawaFlavourLaw
    running         : GaugeCouplingRunning
    observables     : StandardModelObservableBridge

    GaugeGroupContinuousRealisation : Set
    ChiralRepresentationRealisation : Set
    AnomalyCancellationRealisation  : Set
    RenormalisedInteractingQFT       : Set

    gaugeGroupWitness : GaugeGroupContinuousRealisation
    representationWitness : ChiralRepresentationRealisation
    anomalyWitness : AnomalyCancellationRealisation
    qftWitness : RenormalisedInteractingQFT

record StandardModelOpenObligations : Set₁ where
  field
    gaugeGroupUniqueness : Set
    representationUniqueness : Set
    exactlyThreeGenerations : Set
    neutrinoMassMechanism : Set
    higgsPotentialFromFirstPrinciples : Set
    yukawaHierarchyFromFirstPrinciples : Set
    ckmPmnsPhasesFromFirstPrinciples : Set
    gaugeCouplingsAndRunningCalibration : Set
    nonperturbativeQCDControl : Set
    observableReconstructionAndDataAuthority : Set

record StandardModelAuthorityBoundary : Set₁ where
  field
    finiteGaugeNameMatchIsNotContinuousUniqueness : Set
    anomalyCancellationIsNotFullModelDerivation : Set
    higgsMechanismDoesNotFixMeasuredParameters : Set
    ckmUnitarityDoesNotDeriveMatrixEntries : Set
    perturbativeQFTIsNotNonperturbativeCompletion : Set
    measuredConstantsRequireVersionedAuthority : Set
    beyondStandardModelPhysicsNotDerived : Set
