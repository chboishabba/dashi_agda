module DASHI.Physics.Chemistry.AtomicPeriodicTable369C3EntropyIntertwinerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact as Chemistry369
import DASHI.Physics.Chemistry.AmmoniaC3MolecularFixtureExact as NH3
import DASHI.Physics.Chemistry.AmmoniaC3ElectronicSymmetryExact as NH3Electronic
import DASHI.Physics.Chemistry.AmmoniaProtonationReactionExact as NH3Protonation
import DASHI.Physics.Chemistry.AmmoniaH3PlusProtonTransferExact as H3Transfer
import DASHI.Physics.Closure.MonsterC3EntropyStateCountingExact as MonsterEntropy
import DASHI.Moonshine.C3FourierConjugationExact as C3Fourier

data C3Sector : Set where
  sector0 sector1 sector2 : C3Sector

sectorFourierRow : C3Sector → C3Fourier.FourierRow
sectorFourierRow sector0 = C3Fourier.chi0
sectorFourierRow sector1 = C3Fourier.chi1
sectorFourierRow sector2 = C3Fourier.chi2

sector1ConjugateIsSector2 :
  C3Fourier.conjugateRow (sectorFourierRow sector1) ≡ sectorFourierRow sector2
sector1ConjugateIsSector2 = C3Fourier.chi1ConjugateIsChi2

sector2ConjugateIsSector1 :
  C3Fourier.conjugateRow (sectorFourierRow sector2) ≡ sectorFourierRow sector1
sector2ConjugateIsSector1 = C3Fourier.chi2ConjugateIsChi1

record PhysicalMolecularC3Action
  (S : Chemistry369.ChemistryHyperfibreSystem) : Set₁ where
  constructor physicalMolecularC3Action
  field
    time : Chemistry369.Time S
    molecularState : Chemistry369.MolecularStateAt S time
    Rotation : Set
    identityRotation : Rotation
    generatorRotation : Rotation
    compose : Rotation → Rotation → Rotation
    act : Rotation → Chemistry369.MolecularStateAt S time → Chemistry369.MolecularStateAt S time
    generatorCubedIsIdentity : Set
    molecularGeometryPreserved : Set
    bondStructurePreserved : Set
    chargeAndElectronCompatibilityPreserved : Set
    environmentCompatible : Set
    physicalSymmetryIdentification : Set
    sourceOrMeasurementReference : String

record ChemistryC3SectorDecomposition
  {S : Chemistry369.ChemistryHyperfibreSystem}
  (A : PhysicalMolecularC3Action S) : Set₁ where
  constructor chemistryC3SectorDecomposition
  field
    State : Set
    stateFromMolecularFibre : State
    sectorOf : State → C3Sector
    SectorWeight : C3Sector → Nat
    sector0Weight : Nat
    sector1Weight : Nat
    sector2Weight : Nat
    weightsMatch :
      (SectorWeight sector0 ≡ sector0Weight)
      × ((SectorWeight sector1 ≡ sector1Weight)
      × (SectorWeight sector2 ≡ sector2Weight))
    fourierRowOf : C3Sector → C3Fourier.FourierRow
    fourierRowsCanonical :
      (sector : C3Sector) → fourierRowOf sector ≡ sectorFourierRow sector
    c3FourierEquivariance : Set
    phaseConventionReference : String

record C3ResolvedReactionTransition
  {S : Chemistry369.ChemistryHyperfibreSystem} : Set₁ where
  constructor c3ResolvedReactionTransition
  field
    sourceTime : Chemistry369.Time S
    targetTime : Chemistry369.Time S
    sourceFibre : Chemistry369.ChemistryFibre S sourceTime
    targetFibre : Chemistry369.ChemistryFibre S targetTime
    sourceC3Action : PhysicalMolecularC3Action S
    targetC3Action : PhysicalMolecularC3Action S
    SourceState : Set
    TargetState : Set
    sourceSector : SourceState → C3Sector
    targetSector : TargetState → C3Sector
    reactionTransition : Chemistry369.ChemistryFibreTransport sourceFibre targetFibre
    elementConservation : Set
    chargeConservation : Set
    electronAccounting : Set
    bondChangeAccounting : Set
    reactionCoordinateOrMechanism : Set
    energeticReceipt : Set
    kineticReceipt : Set
    environmentReceipt : Set

record ChemistryStateCountingEntropyConsumer : Set₁ where
  constructor chemistryStateCountingEntropyConsumer
  field
    Microstate : Set
    CoarseMolecularState : Set
    sector : Microstate → C3Sector
    microstateCount : CoarseMolecularState → Nat
    probabilityWeight : Microstate → Set
    entropyObservable : Set
    physicalEntropyIdentification : Set
    environmentAndTemperatureIdentification : Set
    volumeOrAreaMeasureIfDensityClaimed : Set

record ChemistryC3MonsterBoundary : Set where
  constructor chemistryC3MonsterBoundary
  field
    global369TernaryEncodingImpliesMolecularC3Symmetry : Bool
    global369TernaryEncodingImpliesMolecularC3SymmetryIsFalse :
      global369TernaryEncodingImpliesMolecularC3Symmetry ≡ false
    c3MolecularSectorImpliesMonsterModule : Bool
    c3MolecularSectorImpliesMonsterModuleIsFalse :
      c3MolecularSectorImpliesMonsterModule ≡ false
    equalSectorDimensionImpliesRepresentationIntertwiner : Bool
    equalSectorDimensionImpliesRepresentationIntertwinerIsFalse :
      equalSectorDimensionImpliesRepresentationIntertwiner ≡ false
    molecularStateCountIsThermodynamicEntropyWithoutAdapter : Bool
    molecularStateCountIsThermodynamicEntropyWithoutAdapterIsFalse :
      molecularStateCountIsThermodynamicEntropyWithoutAdapter ≡ false
    molecularEntropyImpliesPhysicalGravity : Bool
    molecularEntropyImpliesPhysicalGravityIsFalse :
      molecularEntropyImpliesPhysicalGravity ≡ false
    reactionSectorLabelDeterminesReactionPath : Bool
    reactionSectorLabelDeterminesReactionPathIsFalse :
      reactionSectorLabelDeterminesReactionPath ≡ false
    explicitC3ActionRequired : Bool
    explicitC3ActionRequiredIsTrue : explicitC3ActionRequired ≡ true
    exactFourierCarrierRequired : Bool
    exactFourierCarrierRequiredIsTrue : exactFourierCarrierRequired ≡ true
    explicitMonsterIntertwinerRequired : Bool
    explicitMonsterIntertwinerRequiredIsTrue :
      explicitMonsterIntertwinerRequired ≡ true

canonicalChemistryC3MonsterBoundary : ChemistryC3MonsterBoundary
canonicalChemistryC3MonsterBoundary =
  chemistryC3MonsterBoundary
    false refl false refl false refl false refl false refl false refl
    true refl true refl true refl

existingChemistryPromotionBoundary : Chemistry369.AtomicChemistryCrossPollinationBoundary
existingChemistryPromotionBoundary = Chemistry369.canonicalAtomicChemistryCrossPollinationBoundary

existingMonsterStateCountingBoundary : MonsterEntropy.StateCountingEntropyBoundary
existingMonsterStateCountingBoundary = MonsterEntropy.canonicalStateCountingEntropyBoundary

ammoniaC3GeometryFixture : NH3.AmmoniaC3Fixture
ammoniaC3GeometryFixture = NH3.canonicalAmmoniaC3Fixture

ammoniaElectronicSymmetryReceipt : NH3Electronic.NeutralElectronicReceipt
ammoniaElectronicSymmetryReceipt = NH3Electronic.canonicalNeutralElectronicReceipt

ammoniaProtonationStoichiometry : NH3Protonation.ProtonationStoichiometry
ammoniaProtonationStoichiometry = NH3Protonation.canonicalProtonationStoichiometry

ammoniaProtonationThermochemistry : NH3Protonation.ProtonationThermochemistry
ammoniaProtonationThermochemistry = NH3Protonation.canonicalProtonationThermochemistry

h3AmmoniaMeasuredKinetics : H3Transfer.H3AmmoniaKineticReceipt
h3AmmoniaMeasuredKinetics = H3Transfer.canonicalH3AmmoniaKineticReceipt

record ChemistryC3MaxCutStatus : Set where
  constructor chemistryC3MaxCutStatus
  field
    atomicToReactionFibreExists : Bool
    atomicToReactionFibreExistsIsTrue : atomicToReactionFibreExists ≡ true
    c3ConsumerInterfaceExists : Bool
    c3ConsumerInterfaceExistsIsTrue : c3ConsumerInterfaceExists ≡ true
    exactC3FourierCarrierConsumed : Bool
    exactC3FourierCarrierConsumedIsTrue : exactC3FourierCarrierConsumed ≡ true
    sourceBackedSameObjectC3GeometryFixturePaid : Bool
    sourceBackedSameObjectC3GeometryFixturePaidIsTrue :
      sourceBackedSameObjectC3GeometryFixturePaid ≡ true
    sourceBackedElectronicIrrepCoordinatesPaid : Bool
    sourceBackedElectronicIrrepCoordinatesPaidIsTrue :
      sourceBackedElectronicIrrepCoordinatesPaid ≡ true
    sourceBackedProtonationStoichiometryPaid : Bool
    sourceBackedProtonationStoichiometryPaidIsTrue :
      sourceBackedProtonationStoichiometryPaid ≡ true
    sourceBackedProtonationThermochemistryPaid : Bool
    sourceBackedProtonationThermochemistryPaidIsTrue :
      sourceBackedProtonationThermochemistryPaid ≡ true
    productsByproductsReactionFixturePaid : Bool
    productsByproductsReactionFixturePaidIsTrue :
      productsByproductsReactionFixturePaid ≡ true
    sameReactionQuantitativeKineticsPaid : Bool
    sameReactionQuantitativeKineticsPaidIsTrue :
      sameReactionQuantitativeKineticsPaid ≡ true
    fullElectronicMolecularC3ActionInstantiated : Bool
    fullElectronicMolecularC3ActionInstantiatedIsFalse :
      fullElectronicMolecularC3ActionInstantiated ≡ false
    fullC3ResolvedReactionTransportInstantiated : Bool
    fullC3ResolvedReactionTransportInstantiatedIsFalse :
      fullC3ResolvedReactionTransportInstantiated ≡ false
    microscopicTransitionPathPaid : Bool
    microscopicTransitionPathPaidIsFalse :
      microscopicTransitionPathPaid ≡ false
    electronResolvedReactionEnergeticsUniversal : Bool
    electronResolvedReactionEnergeticsUniversalIsFalse :
      electronResolvedReactionEnergeticsUniversal ≡ false

canonicalChemistryC3MaxCutStatus : ChemistryC3MaxCutStatus
canonicalChemistryC3MaxCutStatus =
  chemistryC3MaxCutStatus
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
