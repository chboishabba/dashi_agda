module DASHI.Biology.SpectralGrokkingLatticeExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Finite Fourier/rotation carrier for the modular-addition mechanism observed
-- in grokking studies.

data Phase3 : Set where
  phase0 : Phase3
  phase120 : Phase3
  phase240 : Phase3

addPhase : Phase3 → Phase3 → Phase3
addPhase phase0 y = y
addPhase phase120 phase0 = phase120
addPhase phase120 phase120 = phase240
addPhase phase120 phase240 = phase0
addPhase phase240 phase0 = phase240
addPhase phase240 phase120 = phase0
addPhase phase240 phase240 = phase120

phaseAdditionAssociative :
  (a b c : Phase3) → addPhase (addPhase a b) c ≡ addPhase a (addPhase b c)
phaseAdditionAssociative phase0 b c = refl
phaseAdditionAssociative phase120 phase0 c = refl
phaseAdditionAssociative phase120 phase120 phase0 = refl
phaseAdditionAssociative phase120 phase120 phase120 = refl
phaseAdditionAssociative phase120 phase120 phase240 = refl
phaseAdditionAssociative phase120 phase240 phase0 = refl
phaseAdditionAssociative phase120 phase240 phase120 = refl
phaseAdditionAssociative phase120 phase240 phase240 = refl
phaseAdditionAssociative phase240 phase0 c = refl
phaseAdditionAssociative phase240 phase120 phase0 = refl
phaseAdditionAssociative phase240 phase120 phase120 = refl
phaseAdditionAssociative phase240 phase120 phase240 = refl
phaseAdditionAssociative phase240 phase240 phase0 = refl
phaseAdditionAssociative phase240 phase240 phase120 = refl
phaseAdditionAssociative phase240 phase240 phase240 = refl

TriadicPhasePair : Set
TriadicPhasePair = Phase3 × Phase3

phasePairStateCount : Nat
phasePairStateCount = 3 * 3

phasePairStateCountIsNine : phasePairStateCount ≡ 9
phasePairStateCountIsNine = refl

------------------------------------------------------------------------
-- Finite graph-Laplacian surrogate.  The mode table is the exact spectrum of
-- a three-cycle up to basis choice: one constant mode and two contrast modes.

data LaplacianMode3 : Set where
  constantMode : LaplacianMode3
  cosineMode : LaplacianMode3
  sineMode : LaplacianMode3

laplacianEigenvalue : LaplacianMode3 → Nat
laplacianEigenvalue constantMode = 0
laplacianEigenvalue cosineMode = 3
laplacianEigenvalue sineMode = 3

constantModeHasZeroEigenvalue : laplacianEigenvalue constantMode ≡ 0
constantModeHasZeroEigenvalue = refl

contrastModesAreDegenerate :
  laplacianEigenvalue cosineMode ≡ laplacianEigenvalue sineMode
contrastModesAreDegenerate = refl

natDistance : Nat → Nat → Nat
natDistance a b = (a ∸ b) + (b ∸ a)

squareNat : Nat → Nat
squareNat n = n * n

cycleEnergy3 : Nat × Nat × Nat → Nat
cycleEnergy3 (a , b , c) =
  squareNat (natDistance a b)
  + squareNat (natDistance b c)
  + squareNat (natDistance c a)

constantSignalHasZeroLaplacianEnergy : cycleEnergy3 (2 , 2 , 2) ≡ 0
constantSignalHasZeroLaplacianEnergy = refl

contrastSignalHasPositiveFiniteEnergy : cycleEnergy3 (0 , 1 , 2) ≡ 6
contrastSignalHasPositiveFiniteEnergy = refl

------------------------------------------------------------------------
-- Grokking phases and representation compression.

data GrokkingPhase : Set where
  memorisationPhase : GrokkingPhase
  circuitFormationPhase : GrokkingPhase
  cleanupPhase : GrokkingPhase

irregularComponentCount : GrokkingPhase → Nat
irregularComponentCount memorisationPhase = 9
irregularComponentCount circuitFormationPhase = 6
irregularComponentCount cleanupPhase = 0

symmetryAdaptedComponentCount : GrokkingPhase → Nat
symmetryAdaptedComponentCount memorisationPhase = 0
symmetryAdaptedComponentCount circuitFormationPhase = 3
symmetryAdaptedComponentCount cleanupPhase = 3

cleanupRemovesIrregularComponents :
  irregularComponentCount cleanupPhase ≡ 0
cleanupRemovesIrregularComponents = refl

cleanupRetainsThreeSymmetryModes :
  symmetryAdaptedComponentCount cleanupPhase ≡ 3
cleanupRetainsThreeSymmetryModes = refl

------------------------------------------------------------------------
-- Exceptional lattice dimensions are candidate representation geometries,
-- not consequences of the finite grokking witness.

data ExceptionalLattice : Set where
  E8Lattice : ExceptionalLattice
  LeechLattice : ExceptionalLattice

latticeDimension : ExceptionalLattice → Nat
latticeDimension E8Lattice = 8
latticeDimension LeechLattice = 24

E8DimensionIsEight : latticeDimension E8Lattice ≡ 8
E8DimensionIsEight = refl

LeechDimensionIsTwentyFour : latticeDimension LeechLattice ≡ 24
LeechDimensionIsTwentyFour = refl

record RepresentationGeometry : Set where
  constructor representationGeometry
  field
    ambientDimension : Nat
    modeCount : Nat
    symmetryCompressed : Bool
    graphEnergy : Nat

open RepresentationGeometry public

canonicalGrokkedGeometry : RepresentationGeometry
canonicalGrokkedGeometry = representationGeometry 2 3 true 6

record SpectralGrokkingBoundary : Set where
  constructor spectralGrokkingBoundary
  field
    phasePairBasisIsQuantumSuperposition : Bool
    phasePairBasisIsQuantumSuperpositionIsFalse :
      phasePairBasisIsQuantumSuperposition ≡ false

    grokkingForcesE8OrLeechGeometry : Bool
    grokkingForcesE8OrLeechGeometryIsFalse :
      grokkingForcesE8OrLeechGeometry ≡ false

    graphLaplacianIsTheWholeBrain : Bool
    graphLaplacianIsTheWholeBrainIsFalse :
      graphLaplacianIsTheWholeBrain ≡ false

    FourierRotationMechanismIsRepresented : Bool
    FourierRotationMechanismIsRepresentedIsTrue :
      FourierRotationMechanismIsRepresented ≡ true

open SpectralGrokkingBoundary public

canonicalSpectralGrokkingBoundary : SpectralGrokkingBoundary
canonicalSpectralGrokkingBoundary =
  spectralGrokkingBoundary false refl false refl false refl true refl
