module DASHI.Physics.Foundations.AtomicFermionShellExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Core.CandidateFunctionalCore as Candidate

------------------------------------------------------------------------
-- Atomic identity and electronic state are different data.

data SpinState : Set where
  spinDown : SpinState
  spinUp : SpinState

record AtomicSpecies : Set where
  constructor atomicSpecies
  field
    protonNumber : Nat
    neutronNumber : Nat
    electronNumber : Nat

open AtomicSpecies public

neutral : AtomicSpecies → Set
neutral atom = electronNumber atom ≡ protonNumber atom

argonLikeSpecies : AtomicSpecies
argonLikeSpecies = atomicSpecies 18 22 18

argonLikeSpeciesIsNeutral : neutral argonLikeSpecies
argonLikeSpeciesIsNeutral = refl

record ElectronicConfiguration : Set where
  constructor electronicConfiguration
  field
    configurationLabel : Nat
    occupiedStateCount : Nat

open ElectronicConfiguration public

configurationA : ElectronicConfiguration
configurationA = electronicConfiguration 0 18

configurationB : ElectronicConfiguration
configurationB = electronicConfiguration 1 18

sameElementCanCarryDifferentConfigurationLabels :
  protonNumber argonLikeSpecies ≡ 18
  ×
  configurationLabel configurationA ≡ 0
  ×
  configurationLabel configurationB ≡ 1
sameElementCanCarryDifferentConfigurationLabels = refl , (refl , refl)

------------------------------------------------------------------------
-- Orbital labels are imported representation data, not outputs of a triadic
-- alphabet.  Once the rotational/spin representation is supplied, capacities
-- are exact combinatorial consequences.

record OrbitalLabel : Set where
  constructor orbitalLabel
  field
    principalIndex : Nat
    angularIndex : Nat
    magneticIndexCode : Nat
    spin : SpinState

open OrbitalLabel public

subshellCapacity : Nat → Nat
subshellCapacity angularMomentum =
  2 * (2 * angularMomentum + 1)

shellCapacity : Nat → Nat
shellCapacity principal =
  2 * (principal * principal)

sSubshellCapacityIsTwo : subshellCapacity 0 ≡ 2
sSubshellCapacityIsTwo = refl

pSubshellCapacityIsSix : subshellCapacity 1 ≡ 6
pSubshellCapacityIsSix = refl

dSubshellCapacityIsTen : subshellCapacity 2 ≡ 10
dSubshellCapacityIsTen = refl

firstShellCapacityIsTwo : shellCapacity 1 ≡ 2
firstShellCapacityIsTwo = refl

secondShellCapacityIsEight : shellCapacity 2 ≡ 8
secondShellCapacityIsEight = refl

thirdShellCapacityIsEighteen : shellCapacity 3 ≡ 18
thirdShellCapacityIsEighteen = refl

record FermionicOccupancy : Set where
  constructor fermionicOccupancy
  field
    capacity : Nat
    occupied : Nat
    exclusionBound : occupied ≤ capacity

open FermionicOccupancy public

closedPSubshell : FermionicOccupancy
closedPSubshell = fermionicOccupancy 6 6 ≤-refl

closedPSubshellSaturatesCapacity :
  occupied closedPSubshell ≡ capacity closedPSubshell
closedPSubshellSaturatesCapacity = refl

------------------------------------------------------------------------
-- Corrected finite Z=18 signature supplied in the attachment.

argonOccupationSignature : List Nat
argonOccupationSignature =
  0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []

canonicalArgonSignature : List Nat
canonicalArgonSignature =
  0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []

argonSignatureCorrectionIsExact :
  argonOccupationSignature ≡ canonicalArgonSignature
argonSignatureCorrectionIsExact = refl

------------------------------------------------------------------------
-- A toy orbital score may reorder levels when its parameter changes.  This is
-- an exact crossing witness, not a physical many-electron energy theorem.

data ToyOrbital : Set where
  orbital3s : ToyOrbital
  orbital3p : ToyOrbital
  orbital4s : ToyOrbital
  orbital3d : ToyOrbital

data OrderingRegime : Set where
  principalDominatedRegime : OrderingRegime
  angularPenaltyRegime : OrderingRegime

toyScore : OrderingRegime → ToyOrbital → Nat
toyScore principalDominatedRegime orbital3s = 3
toyScore principalDominatedRegime orbital3p = 3
toyScore principalDominatedRegime orbital4s = 4
toyScore principalDominatedRegime orbital3d = 3
toyScore angularPenaltyRegime orbital3s = 3
toyScore angularPenaltyRegime orbital3p = 4
toyScore angularPenaltyRegime orbital4s = 4
toyScore angularPenaltyRegime orbital3d = 5

principalRegimeMakesThreeDLowerThanFourS :
  toyScore principalDominatedRegime orbital3d
  ≤
  toyScore principalDominatedRegime orbital4s
principalRegimeMakesThreeDLowerThanFourS =
  s≤s (s≤s (s≤s z≤n))

angularPenaltyMakesFourSLowerThanThreeD :
  toyScore angularPenaltyRegime orbital4s
  ≤
  toyScore angularPenaltyRegime orbital3d
angularPenaltyMakesFourSLowerThanThreeD =
  s≤s (s≤s (s≤s (s≤s z≤n)))

------------------------------------------------------------------------
-- Interacting configuration selection and energetic valence.

data ConfigurationCandidate : Set where
  compactConfiguration : ConfigurationCandidate
  promotedConfiguration : ConfigurationCandidate

oneBodyEnergy : ConfigurationCandidate → Nat
oneBodyEnergy compactConfiguration = 4
oneBodyEnergy promotedConfiguration = 3

interactionPenalty : ConfigurationCandidate → Nat
interactionPenalty compactConfiguration = 0
interactionPenalty promotedConfiguration = 3

totalConfigurationEnergy : ConfigurationCandidate → Nat
totalConfigurationEnergy configuration =
  oneBodyEnergy configuration + interactionPenalty configuration

compactWinsAfterInteraction :
  totalConfigurationEnergy compactConfiguration
  ≤
  totalConfigurationEnergy promotedConfiguration
compactWinsAfterInteraction =
  s≤s (s≤s (s≤s (s≤s z≤n)))

data OrbitalActivity : Set where
  inertCoreOrbital : OrbitalActivity
  activeValenceOrbital : OrbitalActivity

activityByEnergyWindow : ToyOrbital → OrbitalActivity
activityByEnergyWindow orbital3s = inertCoreOrbital
activityByEnergyWindow orbital3p = activeValenceOrbital
activityByEnergyWindow orbital4s = activeValenceOrbital
activityByEnergyWindow orbital3d = activeValenceOrbital

highestPrincipalIndexIsNotDefinitionOfValence :
  activityByEnergyWindow orbital3p ≡ activeValenceOrbital
  ×
  activityByEnergyWindow orbital4s ≡ activeValenceOrbital
highestPrincipalIndexIsNotDefinitionOfValence = refl , refl

existingTriadicSheetCarrier : Set
existingTriadicSheetCarrier = Triadic.NineSheet

existingCandidateFunctionalCarrier : Set
existingCandidateFunctionalCarrier = Candidate.CandidateFunctionalSurface

------------------------------------------------------------------------
-- Authority boundary.

record AtomicFermionBoundary : Set where
  constructor atomicFermionBoundary
  field
    electronFillingDefinesElementWithoutNuclearCharge : Bool
    electronFillingDefinesElementWithoutNuclearChargeIsFalse :
      electronFillingDefinesElementWithoutNuclearCharge ≡ false

    orbitalQuantumNumbersFollowFromTriadicCardinalityAlone : Bool
    orbitalQuantumNumbersFollowFromTriadicCardinalityAloneIsFalse :
      orbitalQuantumNumbersFollowFromTriadicCardinalityAlone ≡ false

    pauliAntisymmetryIsASetQuotient : Bool
    pauliAntisymmetryIsASetQuotientIsFalse :
      pauliAntisymmetryIsASetQuotient ≡ false

    toyScoreIsAFirstPrinciplesAtomicHamiltonian : Bool
    toyScoreIsAFirstPrinciplesAtomicHamiltonianIsFalse :
      toyScoreIsAFirstPrinciplesAtomicHamiltonian ≡ false

    randomChoiceOfProtonNumberDerivesAnElement : Bool
    randomChoiceOfProtonNumberDerivesAnElementIsFalse :
      randomChoiceOfProtonNumberDerivesAnElement ≡ false

    shellCapacityProvesActualEnergyOrdering : Bool
    shellCapacityProvesActualEnergyOrderingIsFalse :
      shellCapacityProvesActualEnergyOrdering ≡ false

open AtomicFermionBoundary public

canonicalAtomicFermionBoundary : AtomicFermionBoundary
canonicalAtomicFermionBoundary =
  atomicFermionBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
