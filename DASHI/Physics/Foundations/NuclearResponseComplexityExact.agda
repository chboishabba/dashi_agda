module DASHI.Physics.Foundations.NuclearResponseComplexityExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Proton-neutron asymmetry penalty.

natDistance : Nat → Nat → Nat
natDistance x y = (x ∸ y) + (y ∸ x)

asymmetryNumerator : Nat → Nat → Nat
asymmetryNumerator neutrons protons =
  natDistance neutrons protons * natDistance neutrons protons

balancedAsymmetryVanishing : asymmetryNumerator 4 4 ≡ 0
balancedAsymmetryVanishing = refl

imbalancedAsymmetryIsSixteen : asymmetryNumerator 6 2 ≡ 16
imbalancedAsymmetryIsSixteen = refl

record AsymmetryRatio : Set where
  constructor asymmetryRatio
  field
    numerator : Nat
    massNumber : Nat

open AsymmetryRatio public

canonicalAsymmetryRatio : AsymmetryRatio
canonicalAsymmetryRatio = asymmetryRatio (asymmetryNumerator 6 2) 8

canonicalAsymmetryNumeratorIsSixteen :
  numerator canonicalAsymmetryRatio ≡ 16
canonicalAsymmetryNumeratorIsSixteen = refl

------------------------------------------------------------------------
-- Large shell gaps suppress finite low-energy response.

data GapMagnitude : Set where
  gapOne : GapMagnitude
  gapTwo : GapMagnitude
  gapFour : GapMagnitude

responseBound : GapMagnitude → Nat
responseBound gapOne = 4
responseBound gapTwo = 2
responseBound gapFour = 1

largeGapHasSmallerResponseBound :
  responseBound gapFour ≤ responseBound gapOne
largeGapHasSmallerResponseBound = s≤s z≤n

record ParticleHoleResponse : Set where
  constructor particleHoleResponse
  field
    gap : GapMagnitude
    matrixElementBudget : Nat
    certifiedResponseBound : Nat

open ParticleHoleResponse public

closedShellResponse : ParticleHoleResponse
closedShellResponse = particleHoleResponse gapFour 4 1

openShellResponse : ParticleHoleResponse
openShellResponse = particleHoleResponse gapOne 4 4

closedShellResponseIsOne :
  certifiedResponseBound closedShellResponse ≡ 1
closedShellResponseIsOne = refl

openShellResponseIsFour :
  certifiedResponseBound openShellResponse ≡ 4
openShellResponseIsFour = refl

------------------------------------------------------------------------
-- Pair locking reduces the number of independent active occupations only
-- after an explicit pairing model is supplied.

data FermiBoundaryConfiguration : Set where
  fourIndependentOccupations : FermiBoundaryConfiguration
  twoLockedPairs : FermiBoundaryConfiguration

activeOccupationChoices : FermiBoundaryConfiguration → Nat
activeOccupationChoices fourIndependentOccupations = 4
activeOccupationChoices twoLockedPairs = 2

pairLockingReducesActiveChoices :
  activeOccupationChoices twoLockedPairs
  ≤
  activeOccupationChoices fourIndependentOccupations
pairLockingReducesActiveChoices = s≤s (s≤s z≤n)

------------------------------------------------------------------------
-- Model-dependent nuclear state complexity.

record NuclearComplexityProfile : Set where
  constructor nuclearComplexityProfile
  field
    shellComplexity : Nat
    unpairedComplexity : Nat
    shapeComplexity : Nat
    correlationComplexity : Nat

open NuclearComplexityProfile public

totalNuclearComplexity : NuclearComplexityProfile → Nat
totalNuclearComplexity profile =
  shellComplexity profile
  + unpairedComplexity profile
  + shapeComplexity profile
  + correlationComplexity profile

pairedSphericalProfile : NuclearComplexityProfile
pairedSphericalProfile = nuclearComplexityProfile 1 0 1 1

unpairedDeformedProfile : NuclearComplexityProfile
unpairedDeformedProfile = nuclearComplexityProfile 1 2 3 2

pairedSphericalComplexityIsThree :
  totalNuclearComplexity pairedSphericalProfile ≡ 3
pairedSphericalComplexityIsThree = refl

unpairedDeformedComplexityIsEight :
  totalNuclearComplexity unpairedDeformedProfile ≡ 8
unpairedDeformedComplexityIsEight = refl

------------------------------------------------------------------------
-- Energy and complexity remain separate terms unless a probability model
-- assigns weights to both.

record NuclearSelectionWeights : Set where
  constructor nuclearSelectionWeights
  field
    energyWeight : Nat
    complexityWeight : Nat

open NuclearSelectionWeights public

jointNuclearScore :
  NuclearSelectionWeights → Nat → NuclearComplexityProfile → Nat
jointNuclearScore weights energy profile =
  energyWeight weights * energy
  +
  complexityWeight weights * totalNuclearComplexity profile

energyOnlyWeights : NuclearSelectionWeights
energyOnlyWeights = nuclearSelectionWeights 1 0

energyComplexityWeights : NuclearSelectionWeights
energyComplexityWeights = nuclearSelectionWeights 1 1

complexityWeightChangesScore :
  jointNuclearScore energyOnlyWeights 5 pairedSphericalProfile ≡ 5
  ×
  jointNuclearScore energyComplexityWeights 5 pairedSphericalProfile ≡ 8
complexityWeightChangesScore = refl , refl

record NuclearResponseComplexityBoundary : Set where
  constructor nuclearResponseComplexityBoundary
  field
    asymmetryPenaltyComesFromTotalNucleonCountAlone : Bool
    asymmetryPenaltyComesFromTotalNucleonCountAloneIsFalse :
      asymmetryPenaltyComesFromTotalNucleonCountAlone ≡ false

    largeGapForcesZeroSusceptibility : Bool
    largeGapForcesZeroSusceptibilityIsFalse :
      largeGapForcesZeroSusceptibility ≡ false

    pairingReducesComplexityWithoutAttractivePairField : Bool
    pairingReducesComplexityWithoutAttractivePairFieldIsFalse :
      pairingReducesComplexityWithoutAttractivePairField ≡ false

    nuclearEnergyDefinitionallyEqualsStateComplexity : Bool
    nuclearEnergyDefinitionallyEqualsStateComplexityIsFalse :
      nuclearEnergyDefinitionallyEqualsStateComplexity ≡ false

open NuclearResponseComplexityBoundary public

canonicalNuclearResponseComplexityBoundary : NuclearResponseComplexityBoundary
canonicalNuclearResponseComplexityBoundary =
  nuclearResponseComplexityBoundary false refl false refl false refl false refl
