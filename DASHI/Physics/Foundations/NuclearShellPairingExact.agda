module DASHI.Physics.Foundations.NuclearShellPairingExact where

open import DASHI.Core.Prelude

import DASHI.Algebra.Trit.OddEvenLaneTritBridge as ParityTrit

------------------------------------------------------------------------
-- A nucleus has separate proton and neutron occupancy sectors.

data NucleonSector : Set where
  protonSector : NucleonSector
  neutronSector : NucleonSector

data GapClass : Set where
  smallGap : GapClass
  largeGap : GapClass

record ShellProfile : Set where
  constructor shellProfile
  field
    sector : NucleonSector
    degeneracy : Nat
    occupancy : Nat
    occupancyBound : occupancy ≤ degeneracy
    fullyOccupied : Bool
    gapClass : GapClass

open ShellProfile public

data ClosureStatus : Set where
  openShell : ClosureStatus
  closedWithoutLargeGap : ClosureStatus
  magicClosure : ClosureStatus

closureStatus : ShellProfile → ClosureStatus
closureStatus
  (shellProfile sector capacity occupied bound false gap) = openShell
closureStatus
  (shellProfile sector capacity occupied bound true smallGap) =
  closedWithoutLargeGap
closureStatus
  (shellProfile sector capacity occupied bound true largeGap) =
  magicClosure

canonicalProtonClosure : ShellProfile
canonicalProtonClosure =
  shellProfile protonSector 2 2 ≤-refl true largeGap

canonicalNeutronClosure : ShellProfile
canonicalNeutronClosure =
  shellProfile neutronSector 2 2 ≤-refl true largeGap

protonClosureIsMagic :
  closureStatus canonicalProtonClosure ≡ magicClosure
protonClosureIsMagic = refl

neutronClosureIsMagic :
  closureStatus canonicalNeutronClosure ≡ magicClosure
neutronClosureIsMagic = refl

record DoubleClosure : Set where
  constructor doubleClosure
  field
    protonProfile : ShellProfile
    neutronProfile : ShellProfile
    protonMagic : closureStatus protonProfile ≡ magicClosure
    neutronMagic : closureStatus neutronProfile ≡ magicClosure

canonicalDoubleClosure : DoubleClosure
canonicalDoubleClosure =
  doubleClosure canonicalProtonClosure canonicalNeutronClosure refl refl

------------------------------------------------------------------------
-- Shell evolution with composition.

data CompositionRegime : Set where
  balancedComposition : CompositionRegime
  neutronRichComposition : CompositionRegime
  protonRichComposition : CompositionRegime

compositionGap : CompositionRegime → NucleonSector → GapClass
compositionGap balancedComposition protonSector = largeGap
compositionGap balancedComposition neutronSector = largeGap
compositionGap neutronRichComposition protonSector = smallGap
compositionGap neutronRichComposition neutronSector = largeGap
compositionGap protonRichComposition protonSector = largeGap
compositionGap protonRichComposition neutronSector = smallGap

occupancyCanChangeEffectiveGap :
  compositionGap balancedComposition protonSector ≡ largeGap
  ×
  compositionGap neutronRichComposition protonSector ≡ smallGap
occupancyCanChangeEffectiveGap = refl , refl

------------------------------------------------------------------------
-- Pairing requires an attractive interaction and time-reversed partner data.

data PairingInteraction : Set where
  noAttractivePairing : PairingInteraction
  attractivePairing : PairingInteraction

data PairingStatus : Set where
  noPairingPreference : PairingStatus
  pairedStateFavoured : PairingStatus

pairingStatus : PairingInteraction → PairingStatus
pairingStatus noAttractivePairing = noPairingPreference
pairingStatus attractivePairing = pairedStateFavoured

pairingRequiresAttraction :
  pairingStatus attractivePairing ≡ pairedStateFavoured
  ×
  pairingStatus noAttractivePairing ≡ noPairingPreference
pairingRequiresAttraction = refl , refl

data NumberParity : Set where
  evenNumber : NumberParity
  oddNumber : NumberParity

record NuclearParitySector : Set where
  constructor nuclearParitySector
  field
    protonParity : NumberParity
    neutronParity : NumberParity

open NuclearParitySector public

blockedLikeParticleSectors : NuclearParitySector → Nat
blockedLikeParticleSectors
  (nuclearParitySector evenNumber evenNumber) = 0
blockedLikeParticleSectors
  (nuclearParitySector oddNumber evenNumber) = 1
blockedLikeParticleSectors
  (nuclearParitySector evenNumber oddNumber) = 1
blockedLikeParticleSectors
  (nuclearParitySector oddNumber oddNumber) = 2

evenEvenSector : NuclearParitySector
evenEvenSector = nuclearParitySector evenNumber evenNumber

oddMassSector : NuclearParitySector
oddMassSector = nuclearParitySector oddNumber evenNumber

oddOddSector : NuclearParitySector
oddOddSector = nuclearParitySector oddNumber oddNumber

evenEvenHasNoBlockedSector :
  blockedLikeParticleSectors evenEvenSector ≡ 0
evenEvenHasNoBlockedSector = refl

oddMassHasOneBlockedSector :
  blockedLikeParticleSectors oddMassSector ≡ 1
oddMassHasOneBlockedSector = refl

oddOddHasTwoBlockedSectors :
  blockedLikeParticleSectors oddOddSector ≡ 2
oddOddHasTwoBlockedSectors = refl

pairingPenalty : PairingInteraction → NuclearParitySector → Nat
pairingPenalty noAttractivePairing parity = 0
pairingPenalty attractivePairing parity = blockedLikeParticleSectors parity

oddOddPairingPenaltyIsTwo :
  pairingPenalty attractivePairing oddOddSector ≡ 2
oddOddPairingPenaltyIsTwo = refl

------------------------------------------------------------------------
-- Observable odd-even staggering and separation-energy curvature.

natDistance : Nat → Nat → Nat
natDistance x y = (x ∸ y) + (y ∸ x)

threePointStaggering : Nat → Nat → Nat → Nat
threePointStaggering previous current next =
  natDistance (previous + next) (2 * current)

canonicalPairingStaggering :
  threePointStaggering 4 3 4 ≡ 2
canonicalPairingStaggering = refl

secondSeparationCurvature : Nat → Nat → Nat
secondSeparationCurvature below above = natDistance below above

canonicalMagicCurvature :
  secondSeparationCurvature 6 2 ≡ 4
canonicalMagicCurvature = refl

------------------------------------------------------------------------
-- Parity is an independent two-state sector.  The existing odd/even-to-trit
-- adapter may encode it, but the ternary carrier does not create pairing.

parityEncodingCarrier : Set
parityEncodingCarrier = ParityTrit.OddEvenLaneClass

record NuclearShellPairingBoundary : Set where
  constructor nuclearShellPairingBoundary
  field
    pauliExclusionDeterminesObservedMagicNumbers : Bool
    pauliExclusionDeterminesObservedMagicNumbersIsFalse :
      pauliExclusionDeterminesObservedMagicNumbers ≡ false

    shellCardinalityAloneDeterminesMagicity : Bool
    shellCardinalityAloneDeterminesMagicityIsFalse :
      shellCardinalityAloneDeterminesMagicity ≡ false

    pairingIsForcedByExclusionWithoutAttraction : Bool
    pairingIsForcedByExclusionWithoutAttractionIsFalse :
      pairingIsForcedByExclusionWithoutAttraction ≡ false

    protonAndNeutronClosuresAreOneTotalOccupancyClaim : Bool
    protonAndNeutronClosuresAreOneTotalOccupancyClaimIsFalse :
      protonAndNeutronClosuresAreOneTotalOccupancyClaim ≡ false

    binaryParityIsIntrinsicToTernaryCardinality : Bool
    binaryParityIsIntrinsicToTernaryCardinalityIsFalse :
      binaryParityIsIntrinsicToTernaryCardinality ≡ false

open NuclearShellPairingBoundary public

canonicalNuclearShellPairingBoundary : NuclearShellPairingBoundary
canonicalNuclearShellPairingBoundary =
  nuclearShellPairingBoundary false refl false refl false refl false refl false refl
