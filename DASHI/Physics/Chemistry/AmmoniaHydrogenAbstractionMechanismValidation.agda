module DASHI.Physics.Chemistry.AmmoniaHydrogenAbstractionMechanismValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaHydrogenAbstractionMechanismExact as Mechanism

reactionIdentityPaid :
  Mechanism.AbstractionBoundary.sourceBackedReactionIdentityPaid
    Mechanism.canonicalAbstractionBoundary ≡ true
reactionIdentityPaid = refl

analyticalPESPaid :
  Mechanism.AbstractionBoundary.sourceBackedAnalyticalPESPaid
    Mechanism.canonicalAbstractionBoundary ≡ true
analyticalPESPaid = refl

reactionPathTopologyPaid :
  Mechanism.AbstractionBoundary.sourceBackedReactionPathTopologyPaid
    Mechanism.canonicalAbstractionBoundary ≡ true
reactionPathTopologyPaid = refl

wavepacketDynamicsPaid :
  Mechanism.AbstractionBoundary.sourceBackedTimeDependentWavepacketDynamicsPaid
    Mechanism.canonicalAbstractionBoundary ≡ true
wavepacketDynamicsPaid = refl

atomInventoryConserved :
  Mechanism.AbstractionBookkeeping.hydrogenAtomsReactant
    Mechanism.canonicalAbstractionBookkeeping
  ≡ Mechanism.AbstractionBookkeeping.hydrogenAtomsProduct
      Mechanism.canonicalAbstractionBookkeeping
atomInventoryConserved = refl

full369HyperformBindingPaid :
  Mechanism.AbstractionBoundary.literal369AtomicReactionBindingPaid
    Mechanism.canonicalAbstractionBoundary ≡ true
full369HyperformBindingPaid = refl

uniqueMicroscopicTrajectoryNotClaimed :
  Mechanism.AbstractionBoundary.uniqueMicroscopicTrajectoryDetermined
    Mechanism.canonicalAbstractionBoundary ≡ false
uniqueMicroscopicTrajectoryNotClaimed = refl
