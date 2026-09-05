module DASHI.Analysis.NonArchimedeanSpectralCrossLaneBidiExact where

------------------------------------------------------------------------
-- Cross-lane BIDI x-pollination.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Interop.AdicHypervoxelArgumentTransportBridgeExact as Adic

record SignedBeforeNormDiscipline : Set where
  constructor signedBeforeNormDiscipline
  field
    phasePreservedBeforeProjection : Bool
    conjugateOrSymmetryPairingPrecedesNorm : Bool
    scalarNormCanEraseCancellation : Bool
    dyadicCarrierEqualsC3Carrier : Bool

canonicalSignedBeforeNormDiscipline : SignedBeforeNormDiscipline
canonicalSignedBeforeNormDiscipline =
  signedBeforeNormDiscipline true true true false

c3PairThenNormWitness : (x : C3.Cyclotomic3) →
  C3.multiply x (C3.conjugate x) ≡ C3.embedRational (C3.norm x)
c3PairThenNormWitness = C3.multiplyByConjugateLandsOnNorm

------------------------------------------------------------------------
-- Reuse the adic bridge's exported governance boundary directly.  This keeps
-- the cross-pollination independent of the private alias used inside that
-- module while preserving the exact projected-shadow != definitional-identity
-- discipline.
------------------------------------------------------------------------

adicProjectedShadowIsNotDefinitionalIdentity :
  Adic.AdicArgumentTransportBoundary.projectedShadowEqualsDefinitionalIdentity
    Adic.canonicalAdicArgumentTransportBoundary
  ≡ false
adicProjectedShadowIsNotDefinitionalIdentity = refl

record CrossLaneFirewall : Set where
  constructor crossLaneFirewall
  field
    signedCancellationTransfersStructurally : Bool
    numericalCyclotomicIdentityTransfersAcrossOrders : Bool
    projectedShadowIsDefinitionalIdentity : Bool
    spatialDynamicsFollowsFromCharacterRechart : Bool

canonicalCrossLaneFirewall : CrossLaneFirewall
canonicalCrossLaneFirewall =
  crossLaneFirewall true false false false


data ReverseRepair : Set where
  reopenSignedChannels : ReverseRepair
  constructSameObjectWeld : ReverseRepair
  sharpenScalarBound : ReverseRepair

repairForLostCancellation : ReverseRepair
repairForLostCancellation = reopenSignedChannels

repairForRepresentationJump : ReverseRepair
repairForRepresentationJump = constructSameObjectWeld

lostCancellationIsRepresentationProblem :
  repairForLostCancellation ≡ reopenSignedChannels
lostCancellationIsRepresentationProblem = refl

representationJumpNeedsWeld :
  repairForRepresentationJump ≡ constructSameObjectWeld
representationJumpNeedsWeld = refl
