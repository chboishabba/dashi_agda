module DASHI.Analysis.NonArchimedeanSpectralCrossLaneBidiExact where

------------------------------------------------------------------------
-- Cross-lane BIDI x-pollination.
--
-- The source repo contributes a compact finite example of a general DASHI
-- discipline already used elsewhere:
--
--   preserve phase / sign / channel data
--   -> pair or quotient by the relevant symmetry
--   -> only then project to a scalar invariant.
--
-- This module exports that structural law without identifying the dyadic
-- cyclotomic carrier with the existing C3 carrier, and without identifying
-- character-space transport with spatial dynamics.
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

------------------------------------------------------------------------
-- Existing C3 owner supplies an exact witness that the structural law is
-- already native to DASHI: x * conjugate(x) lands on the norm axis only after
-- conjugation has been retained explicitly.
------------------------------------------------------------------------

c3PairThenNormWitness : (x : C3.Cyclotomic3) →
  C3.multiply x (C3.conjugate x) ≡ C3.embedRational (C3.norm x)
c3PairThenNormWitness = C3.multiplyByConjugateLandsOnNorm

------------------------------------------------------------------------
-- Existing adic bridge supplies the same-object firewall: an exact transport
-- relation may still only be a projected shadow of another representation.
------------------------------------------------------------------------

adicProjectedShadowFirewall :
  ∀ {H A B G S} →
  (bridge : Adic.Adic.HypervoxelAdicYoungFibonacciBridge H A B G S) →
  Adic.Adic.HypervoxelAdicYoungFibonacciBridge.relation bridge
    ≡ Adic.Adic.projectedShadow
adicProjectedShadowFirewall = Adic.adicBridgeRemainsProjectedShadow

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

------------------------------------------------------------------------
-- BIDI export: if a downstream consumer asks for a scalar norm theorem but
-- cancellation depends on signed/conjugate channels, the reverse search must
-- reopen the pre-norm representation rather than estimate the scalar harder.
------------------------------------------------------------------------

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
