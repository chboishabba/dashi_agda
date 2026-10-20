module DASHI.Analysis.RiemannSSP15ProducerMarkedClimbingGymBridgeExact where

------------------------------------------------------------------------
-- PRODUCER-MARKED RH / SSP15 -> SIGNED RADIX ROOT WALL
--
-- Current master already owns the conditional producer-side compilation
--
--   producer-marked RH role
--     -> pointed signed SSP/FRACTRAN seed.
--
-- The climbing-gym wall consumes exactly that pointed carrier.  Therefore the
-- lawful cross-pollination is a thin adapter into the ROOT of the selected
-- prime's existing radix tree, not a new RH/Monster identification.
--
-- This pays the shared finite carrier and role-polarity transport only.  It
-- does not identify the producer-side RH role certificate with the supplied
-- JMD hole/zero observations, and it does not construct the analytic phase or
-- hole-height formulas.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Analysis.RiemannSSP15DepthFiveRoleCodecExact as Codec
import DASHI.Analysis.RiemannSSP15FilteredProvenanceCapstoneExact as Capstone
import DASHI.Analysis.RiemannSSP15ProducerMarkedSignedFRACTRANExact as Producer
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Quotient
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.RadixValuationStageBridge as Radix
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as Branch
import DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact as Gym
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- 1. Producer-marked code -> exact climbing-gym root wall.
------------------------------------------------------------------------

producerMarkedRootWall :
  {certificate : Capstone.PrimitiveRowProducerRoleCertificate} ->
  Capstone.ProducerMarkedSSP15Code certificate ->
  Gym.SignedRadixWallState 0
producerMarkedRootWall code =
  Gym.signed-radix-wall-state
    (Branch.pointedLane (Producer.producerMarkedSeed code))
    Radix.radial-root

producerMarkedRootWallPrimeExact :
  {certificate : Capstone.PrimitiveRowProducerRoleCertificate} ->
  (code : Capstone.ProducerMarkedSSP15Code certificate) ->
  Gym.wallPrime (producerMarkedRootWall code)
  ≡
  Branch.selectedPrime (Branch.pointedLane (Producer.producerMarkedSeed code))
producerMarkedRootWallPrimeExact code = refl

producerMarkedRootWallMultiplicityExact :
  {certificate : Capstone.PrimitiveRowProducerRoleCertificate} ->
  (code : Capstone.ProducerMarkedSSP15Code certificate) ->
  Gym.wallMultiplicity (producerMarkedRootWall code)
  ≡
  Branch.signedMultiplicity (Branch.pointedLane (Producer.producerMarkedSeed code))
producerMarkedRootWallMultiplicityExact code = refl

------------------------------------------------------------------------
-- 2. RH role polarity is exactly the wall's signed/FRACTRAN orientation.
------------------------------------------------------------------------

originRoleRootWallOrientationInverse :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  (mode : Quotient.ComplementMode5) ->
  Gym.wallOrientation
    (producerMarkedRootWall
      (Capstone.canonicalProducerMarkedCode
        certificate mode Codec.originRole))
  ≡ Signed.inverseOrientation
originRoleRootWallOrientationInverse =
  Producer.originRoleHyperformOrientationInverse

jRoleRootWallOrientationMediated :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  (mode : Quotient.ComplementMode5) ->
  Gym.wallOrientation
    (producerMarkedRootWall
      (Capstone.canonicalProducerMarkedCode
        certificate mode Codec.jRole))
  ≡ Signed.mediatedOrientation
jRoleRootWallOrientationMediated =
  Producer.jRoleHyperformOrientationMediated

sRoleRootWallOrientationForward :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  (mode : Quotient.ComplementMode5) ->
  Gym.wallOrientation
    (producerMarkedRootWall
      (Capstone.canonicalProducerMarkedCode
        certificate mode Codec.sRole))
  ≡ Signed.forwardOrientation
sRoleRootWallOrientationForward =
  Producer.sRoleHyperformOrientationForward

------------------------------------------------------------------------
-- 3. Neutral j role still retains the selected Ogg lane on the root wall.
------------------------------------------------------------------------

jMode09RootWallPrimeIsThree :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  Gym.wallPrime
    (producerMarkedRootWall
      (Capstone.canonicalProducerMarkedCode
        certificate Quotient.mode09 Codec.jRole))
  ≡ Lane.p3
jMode09RootWallPrimeIsThree =
  Producer.jMode09PrimeIsThree

jMode18RootWallPrimeIsEleven :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  Gym.wallPrime
    (producerMarkedRootWall
      (Capstone.canonicalProducerMarkedCode
        certificate Quotient.mode18 Codec.jRole))
  ≡ Lane.p11
jMode18RootWallPrimeIsEleven =
  Producer.jMode18PrimeIsEleven

jMode27RootWallPrimeIsNineteen :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  Gym.wallPrime
    (producerMarkedRootWall
      (Capstone.canonicalProducerMarkedCode
        certificate Quotient.mode27 Codec.jRole))
  ≡ Lane.p19
jMode27RootWallPrimeIsNineteen =
  Producer.jMode27PrimeIsNineteen

jMode36RootWallPrimeIsThirtyOne :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  Gym.wallPrime
    (producerMarkedRootWall
      (Capstone.canonicalProducerMarkedCode
        certificate Quotient.mode36 Codec.jRole))
  ≡ Lane.p31
jMode36RootWallPrimeIsThirtyOne =
  Producer.jMode36PrimeIsThirtyOne

jMode45RootWallPrimeIsFiftyNine :
  (certificate : Capstone.PrimitiveRowProducerRoleCertificate) ->
  Gym.wallPrime
    (producerMarkedRootWall
      (Capstone.canonicalProducerMarkedCode
        certificate Quotient.mode45 Codec.jRole))
  ≡ Lane.p59
jMode45RootWallPrimeIsFiftyNine =
  Producer.jMode45PrimeIsFiftyNine

------------------------------------------------------------------------
-- 4. Boundary: same finite carrier does not identify empirical/analytic roles.
------------------------------------------------------------------------

record RiemannSSP15ProducerMarkedClimbingGymBoundary : Set where
  constructor riemann-ssp15-producer-marked-climbing-gym-boundary
  field
    existingProducerMarkedSignedSeedReused : Bool
    exactRootWallAdapterConstructed : Bool
    originRoleMapsToInverseWallOrientation : Bool
    jRoleMapsToMediatedWallOrientation : Bool
    sRoleMapsToForwardWallOrientation : Bool
    neutralJRoleRetainsSelectedPrimeOnWall : Bool

    producerMarkedRootWallIdentifiesJMDHoleObservation : Bool
    producerMarkedRootWallConstructsAnalyticHeightPhase : Bool
    producerMarkedRootWallCreatesZetaZeroParametrisation : Bool
    producerMarkedRootWallProvesRiemannHypothesis : Bool

open RiemannSSP15ProducerMarkedClimbingGymBoundary public

canonicalRiemannSSP15ProducerMarkedClimbingGymBoundary :
  RiemannSSP15ProducerMarkedClimbingGymBoundary
canonicalRiemannSSP15ProducerMarkedClimbingGymBoundary =
  riemann-ssp15-producer-marked-climbing-gym-boundary
    true true true true true true
    false false false false
