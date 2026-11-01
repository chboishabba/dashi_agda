module DASHI.ComputerScience.RSA260BidiMksolStyleConsumerCollisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.ComputerScience.RSA260BidiMksolConsumerProjectionExact as Mksol

------------------------------------------------------------------------
-- SYNTHETIC MKSOL-STYLE CONSUMER COLLISION
--
-- Runtime diagnostic on the existing 12-run synthetic generator harness:
--
--   action(F;M,V) = XOR_{0 <= l < d} M^l V F_l.
--
-- This is intentionally only a finite mksol-style consumer.  It is NOT claimed
-- to be the exact CADO mksol implementation.  Its role is narrower: test whether
-- rank fingerprints that were optimized for receipt identity preserve even a
-- concrete generator-evaluation consumer.
--
-- They do not.  The existing (degree, rank F2, rank F3, rank F4) collisions also
-- have different action receipts.
------------------------------------------------------------------------

mksolProjectionBoundary : Mksol.MksolConsumerProjectionBoundary
mksolProjectionBoundary = Mksol.canonicalMksolConsumerProjectionBoundary

data SyntheticMksolWorld : Set where
  seed0World : SyntheticMksolWorld
  seed3World : SyntheticMksolWorld
  seed2World : SyntheticMksolWorld
  affine5World : SyntheticMksolWorld

data DegreeRawRankObserver : Set where
  d16-r8-r7-r7 : DegreeRawRankObserver
  d17-r7-r7-r7 : DegreeRawRankObserver

data MksolStyleActionAnswer : Set where
  seed0Action : MksolStyleActionAnswer
  seed3Action : MksolStyleActionAnswer
  seed2Action : MksolStyleActionAnswer
  affine5Action : MksolStyleActionAnswer

rankObserve : SyntheticMksolWorld -> DegreeRawRankObserver
rankObserve seed0World = d16-r8-r7-r7
rankObserve seed3World = d16-r8-r7-r7
rankObserve seed2World = d17-r7-r7-r7
rankObserve affine5World = d17-r7-r7-r7

mksolStyleActionObserve : SyntheticMksolWorld -> MksolStyleActionAnswer
mksolStyleActionObserve seed0World = seed0Action
mksolStyleActionObserve seed3World = seed3Action
mksolStyleActionObserve seed2World = seed2Action
mksolStyleActionObserve affine5World = affine5Action

mksolStyleQuery : Query.QueryFamily SyntheticMksolWorld MksolStyleActionAnswer
mksolStyleQuery = Query.queryFamily ⊤ (λ world _ -> mksolStyleActionObserve world)

RankObserverAdequacyDefect : Set₁
RankObserverAdequacyDefect =
  Query.QueryAdequacyDefect
    rankObserve
    mksolStyleQuery
    tt

seed0Seed3ActionCollision : RankObserverAdequacyDefect
seed0Seed3ActionCollision =
  Query.queryAdequacyDefect
    seed0World
    seed3World
    refl
    (λ ())

seed2Affine5ActionCollision : RankObserverAdequacyDefect
seed2Affine5ActionCollision =
  Query.queryAdequacyDefect
    seed2World
    affine5World
    refl
    (λ ())

rankObserverNotAdequateForMksolStyleAction :
  Query.AdequateFor rankObserve mksolStyleQuery tt -> ⊥
rankObserverNotAdequateForMksolStyleAction =
  Query.queryAdequacyDefectBlocksFactorisation seed0Seed3ActionCollision

------------------------------------------------------------------------
-- Runtime receipt.  Digests name the computed synthetic action arrays only.
------------------------------------------------------------------------

record MksolStyleRuntimeReceipt : Set where
  constructor mksol-style-runtime-receipt
  field
    runtimePath : String
    outputPath : String
    outputSHA256 : String
    worldCount : Nat
    separatingCollisionCount : Nat
    seed0ActionSHA256 : String
    seed3ActionSHA256 : String
    seed2ActionSHA256 : String
    affine5ActionSHA256 : String
    seed0ActionWeight : Nat
    seed3ActionWeight : Nat
    seed2ActionWeight : Nat
    affine5ActionWeight : Nat
    exactLocalRuntimeExecuted : Bool
    sourceCommittedToRepository : Bool
open MksolStyleRuntimeReceipt public

currentMksolStyleRuntimeReceipt : MksolStyleRuntimeReceipt
currentMksolStyleRuntimeReceipt =
  mksol-style-runtime-receipt
    "/mnt/data synthetic execution using rsa260_bidi_raw_rank_crossvalidate.py"
    "/mnt/data/rsa260_bidi_mksol_style_consumer_diagnostic.json"
    "942bbb620357eaf9f5efc1655eef09fd1917b25727fedac3608b6fbb78d8958e"
    12
    2
    "ee391d38565523cd9f74a59651b3747f942c703e10467ba91020c2e8800a9a5d"
    "d0d6a50009a2e0547980304b09c8d3304a69ebefb1c812dc44cbe7a3c8ff2cc5"
    "51914cb2dd92648e88ea63954511e375e7eefeaec4686d2da254d700dcb3244d"
    "e35485681876fc35def14c3c16acf24ba30f16e2d4b788f4e615c8892ca5ab2b"
    3766 3775 3661 3624
    true
    false

record MksolStyleConsumerCollisionBoundary : Set where
  constructor mksol-style-consumer-collision-boundary
  field
    concreteGeneratorEvaluationConsumerExecuted : Bool
    oldDegreeRawRankObserverCollidesForActionConsumer : Bool
    seed0Seed3ActionSeparationPaid : Bool
    seed2Affine5ActionSeparationPaid : Bool
    rankReceiptIdentityFailureWasOnlyNamingFailure : Bool
    runtimeActionEqualsExactCADOMksolSemantics : Bool
    syntheticActionUsesProductionRSA260Carrier : Bool
    rankSketchPaysMksolEvaluationPreservation : Bool
    exactCoefficientReplayRemainsCandidateAdequateRepresentation : Bool
open MksolStyleConsumerCollisionBoundary public

canonicalMksolStyleConsumerCollisionBoundary : MksolStyleConsumerCollisionBoundary
canonicalMksolStyleConsumerCollisionBoundary =
  mksol-style-consumer-collision-boundary
    true true true true
    false false false false true

data MksolStyleConsumerCollisionResidual : Set where
  proveExactReplayPreservesSyntheticGeneratorAction : MksolStyleConsumerCollisionResidual
  attackCoarserThanReplayRepresentationsAgainstActionConsumer : MksolStyleConsumerCollisionResidual
  alignSyntheticActionWithSourceNativeCADOMksolEvaluation : MksolStyleConsumerCollisionResidual
  bindSameObjectVAndPreparedOperatorForProduction : MksolStyleConsumerCollisionResidual
  executeProductionMksolOnlyAfterCarrierPayments : MksolStyleConsumerCollisionResidual

firstMksolStyleConsumerCollisionResidual : MksolStyleConsumerCollisionResidual
firstMksolStyleConsumerCollisionResidual = proveExactReplayPreservesSyntheticGeneratorAction
