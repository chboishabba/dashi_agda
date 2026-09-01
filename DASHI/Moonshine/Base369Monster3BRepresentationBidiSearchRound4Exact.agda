module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound4Exact where

------------------------------------------------------------------------
-- ROUND 4 BIDI SEARCH: PHASE RESOLUTION COLLAPSES INTO THE ACTION PRODUCER
--
-- Round 3 still described the live MN3B leaf as a two-part object:
--
--   actual phase-resolved sector + actual zeta/model recognition.
--
-- The single-producer owner proves the first part is compiler output whenever
-- the recovered action is already given on a literal State carrier: choose the
-- zeta sector to be the dependent CentralEigenspace itself.  Inclusion and
-- recovery are identities.  The scientific producer therefore narrows to:
--
--   literal State + Normalizer + central/normalizer action
--   + ActualZetaSectorRecognition on THAT literal zeta eigenspace.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Base369Monster3BSingleActionProducerBidiExact as Single
import DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound3Exact as R3

------------------------------------------------------------------------
-- 1. Search actions after the collapse.
------------------------------------------------------------------------

data Round4SearchAction : Set where
  recoverLiteralStateActionProducer : Round4SearchAction
  separatelyConstructPhaseResolvedSector : Round4SearchAction
  recoverRecognitionOnLiteralZetaEigenspace : Round4SearchAction
  constructFreshNinetyCarrier : Round4SearchAction
  recoverActualFin90InertiaAction : Round4SearchAction
  recoverSameActionTwelveSeventyEightBlocks : Round4SearchAction
  recoverActualFiftyFourResidualAction : Round4SearchAction

data SearchStatus : Set where
  live pruned downstream parallel : SearchStatus

searchStatus : Round4SearchAction → SearchStatus
searchStatus recoverLiteralStateActionProducer = live
searchStatus separatelyConstructPhaseResolvedSector = pruned
searchStatus recoverRecognitionOnLiteralZetaEigenspace = live
searchStatus constructFreshNinetyCarrier = pruned
searchStatus recoverActualFin90InertiaAction = downstream
searchStatus recoverSameActionTwelveSeventyEightBlocks = downstream
searchStatus recoverActualFiftyFourResidualAction = parallel

phaseResolutionSearchIsPruned :
  searchStatus separatelyConstructPhaseResolvedSector ≡ pruned
phaseResolutionSearchIsPruned = refl

freshNinetyCarrierSearchIsPruned :
  searchStatus constructFreshNinetyCarrier ≡ pruned
freshNinetyCarrierSearchIsPruned = refl

------------------------------------------------------------------------
-- 2. One producer yields the old action-recognition capstone.
------------------------------------------------------------------------

singleProducerCompilesOldCapstone :
  Single.ActualMonster3BSingleActionProducer → Set
singleProducerCompilesOldCapstone source =
  let _ = Single.actualActionRecognitionFromSingleProducer source
  in  Set

------------------------------------------------------------------------
-- 3. Frontier status.
------------------------------------------------------------------------

record Round4Boundary : Set where
  constructor round4-boundary
  field
    literalActionProducerIsLive : Bool
    separatePhaseResolvedSearchPruned : Bool
    recognitionMustBeOnLiteralEigenspace : Bool
    characterEqualityAloneCreatesRecognition : Bool
    freshNinetyCarrierSearchPruned : Bool
    fin90InertiaIsDownstreamOfSingleProducer : Bool
    twelveSeventyEightIsDownstreamOfFin90Action : Bool
    fiftyFourResidualActionRemainsParallelSameActionTest : Bool
    actualSingleProducerRecoveredHere : Bool

canonicalRound4Boundary : Round4Boundary
canonicalRound4Boundary =
  round4-boundary
    true true true false true true true true false

------------------------------------------------------------------------
-- 4. Round-3 status is superseded only in search granularity, not by claiming
--    the actual producer has been recovered.
------------------------------------------------------------------------

round3StillRecordedActualZetaActionOpen :
  R3.leafState R3.actualZetaActionRecognition ≡ R3.open
round3StillRecordedActualZetaActionOpen = refl
