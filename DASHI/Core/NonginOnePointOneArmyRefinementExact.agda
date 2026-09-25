module DASHI.Core.NonginOnePointOneArmyRefinementExact where

------------------------------------------------------------------------
-- NONGIN 1.1-ARMY REFINEMENT
--
-- HISTORICAL SOURCE / GENEALOGY
--
-- User-supplied raw nongin-origin material records the sequence:
--
--   1 + 1/10 = 1.1 > 1
--   "my 1.1 army vs your 1 army"
--   "1.1 knowledge" versus "1.0 knowledge"
--   "even 1 layer of removal and 10% is significant"
--
-- This module formalises the structural content only:
--
--   base carrier X
--     <- forget --
--   frame-bearing carrier X x F
--
-- where the richer carrier can retain distinctions invisible to the base
-- projection.  The historical "+10%" notation is NOT promoted to an empirical
-- ten-percent performance law, intelligence ranking, or physical constant.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Core.ConsumerGuidedReopenableRefinementExact as Refine
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Base
import DASHI.Core.DialecticOriginSourceAtlasExact as Origin
import DASHI.Promotion.MetacognitiveFrameBearingState as Meta

------------------------------------------------------------------------
-- 1. Generic 1.0 / 1.1 carrier pair.
------------------------------------------------------------------------

OnePointOneCarrier : Set -> Set -> Set
OnePointOneCarrier Base Frame = Base × Frame

onePointZeroProject :
  {Base Frame : Set} ->
  OnePointOneCarrier Base Frame ->
  Base
onePointZeroProject = proj₁

onePointOneProject :
  {Base Frame : Set} ->
  OnePointOneCarrier Base Frame ->
  OnePointOneCarrier Base Frame
onePointOneProject state = state

forgetOnePointOne :
  {Base Frame : Set} ->
  OnePointOneCarrier Base Frame ->
  Base
forgetOnePointOne = onePointZeroProject

onePointZeroFactorsThroughOnePointOne :
  {Base Frame : Set} ->
  (state : OnePointOneCarrier Base Frame) ->
  onePointZeroProject state
  ≡ forgetOnePointOne (onePointOneProject state)
onePointZeroFactorsThroughOnePointOne state = refl

------------------------------------------------------------------------
-- 2. A nontrivial frame supplies the exact strict-refinement witness.
------------------------------------------------------------------------

record NontrivialFrame (Frame : Set) : Set where
  constructor nontrivial-frame
  field
    firstFrame secondFrame : Frame
    framesDistinct : firstFrame ≡ secondFrame -> ⊥

open NontrivialFrame public

onePointOneStrictlyRefinesOnePointZero :
  {Base Frame : Set} ->
  (base : Base) ->
  (frameWitness : NontrivialFrame Frame) ->
  Refine.StrictProjectionRefinement
    (onePointZeroProject {Base} {Frame})
    (onePointOneProject {Base} {Frame})
onePointOneStrictlyRefinesOnePointZero base frameWitness =
  Refine.strictProjectionRefinement
    forgetOnePointOne
    onePointZeroFactorsThroughOnePointOne
    (base , firstFrame frameWitness)
    (base , secondFrame frameWitness)
    refl
    (λ same ->
      framesDistinct frameWitness (cong proj₂ same))

------------------------------------------------------------------------
-- 3. Strategic/consumer relevance requires a consumer that actually uses the
--    frame coordinate.  More representation alone is not automatically useful.
------------------------------------------------------------------------

record FrameSensitiveConsumer
    {Base Frame Output : Set}
    (consume : OnePointOneCarrier Base Frame -> Output) : Set₁ where
  constructor frame-sensitive-consumer
  field
    baseWitness : Base
    frameWitness : NontrivialFrame Frame
    consumerSeparatesFrames :
      consume (baseWitness , firstFrame frameWitness)
      ≡ consume (baseWitness , secondFrame frameWitness) -> ⊥

open FrameSensitiveConsumer public

onePointOneConsumerGuidedRefinement :
  {Base Frame Output : Set} ->
  {consume : OnePointOneCarrier Base Frame -> Output} ->
  FrameSensitiveConsumer consume ->
  Refine.ConsumerGuidedRefinement
    (onePointZeroProject {Base} {Frame})
    (onePointOneProject {Base} {Frame})
    consume
onePointOneConsumerGuidedRefinement sensitivity =
  Refine.consumerGuidedRefinement
    (onePointOneStrictlyRefinesOnePointZero
      (baseWitness sensitivity)
      (frameWitness sensitivity))
    (consumerSeparatesFrames sensitivity)

onePointZeroCannotServeEveryFrameSensitiveConsumer :
  {Base Frame Output : Set} ->
  {consume : OnePointOneCarrier Base Frame -> Output} ->
  (sensitivity : FrameSensitiveConsumer consume) ->
  Base.ConsumerDescent
    (onePointZeroProject {Base} {Frame})
    consume ->
  ⊥
onePointZeroCannotServeEveryFrameSensitiveConsumer sensitivity =
  Refine.consumerGuidedRefinementRefutesOldDescent
    (onePointOneConsumerGuidedRefinement sensitivity)

------------------------------------------------------------------------
-- 4. Exact finite witness.
------------------------------------------------------------------------

data Base1 : Set where
  sharedSituation : Base1

data Frame2 : Set where
  immersed : Frame2
  frameAware : Frame2

immersedNotFrameAware : immersed ≡ frameAware -> ⊥
immersedNotFrameAware ()

canonicalFrameWitness : NontrivialFrame Frame2
canonicalFrameWitness =
  nontrivial-frame immersed frameAware immersedNotFrameAware

data Response2 : Set where
  lowerFrameResponse : Response2
  frameBearingResponse : Response2

frameSensitiveResponse :
  OnePointOneCarrier Base1 Frame2 -> Response2
frameSensitiveResponse (sharedSituation , immersed) = lowerFrameResponse
frameSensitiveResponse (sharedSituation , frameAware) = frameBearingResponse

responseSeparatesFrames :
  frameSensitiveResponse (sharedSituation , immersed)
  ≡ frameSensitiveResponse (sharedSituation , frameAware) -> ⊥
responseSeparatesFrames ()

canonicalFrameSensitiveConsumer :
  FrameSensitiveConsumer frameSensitiveResponse
canonicalFrameSensitiveConsumer =
  frame-sensitive-consumer
    sharedSituation
    canonicalFrameWitness
    responseSeparatesFrames

canonicalOnePointOneRefinement :
  Refine.ConsumerGuidedRefinement
    (onePointZeroProject {Base1} {Frame2})
    (onePointOneProject {Base1} {Frame2})
    frameSensitiveResponse
canonicalOnePointOneRefinement =
  onePointOneConsumerGuidedRefinement canonicalFrameSensitiveConsumer

------------------------------------------------------------------------
-- 5. Genealogy / promotion boundary.
------------------------------------------------------------------------

record NonginOnePointOneArmyBoundary : Set where
  constructor nongin-one-point-one-army-boundary
  field
    nonginGenealogyRetained : Bool
    inheritedOriginBoundary :
      Origin.DialecticOriginSourceAtlasBoundary
    inheritedMetacognitiveBoundary :
      Meta.MetacognitivePowerUpBoundary
    onePointOneFactorsToOnePointZero : Bool
    nontrivialFrameCanSplitOldFibre : Bool
    usefulnessRequiresFrameSensitiveConsumer : Bool
    literalTenPercentPerformanceLawClaimed : Bool
    onePointOneAgentsUniversallySuperiorClaimed : Bool
    frameAwarenessCreatesCausalAuthority : Bool
    frameAwarenessCreatesActionAuthority : Bool

canonicalNonginOnePointOneArmyBoundary :
  NonginOnePointOneArmyBoundary
canonicalNonginOnePointOneArmyBoundary =
  nongin-one-point-one-army-boundary
    true
    Origin.canonicalDialecticOriginSourceAtlasBoundary
    Meta.canonicalMetacognitivePowerUpBoundary
    true true true
    false false false false
