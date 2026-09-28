module DASHI.Reasoning.Trialectic369Shortest3BActionSourceBridgeExact where

------------------------------------------------------------------------
-- SHORTEST 3B FRONTIER -> ACTUAL ACTION RECOGNITION COMPILER
--
-- DASHI CONTRIBUTION
--
-- The existing Shortest3BFrontierSource already contains:
--
--   * one selected literal 3B same-element attachment,
--   * its exact VOA phase source / normalizer action,
--   * ActualZetaSectorRecognition on THAT literal zeta eigenspace.
--
-- Those are exactly the fields required by
-- ActualMonster3BSingleActionProducer.  Therefore actual action recognition is
-- compiler output from the shortest 3B source; it is not a second independent
-- recognition leaf for the trialectic outgoing residual.
--
-- What still does NOT follow is an action on the Fin90 multiplicity coordinate
-- independent of the X6 position.  That remains the
-- ActualMultiplicityInertiaAttachment wall.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Base369Monster3BShortestFrontierCapstoneBidiExact as Shortest
import DASHI.Moonshine.Base369Monster3BSingleActionProducerBidiExact as Single
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action
import DASHI.Moonshine.Base369Monster3BVOAActionPhaseAdapterBidiExact as Phase
import DASHI.Moonshine.MonsterGradedVOAActual3BKernelSameElementBidiExact as KernelWeld
import DASHI.Moonshine.MonsterGradedVOASelected3BSameElementBidiExact as Selected

------------------------------------------------------------------------
-- 1. Reuse the exact selected phase source carried by the shortest frontier.
------------------------------------------------------------------------

selectedPhaseSource :
  ∀ {Monster K : Set} ->
  Shortest.Shortest3BFrontierSource Monster K ->
  _
selectedPhaseSource source =
  Selected.phaseSource
    (KernelWeld.selectedSource
      (Shortest.attachment source))

------------------------------------------------------------------------
-- 2. Compile the single action producer.
------------------------------------------------------------------------

shortestToSingleActionProducer :
  ∀ {Monster K : Set} ->
  Shortest.Shortest3BFrontierSource Monster K ->
  Single.ActualMonster3BSingleActionProducer
shortestToSingleActionProducer {Monster} source =
  record
    { State =
        Phase.VOACarrier
          (Phase.bridge (selectedPhaseSource source))
    ; Normalizer = Monster
    ; normalizerAction =
        Phase.normalizerActionFromVOA
          (selectedPhaseSource source)
    ; recognition =
        Shortest.recognition source
    }

------------------------------------------------------------------------
-- 3. Therefore actual action recognition is compiler output.
------------------------------------------------------------------------

shortestToActualActionRecognition :
  ∀ {Monster K : Set} ->
  Shortest.Shortest3BFrontierSource Monster K ->
  Action.ActualMonster3BActionRecognition
shortestToActualActionRecognition source =
  Single.actualActionRecognitionFromSingleProducer
    (shortestToSingleActionProducer source)

shortestCompiledRecognitionIsInputRecognition :
  ∀ {Monster K : Set}
    (source : Shortest.Shortest3BFrontierSource Monster K) ->
  Action.recognition
    (shortestToActualActionRecognition source)
  ≡ Shortest.recognition source
shortestCompiledRecognitionIsInputRecognition source = refl

------------------------------------------------------------------------
-- 4. The Fin90 multiplicity coordinate is available, but its independent
--    inertia action is not compiler output from recognition alone.
------------------------------------------------------------------------

data ShortestSourceAutomaticallyCreatesMultiplicityInertiaAttachment : Set where
data CharacterMultiplicityNinetyDeterminesMultiplicityAction : Set where

shortestSourceDoesNotAutomaticallyCreateMultiplicityInertia :
  ShortestSourceAutomaticallyCreatesMultiplicityInertiaAttachment -> ⊥
shortestSourceDoesNotAutomaticallyCreateMultiplicityInertia ()

ninetyCopiesDoNotDetermineMultiplicityAction :
  CharacterMultiplicityNinetyDeterminesMultiplicityAction -> ⊥
ninetyCopiesDoNotDetermineMultiplicityAction ()

record Trialectic369Shortest3BActionSourceBridgeBoundary : Set where
  constructor trialectic-369-shortest3b-action-source-bridge-boundary
  field
    shortestSourceContainsLiteralPhaseAction : Bool
    shortestSourceContainsActualZetaRecognition : Bool
    singleActionProducerCompiled : Bool
    actualActionRecognitionCompiled : Bool
    sameRecognitionReusedDefinitionally : Bool
    separateTrialecticActualActionRecognitionLeafNeeded : Bool
    multiplicityInertiaAttachmentCompiledFromRecognitionAlone : Bool

canonicalTrialectic369Shortest3BActionSourceBridgeBoundary :
  Trialectic369Shortest3BActionSourceBridgeBoundary
canonicalTrialectic369Shortest3BActionSourceBridgeBoundary =
  trialectic-369-shortest3b-action-source-bridge-boundary
    true true true true true false false
