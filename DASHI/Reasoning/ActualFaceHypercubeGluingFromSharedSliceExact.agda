module DASHI.Reasoning.ActualFaceHypercubeGluingFromSharedSliceExact where

------------------------------------------------------------------------
-- SHARED ACTUAL X6 SLICE -> FULL FACE-HYPERCUBE CECH PROMOTION
--
-- DASHI CONTRIBUTION
--
-- A large part of the actual-state Cech promotion is generic.
--
-- If one has:
--
--   * one model action on X6,
--   * one literal actual-state carrier,
--   * one injective inclusion X6 -> ActualState,
--   * one actual action intertwining that inclusion,
--
-- then all six face charts may reuse the same literal X6 slice.  Identity edge
-- transports then make all twelve edge agreements and all eight corner
-- cocycles automatic.
--
-- Domain-specific recognition is therefore reduced to the existence of one
-- shared actual slice plus its action intertwiner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Base369Ternary27FaceHypercubeCechGluingBidiExact as Cech

record SharedActualX6SliceRecognition
    (Actor ActualState : Set) : Set₁ where
  field
    modelAct :
      Actor -> H.X6 -> H.X6

    actualAct :
      Actor -> ActualState -> ActualState

    include :
      H.X6 -> ActualState

    includeInjective :
      {left right : H.X6} ->
      include left ≡ include right ->
      left ≡ right

    includeIntertwines :
      (actor : Actor) ->
      (state : H.X6) ->
      include (modelAct actor state)
      ≡ actualAct actor (include state)

open SharedActualX6SliceRecognition public

compileSharedSliceGluing :
  {Actor ActualState : Set} ->
  SharedActualX6SliceRecognition Actor ActualState ->
  Cech.ActualFaceHypercubeGluingPromotion Actor ActualState
compileSharedSliceGluing recognition = record
  { modelGluing =
      Cech.uniformModelGluing (modelAct recognition)
  ; actualAct =
      actualAct recognition
  ; includeFace =
      λ face state -> include recognition state
  ; includeFaceInjective =
      λ face equality -> includeInjective recognition equality
  ; includeFaceIntertwines =
      λ face actor state ->
        includeIntertwines recognition actor state
  ; edgeDescriptionsAgreeInActualState =
      λ edge state -> refl
  }

sharedSliceCompilesEveryFace :
  {Actor ActualState : Set} ->
  (recognition : SharedActualX6SliceRecognition Actor ActualState) ->
  (face : DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact.Face6) ->
  (state : H.X6) ->
  Cech.includeFace (compileSharedSliceGluing recognition) face state
  ≡ include recognition state
sharedSliceCompilesEveryFace recognition face state = refl

record SharedSliceGluingCompilerBoundary : Set where
  constructor shared-slice-gluing-compiler-boundary
  field
    oneLiteralActualSliceSuffices : Bool
    injectiveInclusionRequired : Bool
    actionIntertwiningRequired : Bool
    sixFaceChartsGenerated : Bool
    twelveEdgeAgreementsGenerated : Bool
    eightCornerCocyclesGenerated : Bool
    domainSpecificActualRecognitionConstructedHere : Bool

canonicalSharedSliceGluingCompilerBoundary :
  SharedSliceGluingCompilerBoundary
canonicalSharedSliceGluingCompilerBoundary =
  shared-slice-gluing-compiler-boundary
    true true true true true true false
