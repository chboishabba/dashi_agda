module DASHI.Core.ActionOrbitRecognitionFunctorExact where

------------------------------------------------------------------------
-- ACTION / ORBIT / STABILIZER RECOGNITION FUNCTOR
--
-- DASHI CONTRIBUTION
--
-- Generic contract for recognising one finite/action-groupoid presentation in
-- another.  It reuses the repository's canonical:
--
--   InvertibleSymmetryAction
--   OrbitPresentation
--
-- rather than introducing a second quotient/groupoid formalism.
--
-- The basic action functor preserves identity/composition/inverse labels and
-- intertwines the actions.  OrbitRecognition then requires an induced map on
-- chosen orbit presentations.  Stronger recognition grades add injectivity,
-- surjectivity and stabilizer preservation/reflection explicitly.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit

------------------------------------------------------------------------
-- 1. Action-functor layer.
------------------------------------------------------------------------

record ActionRecognitionFunctor
    {SourceState SourceSymmetry TargetState TargetSymmetry : Set}
    (sourceAction :
      Action.InvertibleSymmetryAction SourceState SourceSymmetry)
    (targetAction :
      Action.InvertibleSymmetryAction TargetState TargetSymmetry) : Set₁ where
  constructor action-recognition-functor
  field
    mapState : SourceState -> TargetState
    mapSymmetry : SourceSymmetry -> TargetSymmetry

    preservesIdentity :
      mapSymmetry (Action.identity sourceAction)
      ≡ Action.identity targetAction

    preservesCombine :
      (g h : SourceSymmetry) ->
      mapSymmetry (Action.combine sourceAction g h)
      ≡ Action.combine targetAction (mapSymmetry g) (mapSymmetry h)

    preservesInverse :
      (g : SourceSymmetry) ->
      mapSymmetry (Action.inverse sourceAction g)
      ≡ Action.inverse targetAction (mapSymmetry g)

    actionEquivariant :
      (g : SourceSymmetry) ->
      (state : SourceState) ->
      mapState (Action.act sourceAction g state)
      ≡ Action.act targetAction (mapSymmetry g) (mapState state)

open ActionRecognitionFunctor public

------------------------------------------------------------------------
-- 2. Orbit-level recognition.
------------------------------------------------------------------------

record OrbitRecognition
    {SourceState SourceSymmetry TargetState TargetSymmetry : Set}
    {sourceAction :
      Action.InvertibleSymmetryAction SourceState SourceSymmetry}
    {targetAction :
      Action.InvertibleSymmetryAction TargetState TargetSymmetry}
    (functor : ActionRecognitionFunctor sourceAction targetAction)
    (sourceOrbits : Orbit.OrbitPresentation sourceAction)
    (targetOrbits : Orbit.OrbitPresentation targetAction) : Set₁ where
  constructor orbit-recognition
  field
    mapOrbit :
      Orbit.Orbit sourceOrbits ->
      Orbit.Orbit targetOrbits

    orbitMapExact :
      (state : SourceState) ->
      Orbit.orbitOf targetOrbits (mapState functor state)
      ≡ mapOrbit (Orbit.orbitOf sourceOrbits state)

open OrbitRecognition public

mappedActionStaysInMappedOrbit :
  ∀ {SourceState SourceSymmetry TargetState TargetSymmetry : Set}
    {sourceAction :
      Action.InvertibleSymmetryAction SourceState SourceSymmetry}
    {targetAction :
      Action.InvertibleSymmetryAction TargetState TargetSymmetry}
    {functor : ActionRecognitionFunctor sourceAction targetAction}
    {sourceOrbits : Orbit.OrbitPresentation sourceAction}
    {targetOrbits : Orbit.OrbitPresentation targetAction}
    (recognition : OrbitRecognition functor sourceOrbits targetOrbits)
    (g : SourceSymmetry)
    (state : SourceState) ->
  Orbit.orbitOf targetOrbits
    (mapState functor (Action.act sourceAction g state))
  ≡ mapOrbit recognition (Orbit.orbitOf sourceOrbits state)
mappedActionStaysInMappedOrbit
    {sourceAction = sourceAction}
    {targetAction = targetAction}
    {functor = functor}
    {targetOrbits = targetOrbits}
    recognition g state =
  trans
    (cong
      (Orbit.orbitOf targetOrbits)
      (actionEquivariant functor g state))
    (trans
      (Orbit.orbitInvariant targetOrbits
        (mapSymmetry functor g)
        (mapState functor state))
      (orbitMapExact recognition state))

------------------------------------------------------------------------
-- 3. Pi_0 / connected-component strength.
------------------------------------------------------------------------

record Pi0Embedding
    {SourceState SourceSymmetry TargetState TargetSymmetry : Set}
    {sourceAction :
      Action.InvertibleSymmetryAction SourceState SourceSymmetry}
    {targetAction :
      Action.InvertibleSymmetryAction TargetState TargetSymmetry}
    {functor : ActionRecognitionFunctor sourceAction targetAction}
    {sourceOrbits : Orbit.OrbitPresentation sourceAction}
    {targetOrbits : Orbit.OrbitPresentation targetAction}
    (recognition : OrbitRecognition functor sourceOrbits targetOrbits) : Set₁ where
  constructor pi0-embedding
  field
    reflectsOrbitEquality :
      {left right : Orbit.Orbit sourceOrbits} ->
      mapOrbit recognition left ≡ mapOrbit recognition right ->
      left ≡ right

open Pi0Embedding public

record Pi0Surjection
    {SourceState SourceSymmetry TargetState TargetSymmetry : Set}
    {sourceAction :
      Action.InvertibleSymmetryAction SourceState SourceSymmetry}
    {targetAction :
      Action.InvertibleSymmetryAction TargetState TargetSymmetry}
    {functor : ActionRecognitionFunctor sourceAction targetAction}
    {sourceOrbits : Orbit.OrbitPresentation sourceAction}
    {targetOrbits : Orbit.OrbitPresentation targetAction}
    (recognition : OrbitRecognition functor sourceOrbits targetOrbits) : Set₁ where
  constructor pi0-surjection
  field
    preimageOrbit :
      Orbit.Orbit targetOrbits ->
      Orbit.Orbit sourceOrbits

    hitsEveryTargetOrbit :
      (targetOrbit : Orbit.Orbit targetOrbits) ->
      mapOrbit recognition (preimageOrbit targetOrbit)
      ≡ targetOrbit

open Pi0Surjection public

------------------------------------------------------------------------
-- 4. Stabilizer preservation/reflection.
------------------------------------------------------------------------

record StabilizerRecognition
    {SourceState SourceSymmetry TargetState TargetSymmetry : Set}
    {sourceAction :
      Action.InvertibleSymmetryAction SourceState SourceSymmetry}
    {targetAction :
      Action.InvertibleSymmetryAction TargetState TargetSymmetry}
    {functor : ActionRecognitionFunctor sourceAction targetAction}
    {sourceOrbits : Orbit.OrbitPresentation sourceAction}
    {targetOrbits : Orbit.OrbitPresentation targetAction}
    (recognition : OrbitRecognition functor sourceOrbits targetOrbits) : Set₁ where
  constructor stabilizer-recognition
  field
    representativeCompatibility :
      (sourceOrbit : Orbit.Orbit sourceOrbits) ->
      mapState functor (Orbit.representative sourceOrbits sourceOrbit)
      ≡ Orbit.representative targetOrbits (mapOrbit recognition sourceOrbit)

    preservesStabilizer :
      (sourceOrbit : Orbit.Orbit sourceOrbits) ->
      (g : SourceSymmetry) ->
      Action.act sourceAction g
        (Orbit.representative sourceOrbits sourceOrbit)
      ≡ Orbit.representative sourceOrbits sourceOrbit ->
      Action.act targetAction (mapSymmetry functor g)
        (Orbit.representative targetOrbits
          (mapOrbit recognition sourceOrbit))
      ≡ Orbit.representative targetOrbits
          (mapOrbit recognition sourceOrbit)

    reflectsMappedStabilizer :
      (sourceOrbit : Orbit.Orbit sourceOrbits) ->
      (g : SourceSymmetry) ->
      Action.act targetAction (mapSymmetry functor g)
        (Orbit.representative targetOrbits
          (mapOrbit recognition sourceOrbit))
      ≡ Orbit.representative targetOrbits
          (mapOrbit recognition sourceOrbit) ->
      Action.act sourceAction g
        (Orbit.representative sourceOrbits sourceOrbit)
      ≡ Orbit.representative sourceOrbits sourceOrbit

open StabilizerRecognition public

------------------------------------------------------------------------
-- 5. Full recognition package.
------------------------------------------------------------------------

record OrbitStabilizerRecognition
    {SourceState SourceSymmetry TargetState TargetSymmetry : Set}
    {sourceAction :
      Action.InvertibleSymmetryAction SourceState SourceSymmetry}
    {targetAction :
      Action.InvertibleSymmetryAction TargetState TargetSymmetry}
    (functor : ActionRecognitionFunctor sourceAction targetAction)
    (sourceOrbits : Orbit.OrbitPresentation sourceAction)
    (targetOrbits : Orbit.OrbitPresentation targetAction) : Set₁ where
  constructor orbit-stabilizer-recognition
  field
    orbitRecognition :
      OrbitRecognition functor sourceOrbits targetOrbits

    pi0Embedding :
      Pi0Embedding orbitRecognition

    pi0Surjection :
      Pi0Surjection orbitRecognition

    stabilizerRecognition :
      StabilizerRecognition orbitRecognition

open OrbitStabilizerRecognition public

------------------------------------------------------------------------
-- 6. Recognition composition.
--
-- If A is recognised in B and B is recognised in C through the same
-- intermediate action/orbit presentation, the recognition data compose.
-- This keeps multi-stage representation pipelines theorem-bearing rather than
-- requiring each downstream consumer to rebuild a direct proof from scratch.
------------------------------------------------------------------------

composeActionRecognition :
  ∀ {AState ASym BState BSym CState CSym : Set}
    {actionA : Action.InvertibleSymmetryAction AState ASym}
    {actionB : Action.InvertibleSymmetryAction BState BSym}
    {actionC : Action.InvertibleSymmetryAction CState CSym} ->
  ActionRecognitionFunctor actionA actionB ->
  ActionRecognitionFunctor actionB actionC ->
  ActionRecognitionFunctor actionA actionC
composeActionRecognition first second =
  action-recognition-functor
    (λ state -> mapState second (mapState first state))
    (λ symmetry -> mapSymmetry second (mapSymmetry first symmetry))
    (trans
      (cong (mapSymmetry second) (preservesIdentity first))
      (preservesIdentity second))
    (λ g h ->
      trans
        (cong (mapSymmetry second) (preservesCombine first g h))
        (preservesCombine second
          (mapSymmetry first g)
          (mapSymmetry first h)))
    (λ g ->
      trans
        (cong (mapSymmetry second) (preservesInverse first g))
        (preservesInverse second (mapSymmetry first g)))
    (λ g state ->
      trans
        (cong (mapState second) (actionEquivariant first g state))
        (actionEquivariant second
          (mapSymmetry first g)
          (mapState first state)))

composeOrbitRecognition :
  ∀ {AState ASym BState BSym CState CSym : Set}
    {actionA : Action.InvertibleSymmetryAction AState ASym}
    {actionB : Action.InvertibleSymmetryAction BState BSym}
    {actionC : Action.InvertibleSymmetryAction CState CSym}
    {functorAB : ActionRecognitionFunctor actionA actionB}
    {functorBC : ActionRecognitionFunctor actionB actionC}
    {orbitsA : Orbit.OrbitPresentation actionA}
    {orbitsB : Orbit.OrbitPresentation actionB}
    {orbitsC : Orbit.OrbitPresentation actionC} ->
  (recognitionAB : OrbitRecognition functorAB orbitsA orbitsB) ->
  (recognitionBC : OrbitRecognition functorBC orbitsB orbitsC) ->
  OrbitRecognition
    (composeActionRecognition functorAB functorBC)
    orbitsA
    orbitsC
composeOrbitRecognition
    {functorAB = functorAB}
    {functorBC = functorBC}
    recognitionAB recognitionBC =
  orbit-recognition
    (λ orbit -> mapOrbit recognitionBC (mapOrbit recognitionAB orbit))
    (λ state ->
      trans
        (orbitMapExact recognitionBC (mapState functorAB state))
        (cong
          (mapOrbit recognitionBC)
          (orbitMapExact recognitionAB state)))

composePi0Embedding :
  ∀ {AState ASym BState BSym CState CSym : Set}
    {actionA : Action.InvertibleSymmetryAction AState ASym}
    {actionB : Action.InvertibleSymmetryAction BState BSym}
    {actionC : Action.InvertibleSymmetryAction CState CSym}
    {functorAB : ActionRecognitionFunctor actionA actionB}
    {functorBC : ActionRecognitionFunctor actionB actionC}
    {orbitsA : Orbit.OrbitPresentation actionA}
    {orbitsB : Orbit.OrbitPresentation actionB}
    {orbitsC : Orbit.OrbitPresentation actionC}
    {recognitionAB : OrbitRecognition functorAB orbitsA orbitsB}
    {recognitionBC : OrbitRecognition functorBC orbitsB orbitsC} ->
  Pi0Embedding recognitionAB ->
  Pi0Embedding recognitionBC ->
  Pi0Embedding (composeOrbitRecognition recognitionAB recognitionBC)
composePi0Embedding embeddingAB embeddingBC =
  pi0-embedding
    (λ same ->
      reflectsOrbitEquality embeddingAB
        (reflectsOrbitEquality embeddingBC same))

composePi0Surjection :
  ∀ {AState ASym BState BSym CState CSym : Set}
    {actionA : Action.InvertibleSymmetryAction AState ASym}
    {actionB : Action.InvertibleSymmetryAction BState BSym}
    {actionC : Action.InvertibleSymmetryAction CState CSym}
    {functorAB : ActionRecognitionFunctor actionA actionB}
    {functorBC : ActionRecognitionFunctor actionB actionC}
    {orbitsA : Orbit.OrbitPresentation actionA}
    {orbitsB : Orbit.OrbitPresentation actionB}
    {orbitsC : Orbit.OrbitPresentation actionC}
    {recognitionAB : OrbitRecognition functorAB orbitsA orbitsB}
    {recognitionBC : OrbitRecognition functorBC orbitsB orbitsC} ->
  Pi0Surjection recognitionAB ->
  Pi0Surjection recognitionBC ->
  Pi0Surjection (composeOrbitRecognition recognitionAB recognitionBC)
composePi0Surjection
    {recognitionAB = recognitionAB}
    {recognitionBC = recognitionBC}
    surjectionAB surjectionBC =
  pi0-surjection
    (λ targetOrbit ->
      preimageOrbit surjectionAB
        (preimageOrbit surjectionBC targetOrbit))
    (λ targetOrbit ->
      trans
        (cong
          (mapOrbit recognitionBC)
          (hitsEveryTargetOrbit surjectionAB
            (preimageOrbit surjectionBC targetOrbit)))
        (hitsEveryTargetOrbit surjectionBC targetOrbit))

composeStabilizerRecognition :
  ∀ {AState ASym BState BSym CState CSym : Set}
    {actionA : Action.InvertibleSymmetryAction AState ASym}
    {actionB : Action.InvertibleSymmetryAction BState BSym}
    {actionC : Action.InvertibleSymmetryAction CState CSym}
    {functorAB : ActionRecognitionFunctor actionA actionB}
    {functorBC : ActionRecognitionFunctor actionB actionC}
    {orbitsA : Orbit.OrbitPresentation actionA}
    {orbitsB : Orbit.OrbitPresentation actionB}
    {orbitsC : Orbit.OrbitPresentation actionC}
    {recognitionAB : OrbitRecognition functorAB orbitsA orbitsB}
    {recognitionBC : OrbitRecognition functorBC orbitsB orbitsC} ->
  StabilizerRecognition recognitionAB ->
  StabilizerRecognition recognitionBC ->
  StabilizerRecognition
    (composeOrbitRecognition recognitionAB recognitionBC)
composeStabilizerRecognition
    {actionA = actionA}
    {actionB = actionB}
    {actionC = actionC}
    {functorAB = functorAB}
    {functorBC = functorBC}
    {orbitsA = orbitsA}
    {orbitsB = orbitsB}
    {orbitsC = orbitsC}
    {recognitionAB = recognitionAB}
    {recognitionBC = recognitionBC}
    stabilizerAB stabilizerBC =
  stabilizer-recognition
    representative
    preserves
    reflects
  where
    representative :
      (orbit : Orbit.Orbit orbitsA) ->
      mapState (composeActionRecognition functorAB functorBC)
        (Orbit.representative orbitsA orbit)
      ≡
      Orbit.representative orbitsC
        (mapOrbit
          (composeOrbitRecognition recognitionAB recognitionBC)
          orbit)
    representative orbit =
      trans
        (cong
          (mapState functorBC)
          (representativeCompatibility stabilizerAB orbit))
        (representativeCompatibility stabilizerBC
          (mapOrbit recognitionAB orbit))

    preserves :
      (orbit : Orbit.Orbit orbitsA) ->
      (g : ASym) ->
      Action.act actionA g (Orbit.representative orbitsA orbit)
      ≡ Orbit.representative orbitsA orbit ->
      Action.act actionC
        (mapSymmetry
          (composeActionRecognition functorAB functorBC)
          g)
        (Orbit.representative orbitsC
          (mapOrbit
            (composeOrbitRecognition recognitionAB recognitionBC)
            orbit))
      ≡
      Orbit.representative orbitsC
        (mapOrbit
          (composeOrbitRecognition recognitionAB recognitionBC)
          orbit)
    preserves orbit g fixed =
      preservesStabilizer stabilizerBC
        (mapOrbit recognitionAB orbit)
        (mapSymmetry functorAB g)
        (preservesStabilizer stabilizerAB orbit g fixed)

    reflects :
      (orbit : Orbit.Orbit orbitsA) ->
      (g : ASym) ->
      Action.act actionC
        (mapSymmetry
          (composeActionRecognition functorAB functorBC)
          g)
        (Orbit.representative orbitsC
          (mapOrbit
            (composeOrbitRecognition recognitionAB recognitionBC)
            orbit))
      ≡
      Orbit.representative orbitsC
        (mapOrbit
          (composeOrbitRecognition recognitionAB recognitionBC)
          orbit)
      ->
      Action.act actionA g (Orbit.representative orbitsA orbit)
      ≡ Orbit.representative orbitsA orbit
    reflects orbit g fixed =
      reflectsMappedStabilizer stabilizerAB orbit g
        (reflectsMappedStabilizer stabilizerBC
          (mapOrbit recognitionAB orbit)
          (mapSymmetry functorAB g)
          fixed)

composeOrbitStabilizerRecognition :
  ∀ {AState ASym BState BSym CState CSym : Set}
    {actionA : Action.InvertibleSymmetryAction AState ASym}
    {actionB : Action.InvertibleSymmetryAction BState BSym}
    {actionC : Action.InvertibleSymmetryAction CState CSym}
    {functorAB : ActionRecognitionFunctor actionA actionB}
    {functorBC : ActionRecognitionFunctor actionB actionC}
    {orbitsA : Orbit.OrbitPresentation actionA}
    {orbitsB : Orbit.OrbitPresentation actionB}
    {orbitsC : Orbit.OrbitPresentation actionC} ->
  OrbitStabilizerRecognition functorAB orbitsA orbitsB ->
  OrbitStabilizerRecognition functorBC orbitsB orbitsC ->
  OrbitStabilizerRecognition
    (composeActionRecognition functorAB functorBC)
    orbitsA
    orbitsC
composeOrbitStabilizerRecognition first second =
  orbit-stabilizer-recognition
    (composeOrbitRecognition
      (orbitRecognition first)
      (orbitRecognition second))
    (composePi0Embedding
      (pi0Embedding first)
      (pi0Embedding second))
    (composePi0Surjection
      (pi0Surjection first)
      (pi0Surjection second))
    (composeStabilizerRecognition
      (stabilizerRecognition first)
      (stabilizerRecognition second))

data CardinalityMatchCreatesRecognitionFunctor : Set where
data StateMapAlonePreservesPi0 : Set where
data OrbitBijectionAlonePreservesStabilizers : Set where

cardinalityMatchDoesNotCreateRecognitionFunctor :
  CardinalityMatchCreatesRecognitionFunctor -> ⊥
cardinalityMatchDoesNotCreateRecognitionFunctor ()

stateMapAloneDoesNotPreservePi0 :
  StateMapAlonePreservesPi0 -> ⊥
stateMapAloneDoesNotPreservePi0 ()

orbitBijectionAloneDoesNotPreserveStabilizers :
  OrbitBijectionAlonePreservesStabilizers -> ⊥
orbitBijectionAloneDoesNotPreserveStabilizers ()

record ActionOrbitRecognitionBoundary : Set where
  constructor action-orbit-recognition-boundary
  field
    actionEquivarianceRequired : Bool
    symmetryIdentityCompositionInverseRequired : Bool
    orbitMapMustBeExactOnStates : Bool
    pi0InjectivitySeparateObligation : Bool
    pi0SurjectivitySeparateObligation : Bool
    stabilizerPreservationSeparateObligation : Bool
    stabilizerReflectionSeparateObligation : Bool
    cardinalityMatchSufficientForRecognition : Bool

canonicalActionOrbitRecognitionBoundary :
  ActionOrbitRecognitionBoundary
canonicalActionOrbitRecognitionBoundary =
  action-orbit-recognition-boundary
    true true true true true true true false
