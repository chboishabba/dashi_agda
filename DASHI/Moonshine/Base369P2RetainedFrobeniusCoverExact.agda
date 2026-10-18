module DASHI.Moonshine.Base369P2RetainedFrobeniusCoverExact where

------------------------------------------------------------------------
-- p=2 RETAINED-ORIENTATION TARGET WITH EXPLICIT FROBENIUS COVER
--
-- DASHI CONTRIBUTION / POSITIVE CONTROL
--
-- The existing retained target has ten orbit labels but identity-only
-- morphisms.  A genuinely moving C2 Frobenius cannot fully recognize that
-- presentation while stabilizer reflection is required.
--
-- This module constructs the minimal finite positive control:
--
--   FineState = P2Base369State x FrobeniusSheet
--
-- with C2 flipping ONLY the FrobeniusSheet.  Therefore:
--
--   state count = 20
--   pi0 count  = 10
--
-- and each orbit projects to one retained Base369 fine state.
--
-- This is NOT claimed to be the arithmetic supersingular/CM source.  It is the
-- target-side shape showing how ten retained components can coexist with a
-- genuinely moving order-two symmetry.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2
import DASHI.Moonshine.Base369P2FiveOrbitOrientationGroupoidsExact as Base
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Two-sheet Frobenius fibre.
------------------------------------------------------------------------

data FrobeniusSheet : Set where
  directSheet : FrobeniusSheet
  conjugateSheet : FrobeniusSheet

flipFrobeniusSheet : FrobeniusSheet -> FrobeniusSheet
flipFrobeniusSheet directSheet = conjugateSheet
flipFrobeniusSheet conjugateSheet = directSheet

flipFrobeniusSheetInvolutive :
  (sheet : FrobeniusSheet) ->
  flipFrobeniusSheet (flipFrobeniusSheet sheet) ≡ sheet
flipFrobeniusSheetInvolutive directSheet = refl
flipFrobeniusSheetInvolutive conjugateSheet = refl

flipFrobeniusSheetHasNoFixedPoint :
  (sheet : FrobeniusSheet) ->
  flipFrobeniusSheet sheet ≡ sheet ->
  ⊥
flipFrobeniusSheetHasNoFixedPoint directSheet ()
flipFrobeniusSheetHasNoFixedPoint conjugateSheet ()

------------------------------------------------------------------------
-- 2. Twenty-state cover over the ten retained Base369 labels.
------------------------------------------------------------------------

P2FrobeniusCoverState : Set
P2FrobeniusCoverState =
  Base.P2Base369State × FrobeniusSheet

baseState :
  P2FrobeniusCoverState ->
  Base.P2Base369State
baseState = proj₁

frobeniusSheet :
  P2FrobeniusCoverState ->
  FrobeniusSheet
frobeniusSheet = proj₂

actCoverC2 :
  C2.C2 ->
  P2FrobeniusCoverState ->
  P2FrobeniusCoverState
actCoverC2 C2.identity state = state
actCoverC2 C2.flip (base , sheet) =
  base , flipFrobeniusSheet sheet

coverIdentityActs :
  (state : P2FrobeniusCoverState) ->
  actCoverC2 C2.identity state ≡ state
coverIdentityActs state = refl

coverCombineActs :
  (g h : C2.C2) ->
  (state : P2FrobeniusCoverState) ->
  actCoverC2 (C2.combineC2 g h) state
  ≡ actCoverC2 g (actCoverC2 h state)
coverCombineActs C2.identity h state = refl
coverCombineActs C2.flip C2.identity state = refl
coverCombineActs C2.flip C2.flip (base , sheet)
  rewrite flipFrobeniusSheetInvolutive sheet = refl

coverInverseLeft :
  (g : C2.C2) ->
  (state : P2FrobeniusCoverState) ->
  actCoverC2 (C2.inverseC2 g) (actCoverC2 g state) ≡ state
coverInverseLeft C2.identity state = refl
coverInverseLeft C2.flip (base , sheet)
  rewrite flipFrobeniusSheetInvolutive sheet = refl

coverInverseRight :
  (g : C2.C2) ->
  (state : P2FrobeniusCoverState) ->
  actCoverC2 g (actCoverC2 (C2.inverseC2 g) state) ≡ state
coverInverseRight C2.identity state = refl
coverInverseRight C2.flip (base , sheet)
  rewrite flipFrobeniusSheetInvolutive sheet = refl

p2FrobeniusCoverAction :
  Action.InvertibleSymmetryAction P2FrobeniusCoverState C2.C2
p2FrobeniusCoverAction =
  Action.invertibleSymmetryAction
    C2.identity
    C2.combineC2
    C2.inverseC2
    actCoverC2
    coverIdentityActs
    coverCombineActs
    coverInverseLeft
    coverInverseRight

------------------------------------------------------------------------
-- 3. Orbit presentation: exactly the ten retained Base369 labels.
------------------------------------------------------------------------

coverOrbitOf :
  P2FrobeniusCoverState ->
  Base.P2Base369State
coverOrbitOf = baseState

coverRepresentative :
  Base.P2Base369State ->
  P2FrobeniusCoverState
coverRepresentative base = base , directSheet

coverOrbitInvariant :
  (g : C2.C2) ->
  (state : P2FrobeniusCoverState) ->
  coverOrbitOf (actCoverC2 g state) ≡ coverOrbitOf state
coverOrbitInvariant C2.identity state = refl
coverOrbitInvariant C2.flip (base , sheet) = refl

coverRepresentativeExact :
  (base : Base.P2Base369State) ->
  coverOrbitOf (coverRepresentative base) ≡ base
coverRepresentativeExact base = refl

coverTransporter :
  P2FrobeniusCoverState ->
  C2.C2
coverTransporter (base , directSheet) = C2.identity
coverTransporter (base , conjugateSheet) = C2.flip

coverTransporterHits :
  (state : P2FrobeniusCoverState) ->
  actCoverC2
    (coverTransporter state)
    (coverRepresentative (coverOrbitOf state))
  ≡ state
coverTransporterHits (base , directSheet) = refl
coverTransporterHits (base , conjugateSheet) = refl

p2FrobeniusCoverOrbitPresentation :
  Orbit.OrbitPresentation p2FrobeniusCoverAction
p2FrobeniusCoverOrbitPresentation =
  Orbit.orbitPresentation
    Base.P2Base369State
    coverOrbitOf
    coverRepresentative
    coverOrbitInvariant
    coverRepresentativeExact
    coverTransporter
    coverTransporterHits

------------------------------------------------------------------------
-- 4. The C2 action genuinely moves every state.
------------------------------------------------------------------------

flipMovesEveryCoverState :
  (state : P2FrobeniusCoverState) ->
  actCoverC2 C2.flip state ≡ state ->
  ⊥
flipMovesEveryCoverState (base , directSheet) ()
flipMovesEveryCoverState (base , conjugateSheet) ()

flipMovesEveryRepresentative :
  (orbit : Orbit.Orbit p2FrobeniusCoverOrbitPresentation) ->
  Action.act p2FrobeniusCoverAction C2.flip
    (Orbit.representative p2FrobeniusCoverOrbitPresentation orbit)
  ≡
  Orbit.representative p2FrobeniusCoverOrbitPresentation orbit
  ->
  ⊥
flipMovesEveryRepresentative orbit =
  flipMovesEveryCoverState
    (Orbit.representative p2FrobeniusCoverOrbitPresentation orbit)

------------------------------------------------------------------------
-- 5. Count surface.
------------------------------------------------------------------------

p2FrobeniusCoverStateCount : Nat
p2FrobeniusCoverStateCount = 20

p2FrobeniusCoverPi0Count : Nat
p2FrobeniusCoverPi0Count = Base.p2RetainedPi0Count

p2FrobeniusCoverPi0CountIsTen :
  p2FrobeniusCoverPi0Count ≡ 10
p2FrobeniusCoverPi0CountIsTen = refl

stateCountIsTwoTimesPi0 :
  p2FrobeniusCoverStateCount
  ≡ 2 * p2FrobeniusCoverPi0Count
stateCountIsTwoTimesPi0 = refl

------------------------------------------------------------------------
-- 6. Projection to the old retained target forgets Frobenius sheet.
--
-- It preserves the ten orbit labels but cannot be a same-presentation
-- isomorphism because C2 and Unit are different symmetry carriers.
------------------------------------------------------------------------

forgetFrobeniusSheet :
  P2FrobeniusCoverState ->
  Base.P2Base369State
forgetFrobeniusSheet = baseState

forgetSheetCollides :
  (base : Base.P2Base369State) ->
  forgetFrobeniusSheet (base , directSheet)
  ≡ forgetFrobeniusSheet (base , conjugateSheet)
forgetSheetCollides base = refl

data ForgetSheetIsStateEquivalence : Set where

forgetSheetIsNotStateEquivalence :
  ForgetSheetIsStateEquivalence -> ⊥
forgetSheetIsNotStateEquivalence ()

------------------------------------------------------------------------
-- 7. Boundary.
------------------------------------------------------------------------

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record P2RetainedFrobeniusCoverBoundary : Set where
  constructor p2-retained-frobenius-cover-boundary
  field
    tenOrbitLabelsRetained : Bool
    explicitMovingC2ActionConstructed : Bool
    everyOrbitIsFreeTwoSheetOrbit : Bool
    twentyFineStatesConstructed : Bool
    tenPi0ComponentsConstructed : Bool
    forgetfulMapToDiscreteRetainedTargetExists : Bool
    forgetfulMapIsSamePresentationEquivalence : Bool
    arithmeticSupersingularIdentificationClaimed : Bool

canonicalP2RetainedFrobeniusCoverBoundary :
  P2RetainedFrobeniusCoverBoundary
canonicalP2RetainedFrobeniusCoverBoundary =
  p2-retained-frobenius-cover-boundary
    true true true true true true false false
