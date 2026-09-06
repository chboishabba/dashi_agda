module DASHI.Core.SituatedMediationBidiCrossPollination2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.DeclaredRealizedIntegrityResidualExact as DeclaredRealized

record SituatedMediation (GlobalInput LocalContext RealizedState : Set) : Set where
  constructor situated-mediation
  field globalInput : RealizedState → GlobalInput
        localContext : RealizedState → LocalContext
open SituatedMediation public

record ContextCollision {GlobalInput LocalContext RealizedState : Set}
    (m : SituatedMediation GlobalInput LocalContext RealizedState) : Set where
  constructor context-collision
  field left right : RealizedState
        sameGlobalInput : globalInput m left ≡ globalInput m right
        localContextsDiffer : localContext m left ≢ localContext m right
open ContextCollision public

record LocalOutcomeObserver (RealizedState Outcome : Set) : Set where
  constructor local-outcome-observer
  field outcome : RealizedState → Outcome
open LocalOutcomeObserver public

record ContextSensitiveOutcomeWitness
    {GlobalInput LocalContext RealizedState Outcome : Set}
    (m : SituatedMediation GlobalInput LocalContext RealizedState)
    (o : LocalOutcomeObserver RealizedState Outcome) : Set where
  constructor context-sensitive-outcome-witness
  field collision : ContextCollision m
        outcomesDiffer : outcome o (left collision) ≢ outcome o (right collision)
open ContextSensitiveOutcomeWitness public

data GlobalSignal : Set where sameSignal : GlobalSignal
data LocalGeometry : Set where openPath obstructedPath : LocalGeometry
data RealizedSpecimen : Set where openSpecimen obstructedSpecimen : RealizedSpecimen
data LocalResult : Set where reached didNotReach : LocalResult

specimenMediation : SituatedMediation GlobalSignal LocalGeometry RealizedSpecimen
specimenMediation = situated-mediation g c
  where
    g : RealizedSpecimen → GlobalSignal
    g openSpecimen = sameSignal
    g obstructedSpecimen = sameSignal
    c : RealizedSpecimen → LocalGeometry
    c openSpecimen = openPath
    c obstructedSpecimen = obstructedPath

specimenOutcome : LocalOutcomeObserver RealizedSpecimen LocalResult
specimenOutcome = local-outcome-observer o
  where
    o : RealizedSpecimen → LocalResult
    o openSpecimen = reached
    o obstructedSpecimen = didNotReach

specimenContextSensitive : ContextSensitiveOutcomeWitness specimenMediation specimenOutcome
specimenContextSensitive = context-sensitive-outcome-witness
  (context-collision openSpecimen obstructedSpecimen refl (λ ())) (λ ())

record SituatedMediationBoundary : Set where
  constructor situated-mediation-boundary
  field localContextFirstClass sameGlobalInputMayHideDifferentLocalState analogyTransfersShapeNotDomainAuthority : Bool

canonicalSituatedMediationBoundary : SituatedMediationBoundary
canonicalSituatedMediationBoundary = situated-mediation-boundary true true true
