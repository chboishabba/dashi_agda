module DASHI.Core.SituatedMediationBidiCrossPollination2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.DeclaredRealizedIntegrityResidualExact as DeclaredRealized

------------------------------------------------------------------------
-- SITUATED MEDIATION -- BIDI CROSS-POLLINATION
--
-- DASHI structural extension inspired by two already source-bounded lanes:
--   * DeclaredRealizedIntegrityResidualExact on situated realised affordance;
--   * semiconductor process-integration PR #719
--     https://github.com/chboishabba/dashi_agda/pull/719
--
-- This module imports no branch-local semiconductor theorem and makes no
-- production-process claim.  It extracts only the reusable shape:
--
--   same global/input surface != same local realised state
--
-- unless local geometry/history/context is known to be irrelevant.
------------------------------------------------------------------------

record SituatedMediation
    (GlobalInput LocalContext RealizedState : Set) : Set where
  constructor situated-mediation
  field
    globalInput : RealizedState → GlobalInput
    localContext : RealizedState → LocalContext

open SituatedMediation public

record ContextCollision
    {GlobalInput LocalContext RealizedState : Set}
    (m : SituatedMediation GlobalInput LocalContext RealizedState) : Set where
  constructor context-collision
  field
    left right : RealizedState
    sameGlobalInput : globalInput m left ≡ globalInput m right
    localContextsDiffer : localContext m left ≢ localContext m right

open ContextCollision public

record LocalOutcomeObserver (RealizedState Outcome : Set) : Set where
  constructor local-outcome-observer
  field
    outcome : RealizedState → Outcome

open LocalOutcomeObserver public

record ContextSensitiveOutcomeWitness
    {GlobalInput LocalContext RealizedState Outcome : Set}
    (m : SituatedMediation GlobalInput LocalContext RealizedState)
    (o : LocalOutcomeObserver RealizedState Outcome) : Set where
  constructor context-sensitive-outcome-witness
  field
    collision : ContextCollision m
    outcomesDiffer : outcome o (left collision) ≢ outcome o (right collision)

open ContextSensitiveOutcomeWitness public

------------------------------------------------------------------------
-- Exact finite specimen.
------------------------------------------------------------------------

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

specimenCollision : ContextCollision specimenMediation
specimenCollision = context-collision
  openSpecimen obstructedSpecimen refl (λ ())

specimenContextSensitive :
  ContextSensitiveOutcomeWitness specimenMediation specimenOutcome
specimenContextSensitive =
  context-sensitive-outcome-witness specimenCollision (λ ())

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data GlobalInputDeterminesLocalOutcome : Set where
data SameFormalRuleDeterminesSituatedEffect : Set where
data SameNominalProcedureDeterminesInformationReach : Set where

globalInputDoesNotDetermineLocalOutcome : GlobalInputDeterminesLocalOutcome → ⊥
globalInputDoesNotDetermineLocalOutcome ()

sameFormalRuleDoesNotDetermineSituatedEffect : SameFormalRuleDeterminesSituatedEffect → ⊥
sameFormalRuleDoesNotDetermineSituatedEffect ()

sameNominalProcedureDoesNotDetermineInformationReach :
  SameNominalProcedureDeterminesInformationReach → ⊥
sameNominalProcedureDoesNotDetermineInformationReach ()

record SituatedMediationBoundary : Set where
  constructor situated-mediation-boundary
  field
    localContextFirstClass : Bool
    sameGlobalInputMayHideDifferentLocalState : Bool
    analogyTransfersShapeNotDomainAuthority : Bool

canonicalSituatedMediationBoundary : SituatedMediationBoundary
canonicalSituatedMediationBoundary =
  situated-mediation-boundary true true true
