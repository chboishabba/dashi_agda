module DASHI.Governance.ProxyObjectiveFutureSafetyExact where

------------------------------------------------------------------------
-- SOURCE / CROSS-POLLINATION CALIBRATION
--
-- Authors: Patrick Cousot; Radhia Cousot.
-- Title: "Abstract interpretation: a unified lattice model for static analysis
-- of programs by construction or approximation of fixpoints".
-- Venue: POPL 1977, pp. 238--252.
-- DOI: 10.1145/512950.512973.
--
-- The source motivates abstraction/concrete-state separation only.  The exact
-- proxy/welfare trace-sufficiency theorem below is a DASHI construction.
--
-- Internal producer pollen:
--   * DynamicalQuotientSafety: equal coarse observations require their own
--     future congruence theorem;
--   * PR #548 / DevelopmentalMeasurementQuotientExact: equal present
--     measurement can hide state that changes later developmental outcome;
--   * PR #556 / ResponsiveInfluencePolicy: engagement, repeat purchase,
--     compliance and immediate quiet are explicit proxy objectives and are not
--     definitionally welfare.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Governance.ResponsiveInfluencePolicy as Influence
import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

record ProxyWelfareSystem : Set₁ where
  constructor proxyWelfareSystem
  field
    State : Set
    Action : Set
    ProxyObservation : Set
    WelfareObservation : Set
    system : Dependency.DependentActionSystem State Action
    proxy : State → ProxyObservation
    welfare : State → WelfareObservation

open ProxyWelfareSystem public

record ProxySufficientForFutureWelfare
  (S : ProxyWelfareSystem) : Set₁ where
  constructor proxySufficientForFutureWelfare
  field
    traceSufficiency :
      ∀ {actions : List (Action S)}
        {left right leftAfter rightAfter : State S} →
      proxy S left ≡ proxy S right →
      Reachability.Executes (system S) actions left leftAfter →
      Reachability.Executes (system S) actions right rightAfter →
      welfare S leftAfter ≡ welfare S rightAfter

open ProxySufficientForFutureWelfare public

record ProxyFutureWelfareDefect
  (S : ProxyWelfareSystem) : Set₁ where
  constructor proxyFutureWelfareDefect
  field
    actionTrace : List (Action S)
    left right leftAfter rightAfter : State S
    samePresentProxy : proxy S left ≡ proxy S right
    leftExecution :
      Reachability.Executes (system S) actionTrace left leftAfter
    rightExecution :
      Reachability.Executes (system S) actionTrace right rightAfter
    futureWelfareDiffers : welfare S leftAfter ≡ welfare S rightAfter → ⊥

open ProxyFutureWelfareDefect public

proxyFutureDefectRefutesWelfareSufficiency :
  ∀ {S : ProxyWelfareSystem} →
  ProxySufficientForFutureWelfare S →
  ProxyFutureWelfareDefect S →
  ⊥
proxyFutureDefectRefutesWelfareSufficiency sufficient defect =
  futureWelfareDiffers defect
    (traceSufficiency sufficient
      (samePresentProxy defect)
      (leftExecution defect)
      (rightExecution defect))

------------------------------------------------------------------------
-- Exact finite regression.
------------------------------------------------------------------------

data FiniteState : Set where
  finiteLeftBefore finiteRightBefore finiteLeftAfter finiteRightAfter : FiniteState

data FiniteAction : Set where advance : FiniteAction

finiteStep : FiniteState → FiniteState
finiteStep finiteLeftBefore = finiteLeftAfter
finiteStep finiteRightBefore = finiteRightAfter
finiteStep finiteLeftAfter = finiteLeftAfter
finiteStep finiteRightAfter = finiteRightAfter

finiteSystem : Dependency.DependentActionSystem FiniteState FiniteAction
finiteSystem = record
  { Precondition = λ state action → ⊤
  ; Postcondition = λ before action after → after ≡ finiteStep before
  ; actionLabel = λ action → "advance"
  }

finiteAdmissible :
  (state : FiniteState) →
  Dependency.AdmissibleAction finiteSystem state advance
finiteAdmissible state = record
  { precondition = tt
  ; after = finiteStep state
  ; postcondition = refl
  ; dependencyReceipt = "finite proxy/welfare regression transition"
  }

finiteProxy : FiniteState → Bool
finiteProxy _ = false

finiteWelfare : FiniteState → Bool
finiteWelfare finiteLeftBefore = false
finiteWelfare finiteRightBefore = false
finiteWelfare finiteLeftAfter = false
finiteWelfare finiteRightAfter = true

finiteProxyWelfareSystem : ProxyWelfareSystem
finiteProxyWelfareSystem =
  proxyWelfareSystem
    FiniteState FiniteAction Bool Bool finiteSystem finiteProxy finiteWelfare

finiteLeftRun :
  Reachability.Executes finiteSystem
    (advance ∷ []) finiteLeftBefore finiteLeftAfter
finiteLeftRun =
  Reachability.executesCons
    (finiteAdmissible finiteLeftBefore)
    Reachability.executesNil

finiteRightRun :
  Reachability.Executes finiteSystem
    (advance ∷ []) finiteRightBefore finiteRightAfter
finiteRightRun =
  Reachability.executesCons
    (finiteAdmissible finiteRightBefore)
    Reachability.executesNil

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

finiteProxyFutureDefect :
  ProxyFutureWelfareDefect finiteProxyWelfareSystem
finiteProxyFutureDefect =
  proxyFutureWelfareDefect
    (advance ∷ [])
    finiteLeftBefore
    finiteRightBefore
    finiteLeftAfter
    finiteRightAfter
    refl
    finiteLeftRun
    finiteRightRun
    falseNotTrue

finiteProxyIsNotFutureWelfareSufficient :
  ProxySufficientForFutureWelfare finiteProxyWelfareSystem → ⊥
finiteProxyIsNotFutureWelfareSufficient sufficient =
  proxyFutureDefectRefutesWelfareSufficiency
    sufficient finiteProxyFutureDefect

------------------------------------------------------------------------
-- Adapter boundary back to ResponsiveInfluencePolicy.
------------------------------------------------------------------------

record InfluenceProxyAdapter
  (S : Influence.InfluenceSystem) : Set₁ where
  constructor influenceProxyAdapter
  field
    proxyWelfare : ProxyWelfareSystem
    sameStateCarrier : State proxyWelfare ≡ Influence.State S
    sameActionCarrier : Action proxyWelfare ≡ Influence.Input S

record ProxyFutureSafetyBoundary : Set where
  constructor proxyFutureSafetyBoundary
  field
    presentProxyEqualityImpliesFutureWelfareEquality : Bool
    proxyOptimalityImpliesWelfareOptimality : Bool
    futureWelfareSufficiencyNeedsTraceTheorem : Bool
    separatingDefectCanRefuteSufficiency : Bool
    hiddenStateDifferenceAloneProvesHarm : Bool
    namedDomainNeedsEmpiricalInstantiation : Bool

canonicalProxyFutureSafetyBoundary : ProxyFutureSafetyBoundary
canonicalProxyFutureSafetyBoundary =
  proxyFutureSafetyBoundary false false true true false true

record ProxyFutureSafetyReceipt : Set where
  constructor proxyFutureSafetyReceipt
  field
    sources : List Sources.ScholarlySource
    boundary : ProxyFutureSafetyBoundary

canonicalProxyFutureSafetyReceipt : ProxyFutureSafetyReceipt
canonicalProxyFutureSafetyReceipt =
  proxyFutureSafetyReceipt
    (Sources.cousotAbstractInterpretation
      ∷ Sources.screenUseContextMetaAnalysis
      ∷ Sources.feedingPracticesProspective
      ∷ [])
    canonicalProxyFutureSafetyBoundary
