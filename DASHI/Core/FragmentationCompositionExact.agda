module DASHI.Core.FragmentationCompositionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- FRAGMENTATION COMPOSITION DUALITY
--
-- Two independent finite specimens share only a structural warning:
-- local/coarse presentation can erase information needed for a downstream
-- whole-system query.  The module does not assert that narrative
-- fragmentation proves trauma, nor that every distributed institution is
-- harmful, nor that the two domains are historically equivalent.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- A. REPORTING / NARRATIVE SPECIMEN
------------------------------------------------------------------------

data ReportingWorld : Set where
  trueFragmentedWorld : ReportingWorld
  falseFragmentedWorld : ReportingWorld

data NarrativeSurface : Set where
  fragmentedNarrative : NarrativeSurface

data EventTruthQuery : Set where
  eventTruthQuery : EventTruthQuery

data EventTruthAnswer : Set where
  eventOccurred : EventTruthAnswer
  eventDidNotOccur : EventTruthAnswer

narrativeSurface : ReportingWorld → NarrativeSurface
narrativeSurface world = fragmentedNarrative

eventTruthAnswer : EventTruthQuery → ReportingWorld → EventTruthAnswer
eventTruthAnswer eventTruthQuery trueFragmentedWorld = eventOccurred
eventTruthAnswer eventTruthQuery falseFragmentedWorld = eventDidNotOccur

eventTruthSemantics :
  Query.QuerySemantics ReportingWorld EventTruthQuery EventTruthAnswer
eventTruthSemantics = Query.querySemantics eventTruthAnswer

EventTruthQueryAdequacyDefect : Set₁
EventTruthQueryAdequacyDefect =
  Query.QueryAdequacyDefect narrativeSurface eventTruthSemantics eventTruthQuery

eventTruthQueryAdequacyDefect : EventTruthQueryAdequacyDefect
eventTruthQueryAdequacyDefect =
  Query.queryAdequacyDefect
    trueFragmentedWorld
    falseFragmentedWorld
    refl
    (λ ())

EventTruthQueryAdequate : Set₁
EventTruthQueryAdequate =
  Query.AdequateFor narrativeSurface eventTruthSemantics eventTruthQuery

eventTruthNotAdequate : EventTruthQueryAdequate → ⊥
eventTruthNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation eventTruthQueryAdequacyDefect

------------------------------------------------------------------------
-- B. DISTRIBUTED LOCAL-ACTION SPECIMEN
------------------------------------------------------------------------

data DistributedWorld : Set where
  benignComposition : DistributedWorld
  harmfulComposition : DistributedWorld

data LocalActionSurface : Set where
  sameLocallyIntelligibleActions : LocalActionSurface

data GlobalDefensibilityQuery : Set where
  globalDefensibilityQuery : GlobalDefensibilityQuery

data GlobalDefensibilityAnswer : Set where
  globallyDefensible : GlobalDefensibilityAnswer
  globallyIndefensible : GlobalDefensibilityAnswer

localActionSurface : DistributedWorld → LocalActionSurface
localActionSurface world = sameLocallyIntelligibleActions

globalDefensibilityAnswer :
  GlobalDefensibilityQuery → DistributedWorld → GlobalDefensibilityAnswer
globalDefensibilityAnswer globalDefensibilityQuery benignComposition = globallyDefensible
globalDefensibilityAnswer globalDefensibilityQuery harmfulComposition = globallyIndefensible

globalDefensibilitySemantics :
  Query.QuerySemantics
    DistributedWorld
    GlobalDefensibilityQuery
    GlobalDefensibilityAnswer
globalDefensibilitySemantics = Query.querySemantics globalDefensibilityAnswer

GlobalDefensibilityQueryAdequacyDefect : Set₁
GlobalDefensibilityQueryAdequacyDefect =
  Query.QueryAdequacyDefect
    localActionSurface
    globalDefensibilitySemantics
    globalDefensibilityQuery

globalDefensibilityQueryAdequacyDefect : GlobalDefensibilityQueryAdequacyDefect
globalDefensibilityQueryAdequacyDefect =
  Query.queryAdequacyDefect
    benignComposition
    harmfulComposition
    refl
    (λ ())

GlobalDefensibilityQueryAdequate : Set₁
GlobalDefensibilityQueryAdequate =
  Query.AdequateFor
    localActionSurface
    globalDefensibilitySemantics
    globalDefensibilityQuery

globalDefensibilityNotAdequate : GlobalDefensibilityQueryAdequate → ⊥
globalDefensibilityNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation
    globalDefensibilityQueryAdequacyDefect

------------------------------------------------------------------------
-- Non-promotion boundary.
------------------------------------------------------------------------

record FragmentationBoundary : Set where
  constructor fragmentationBoundary
  field
    fragmentedNarrativeAutomaticallyEstablishesTrauma : Bool
    fragmentedNarrativeAutomaticallyEstablishesFalsity : Bool
    coherentNarrativeAutomaticallyEstablishesTruth : Bool
    localRoleComplianceAutomaticallyGlobalJustification : Bool
    routineTaskAutomaticallyHarmless : Bool
    smallContributionAutomaticallyZeroContribution : Bool
    distributedCausationAutomaticallyNoCausation : Bool
    sameStructuralMechanismAutomaticallySameHistoricalEvent : Bool
    localSurfaceCanEraseGlobalAnswer : Bool

open FragmentationBoundary public

canonicalFragmentationBoundary : FragmentationBoundary
canonicalFragmentationBoundary =
  fragmentationBoundary
    false
    false
    false
    false
    false
    false
    false
    false
    true
