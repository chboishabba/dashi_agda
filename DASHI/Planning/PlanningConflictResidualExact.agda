module DASHI.Planning.PlanningConflictResidualExact where

open import DASHI.Core.Prelude

import DASHI.Biology.SocialEcologicalAffordanceConeExact as Ecology
import DASHI.Governance.OppositionInterfaceAntiDomesticationExact as Opposition
import DASHI.Governance.PeaceJusticeResidualNonFactorabilityExact as Justice

------------------------------------------------------------------------
-- PLANNING CONFLICT / RESIDUAL
--
-- Visible order, administrative participation and built-space exclusion are
-- distinct observation/governance fibres.  This module composes existing
-- finite theorem owners to make that non-collapse explicit for planning.
------------------------------------------------------------------------

hostileBuiltFormCanContractRestAffordance :
  Ecology.available
    Ecology.canonicalUnhousedPerson
    Ecology.hostileEcology
    Ecology.sleepAction ≡ false
hostileBuiltFormCanContractRestAffordance =
  Ecology.hostileDesignContractsSleep

quietOrderDoesNotEstablishJusticeClosure :
  Justice.JusticeClosureCertificate
    Justice.Rechart.suppressedQuietState → ⊥
quietOrderDoesNotEstablishJusticeClosure =
  Justice.orderOnlyPeaceDoesNotEstablishJusticeClosure

surfaceConflictSuppressionCanLeaveJusticeResidualOpen :
  Justice.justiceResidual Justice.Rechart.visibleConflictState ≡
  Justice.justiceResidual Justice.Rechart.suppressedQuietState
surfaceConflictSuppressionCanLeaveJusticeResidualOpen =
  Justice.visibleToSuppressedSurfaceChangePreservesResidual

admittedPlanningOppositionDoesNotCreateMetaRulePower :
  Opposition.CanAlterAdmissionRule Opposition.recognisedOpposition → ⊥
admittedPlanningOppositionDoesNotCreateMetaRulePower =
  Opposition.recognisedOppositionCannotAutomaticallyAlterRule

------------------------------------------------------------------------
-- A finite structural counterexample bundle.  The components are independent
-- canonical witnesses; no claim is made that one real jurisdiction/site
-- instantiates all three simultaneously.
------------------------------------------------------------------------

record PlanningSurfaceClosureIsInsufficient : Set where
  constructor planningSurfaceClosureIsInsufficient
  field
    exclusionCanBePresentInBuiltForm :
      Ecology.available
        Ecology.canonicalUnhousedPerson
        Ecology.hostileEcology
        Ecology.sleepAction ≡ false
    quietSurfaceCanRetainOpenJusticeResidual :
      Justice.justiceResidual Justice.Rechart.suppressedQuietState ≡
        Justice.residualOpen
    admittedOppositionCanLackMetaRulePower :
      Opposition.CanAlterAdmissionRule Opposition.recognisedOpposition → ⊥

canonicalPlanningSurfaceClosureIsInsufficient :
  PlanningSurfaceClosureIsInsufficient
canonicalPlanningSurfaceClosureIsInsufficient =
  planningSurfaceClosureIsInsufficient
    Ecology.hostileDesignContractsSleep
    refl
    Opposition.recognisedOppositionCannotAutomaticallyAlterRule

record PlanningConflictResidualBoundary : Set where
  constructor planningConflictResidualBoundary
  field
    quietSurfaceEqualsJusticeClosure : Bool
    admittedObjectionEqualsRuleChangeAuthority : Bool
    restrictiveBuiltEffectProvesIntent : Bool
    conflictDisappearanceEqualsResidualResolution : Bool

canonicalPlanningConflictResidualBoundary : PlanningConflictResidualBoundary
canonicalPlanningConflictResidualBoundary =
  planningConflictResidualBoundary false false false false
