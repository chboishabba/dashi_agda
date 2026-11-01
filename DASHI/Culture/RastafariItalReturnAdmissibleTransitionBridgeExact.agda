module DASHI.Culture.RastafariItalReturnAdmissibleTransitionBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleTransitionHyperfabricExact as Transition
import DASHI.Culture.RastafariItalReturnFlowCircularityExact as Return

------------------------------------------------------------------------
-- RETURN FLOW -> MERGED ADMISSIBLE TRANSITION CORE
--
-- This module reuses the proof-relevant transition grammar merged in PR #647.
-- A return/reintroduction edge is not merely low-weight or intended: it must be
-- enabled in the current material-history state.
------------------------------------------------------------------------

data ReturnMove : Set where
  reintroduce : ReturnMove

data ReturnParameter : Set where
  declaredReturnProtocol : ReturnParameter

returnEnabled : ReturnMove → ReturnParameter → Return.ReturnStatus → Set
returnEnabled reintroduce declaredReturnProtocol Return.transformedForReturn = ⊤
returnEnabled reintroduce declaredReturnProtocol _ = ⊥

returnStep : ReturnMove → ReturnParameter → Return.ReturnStatus → Return.ReturnStatus
returnStep reintroduce declaredReturnProtocol Return.transformedForReturn = Return.reintroducedVerified
returnStep reintroduce declaredReturnProtocol status = status

returnInvariant : Return.ReturnStatus → Set
returnInvariant _ = ⊤

returnPreservesInvariant :
  (move : ReturnMove) →
  (parameter : ReturnParameter) →
  (state : Return.ReturnStatus) →
  returnEnabled move parameter state →
  returnInvariant state →
  returnInvariant (returnStep move parameter state)
returnPreservesInvariant move parameter state enabled invariant = tt

italReturnTransitionSystem : Transition.AdmissibleTransitionSystem
italReturnTransitionSystem =
  Transition.admissibleTransitionSystem
    Return.ReturnStatus
    ReturnParameter
    ReturnMove
    returnEnabled
    returnStep
    returnInvariant
    returnPreservesInvariant
    "DASHI Ital return-flow adapter; source/process-specific enablement remains external"

------------------------------------------------------------------------
-- Concrete finite accessibility facts.
------------------------------------------------------------------------

transformedReturnIsAccessible :
  Transition.Accessible
    italReturnTransitionSystem
    declaredReturnProtocol
    Return.transformedForReturn
    reintroduce
transformedReturnIsAccessible = tt

transformedReturnIsAdmitted :
  Transition.AdmittedStep
    italReturnTransitionSystem
    reintroduce
    declaredReturnProtocol
    Return.transformedForReturn
transformedReturnIsAdmitted = Transition.admittedStep tt tt

recoveredUnverifiedReturnIsDisabled :
  Transition.Enabled
    italReturnTransitionSystem
    reintroduce
    declaredReturnProtocol
    Return.recoveredUnverified → ⊥
recoveredUnverifiedReturnIsDisabled disabled = disabled

recoveredUnverifiedCannotBeAdmitted :
  Transition.AdmittedStep
    italReturnTransitionSystem
    reintroduce
    declaredReturnProtocol
    Return.recoveredUnverified → ⊥
recoveredUnverifiedCannotBeAdmitted =
  Transition.disabledExcludesAdmittedStep recoveredUnverifiedReturnIsDisabled

verifiedReintroductionPreservesInvariant :
  Transition.InvariantRegion
    italReturnTransitionSystem
    (Transition.step
      italReturnTransitionSystem
      reintroduce
      declaredReturnProtocol
      Return.transformedForReturn)
verifiedReintroductionPreservesInvariant =
  Transition.admittedStepPreservesInvariant transformedReturnIsAdmitted

------------------------------------------------------------------------
-- Promotion boundaries.
------------------------------------------------------------------------

data IntendedReuseProvesEnabledReturn : Set where

data RecoveryProvesAdmittedReintroduction : Set where

data AdmittedReturnProvesClosedLoop : Set where

intendedReuseDoesNotProveEnabledReturn : IntendedReuseProvesEnabledReturn → ⊥
intendedReuseDoesNotProveEnabledReturn ()

recoveryDoesNotProveAdmittedReintroduction :
  RecoveryProvesAdmittedReintroduction → ⊥
recoveryDoesNotProveAdmittedReintroduction ()

admittedReturnDoesNotProveClosedLoop : AdmittedReturnProvesClosedLoop → ⊥
admittedReturnDoesNotProveClosedLoop ()

record ItalReturnTransitionBoundary : Set where
  constructor italReturnTransitionBoundary
  field
    intendedReuseIsEnabledTransition : Bool
    intendedReuseIsEnabledTransitionIsFalse : intendedReuseIsEnabledTransition ≡ false

    recoveredMaterialIsAdmittedReintroduction : Bool
    recoveredMaterialIsAdmittedReintroductionIsFalse :
      recoveredMaterialIsAdmittedReintroduction ≡ false

    enabledTransitionRequiresProof : Bool
    enabledTransitionRequiresProofIsTrue : enabledTransitionRequiresProof ≡ true

    mergedAdmissibleTransitionOwnerIsReused : Bool
    mergedAdmissibleTransitionOwnerIsReusedIsTrue :
      mergedAdmissibleTransitionOwnerIsReused ≡ true

canonicalItalReturnTransitionBoundary : ItalReturnTransitionBoundary
canonicalItalReturnTransitionBoundary =
  italReturnTransitionBoundary
    false refl
    false refl
    true refl
    true refl
