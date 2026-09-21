module DASHI.Law.ClosedIsNotAdequateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Law.ConsumerAdequacyRuntimeTheoremBridgeExact as Bridge
import DASHI.Law.ExactNonFactorabilityResidualCompilerExact as Residual
import DASHI.Law.ConsumerResearchAdmissibilityStopExact as Stop

------------------------------------------------------------------------
-- S15.6 / M7.5 "Closed Is Not Adequate".
--
-- Operational frontier exhaustion and theorem-bearing consumer adequacy are
-- different types.  A closed frontier with a projection fibre collision must
-- reopen exact research; only an actual AdequateFor inhabitant may certify the
-- consumer query.
------------------------------------------------------------------------

data OperationalState : Set where
  frontierOpen : OperationalState
  currentFrontierClosed : OperationalState
  budgetExhausted : OperationalState

data AdequacyCompileDisposition : Set where
  theoremAdequate : AdequacyCompileDisposition
  needsResearch : AdequacyCompileDisposition
  explicitlyUnresolved : AdequacyCompileDisposition
  closedWithoutAdequacy : AdequacyCompileDisposition
  budgetWithoutAdequacy : AdequacyCompileDisposition

------------------------------------------------------------------------
-- Regression 1: mature world has no operational work, but no proof follows.
------------------------------------------------------------------------

data CurrentFrontierClosedAutomaticallyAdequate : Set where

closedFrontierCannotConstructAdequacy :
  CurrentFrontierClosedAutomaticallyAdequate → ⊥
closedFrontierCannotConstructAdequacy ()

closedOperationalDisposition :
  AdequacyCompileDisposition
closedOperationalDisposition = closedWithoutAdequacy

------------------------------------------------------------------------
-- Regression 2: the same closed world plus a real FactorsThrough inhabitant.
------------------------------------------------------------------------

matureWorldWithWitnessIsAdequate :
  Query.AdequateFor
    Query.demoProject
    Query.demoSemantics
    Query.surfaceQuery
matureWorldWithWitnessIsAdequate =
  Bridge.demoFormalAdequacyRecovered

matureWorldTheoremDisposition :
  AdequacyCompileDisposition
matureWorldTheoremDisposition = theoremAdequate

------------------------------------------------------------------------
-- Regression 3: closed frontier, but projection erases time.
------------------------------------------------------------------------

data TimeWorld : Set where
  worldBefore : TimeWorld
  worldAfter : TimeWorld

data TimeErasedProjection : Set where
  sameVisibleSurface : TimeErasedProjection

data TimeQuery : Set where
  asAtSensitiveQuery : TimeQuery

data TimeAnswer : Set where
  beforeAnswer : TimeAnswer
  afterAnswer : TimeAnswer

timeErasedProject : TimeWorld → TimeErasedProjection
timeErasedProject worldBefore = sameVisibleSurface
timeErasedProject worldAfter = sameVisibleSurface

timeAnswer : TimeQuery → TimeWorld → TimeAnswer
timeAnswer asAtSensitiveQuery worldBefore = beforeAnswer
timeAnswer asAtSensitiveQuery worldAfter = afterAnswer

timeSemantics :
  Query.QuerySemantics TimeWorld TimeQuery TimeAnswer
timeSemantics =
  Query.querySemantics timeAnswer

timeErasureDefect :
  Query.QueryAdequacyDefect
    timeErasedProject
    timeSemantics
    asAtSensitiveQuery
timeErasureDefect =
  Query.queryAdequacyDefect
    worldBefore
    worldAfter
    refl
    (λ ())

timeErasureBlocksAdequacy :
  Query.AdequateFor
    timeErasedProject
    timeSemantics
    asAtSensitiveQuery → ⊥
timeErasureBlocksAdequacy =
  Query.queryAdequacyDefectBlocksFactorisation timeErasureDefect

closedTimeErasureResidual :
  Residual.ExactConsumerResidual
    timeErasedProject
    timeSemantics
    asAtSensitiveQuery
closedTimeErasureResidual =
  Residual.exactConsumerResidual
    Residual.temporal
    "world:as-at-coordinate"
    "DASHI.Law.ClosedIsNotAdequateExact"
    "timeErasureDefect"
    timeErasureDefect
    Residual.resolveTemporal
    refl
    true refl
    false refl
    false refl

closedTimeErasureReopensTemporalResearch :
  Residual.demandKind closedTimeErasureResidual ≡ Residual.resolveTemporal
closedTimeErasureReopensTemporalResearch = refl

closedTimeErasureDisposition :
  AdequacyCompileDisposition
closedTimeErasureDisposition = needsResearch

------------------------------------------------------------------------
-- Existing stop owner remains the terminal law.
------------------------------------------------------------------------

stopBoundary :
  Stop.ConsumerResearchAdmissibilityStopBoundary
stopBoundary =
  Stop.canonicalConsumerResearchAdmissibilityStopBoundary

record ClosedIsNotAdequateBoundary : Set where
  constructor closedIsNotAdequateBoundary
  field
    noFreshDemandIsConsumerAdequacyProof : Bool
    noFreshDemandIsConsumerAdequacyProofIsFalse :
      noFreshDemandIsConsumerAdequacyProof ≡ false

    kernelCheckedFactorsThroughMayCertifyAdequacy : Bool
    kernelCheckedFactorsThroughMayCertifyAdequacyIsTrue :
      kernelCheckedFactorsThroughMayCertifyAdequacy ≡ true

    exactNonfactorabilityMayReopenClosedFrontier : Bool
    exactNonfactorabilityMayReopenClosedFrontierIsTrue :
      exactNonfactorabilityMayReopenClosedFrontier ≡ true

    timeErasureMayBeIgnoredWhenFrontierClosed : Bool
    timeErasureMayBeIgnoredWhenFrontierClosedIsFalse :
      timeErasureMayBeIgnoredWhenFrontierClosed ≡ false

    reopenedResearchCreatesSemanticAuthority : Bool
    reopenedResearchCreatesSemanticAuthorityIsFalse :
      reopenedResearchCreatesSemanticAuthority ≡ false

    reopenedResearchCreatesClaimTruth : Bool
    reopenedResearchCreatesClaimTruthIsFalse :
      reopenedResearchCreatesClaimTruth ≡ false

open ClosedIsNotAdequateBoundary public

canonicalClosedIsNotAdequateBoundary :
  ClosedIsNotAdequateBoundary
canonicalClosedIsNotAdequateBoundary =
  closedIsNotAdequateBoundary
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
