module DASHI.Physics.Closure.NSSprint138AxialMonotonicityBlockerReductionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint136HouLuoSymmetricSourceSignReceipt as S136

------------------------------------------------------------------------
-- NS Sprint 138 axial-monotonicity blocker-reduction receipt.
--
-- This is a disjoint receipt surface.  It records the status of the
-- Sprint 137 AxialMonotonicityOfSwirlProfile gate after the blocker
-- reduction pass:
--
--   * the local v = partial_z u1 barrier is supported;
--   * global concavity of psi1 is still open and not proved;
--   * secondary peak exclusion is still open and not proved;
--   * transport commutator domination is still open and not proved;
--   * no global axial monotonicity theorem is promoted;
--   * no conditional BKM upgrade beyond Sprint 136 is promoted;
--   * full_clay_ns_solved and clayNavierStokesPromoted remain false.

sprint138AxialMonotonicityBlockerReductionLedgerClosed : Bool
sprint138AxialMonotonicityBlockerReductionLedgerClosed = true

sprint137GateConsumed : Bool
sprint137GateConsumed = true

AxialMonotonicityOfSwirlProfile : Bool
AxialMonotonicityOfSwirlProfile = false

AxialMonotonicityOfSwirlProfileStillOpen : Bool
AxialMonotonicityOfSwirlProfileStillOpen = true

localPartialZU1BarrierSupported : Bool
localPartialZU1BarrierSupported = true

local_v_equals_partial_z_u1_barrier_supported : Bool
local_v_equals_partial_z_u1_barrier_supported = true

globalConcavityOfPsi1Closed : Bool
globalConcavityOfPsi1Closed = false

globalConcavityOfPsi1Proved : Bool
globalConcavityOfPsi1Proved = false

globalConcavityOfPsi1Open : Bool
globalConcavityOfPsi1Open = true

secondaryPeakExclusionClosed : Bool
secondaryPeakExclusionClosed = false

secondaryPeakExclusionProved : Bool
secondaryPeakExclusionProved = false

secondaryPeakExclusionOpen : Bool
secondaryPeakExclusionOpen = true

transportCommutatorDominationClosed : Bool
transportCommutatorDominationClosed = false

transportCommutatorDominationProved : Bool
transportCommutatorDominationProved = false

transportCommutatorDominationOpen : Bool
transportCommutatorDominationOpen = true

globalAxialMonotonicityTheorem : Bool
globalAxialMonotonicityTheorem = false

globalAxialMonotonicityTheoremPromoted : Bool
globalAxialMonotonicityTheoremPromoted = false

noGlobalAxialMonotonicityTheorem : Bool
noGlobalAxialMonotonicityTheorem = true

conditionalBKMUpgradeBeyondSprint136 : Bool
conditionalBKMUpgradeBeyondSprint136 = false

noConditionalBKMUpgradeBeyondSprint136 : Bool
noConditionalBKMUpgradeBeyondSprint136 = true

full_clay_ns_solved : Bool
full_clay_ns_solved = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

sprint138KeepsFullClayNSFalse :
  full_clay_ns_solved ≡ false
sprint138KeepsFullClayNSFalse = refl

sprint138KeepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
sprint138KeepsClayPromotionFalse = refl

data AxialMonotonicityBlockerReductionStep : Set where
  consumeSprint137AxialMonotonicityGate :
    AxialMonotonicityBlockerReductionStep

  normalizeLocalVariableToPartialZU1 :
    AxialMonotonicityBlockerReductionStep

  recordLocalPartialZU1BarrierSupport :
    AxialMonotonicityBlockerReductionStep

  separateGlobalConcavityOfPsi1Blocker :
    AxialMonotonicityBlockerReductionStep

  separateSecondaryPeakExclusionBlocker :
    AxialMonotonicityBlockerReductionStep

  separateTransportCommutatorDominationBlocker :
    AxialMonotonicityBlockerReductionStep

  refuseGlobalAxialMonotonicityPromotion :
    AxialMonotonicityBlockerReductionStep

  refuseBKMUpgradeBeyondSprint136 :
    AxialMonotonicityBlockerReductionStep

  keepClayPromotionFlagsFalse :
    AxialMonotonicityBlockerReductionStep

canonicalAxialMonotonicityBlockerReductionSteps :
  List AxialMonotonicityBlockerReductionStep
canonicalAxialMonotonicityBlockerReductionSteps =
  consumeSprint137AxialMonotonicityGate
  ∷ normalizeLocalVariableToPartialZU1
  ∷ recordLocalPartialZU1BarrierSupport
  ∷ separateGlobalConcavityOfPsi1Blocker
  ∷ separateSecondaryPeakExclusionBlocker
  ∷ separateTransportCommutatorDominationBlocker
  ∷ refuseGlobalAxialMonotonicityPromotion
  ∷ refuseBKMUpgradeBeyondSprint136
  ∷ keepClayPromotionFlagsFalse
  ∷ []

data AxialMonotonicityOpenBoundary : Set where
  globalConcavityOfPsi1NotProvedHere :
    AxialMonotonicityOpenBoundary

  secondaryPeakExclusionNotProvedHere :
    AxialMonotonicityOpenBoundary

  transportCommutatorDominationNotProvedHere :
    AxialMonotonicityOpenBoundary

  axialMonotonicityOfSwirlProfileNotProvedHere :
    AxialMonotonicityOpenBoundary

  noGlobalAxialMonotonicityTheoremHere :
    AxialMonotonicityOpenBoundary

  noBKMUpgradeBeyondSprint136Here :
    AxialMonotonicityOpenBoundary

  noFullClayNavierStokesPromotionHere :
    AxialMonotonicityOpenBoundary

canonicalAxialMonotonicityOpenBoundaries :
  List AxialMonotonicityOpenBoundary
canonicalAxialMonotonicityOpenBoundaries =
  globalConcavityOfPsi1NotProvedHere
  ∷ secondaryPeakExclusionNotProvedHere
  ∷ transportCommutatorDominationNotProvedHere
  ∷ axialMonotonicityOfSwirlProfileNotProvedHere
  ∷ noGlobalAxialMonotonicityTheoremHere
  ∷ noBKMUpgradeBeyondSprint136Here
  ∷ noFullClayNavierStokesPromotionHere
  ∷ []

data AxialMonotonicityPromotion : Set where

axialMonotonicityPromotionImpossibleHere :
  AxialMonotonicityPromotion →
  ⊥
axialMonotonicityPromotionImpossibleHere ()

localBarrierStatement : String
localBarrierStatement =
  "Sprint 138 keeps the local v=partial_z u1 barrier supported after Sprint 137"

globalConcavityOpenStatement : String
globalConcavityOpenStatement =
  "Global concavity of psi1 remains open and is not proved by this receipt"

secondaryPeakOpenStatement : String
secondaryPeakOpenStatement =
  "Secondary peak exclusion remains open and is not proved by this receipt"

transportCommutatorOpenStatement : String
transportCommutatorOpenStatement =
  "Transport commutator domination remains open and is not proved by this receipt"

failClosedBoundaryStatement : String
failClosedBoundaryStatement =
  "No global axial monotonicity theorem, no BKM upgrade beyond Sprint136, and no Clay Navier-Stokes promotion are recorded"

record LocalPartialZU1BarrierSupport : Set where
  constructor localPartialZU1BarrierSupportReceipt
  field
    localVariableName :
      String
    localVariableNameIsCanonical :
      localVariableName ≡ "v=partial_z u1"
    localBarrierSupportStatement :
      String
    localBarrierSupportStatementIsCanonical :
      localBarrierSupportStatement ≡ localBarrierStatement
    localPartialZU1BarrierSupportedField :
      localPartialZU1BarrierSupported ≡ true
    local_v_equals_partial_z_u1_barrier_supportedField :
      local_v_equals_partial_z_u1_barrier_supported ≡ true

open LocalPartialZU1BarrierSupport public

canonicalLocalPartialZU1BarrierSupport :
  LocalPartialZU1BarrierSupport
canonicalLocalPartialZU1BarrierSupport =
  localPartialZU1BarrierSupportReceipt
    "v=partial_z u1"
    refl
    localBarrierStatement
    refl
    refl
    refl

record GlobalConcavityOfPsi1Boundary : Set where
  constructor globalConcavityOfPsi1BoundaryReceipt
  field
    boundaryStatement :
      String
    boundaryStatementIsCanonical :
      boundaryStatement ≡ globalConcavityOpenStatement
    globalConcavityOfPsi1ClosedField :
      globalConcavityOfPsi1Closed ≡ false
    globalConcavityOfPsi1ProvedField :
      globalConcavityOfPsi1Proved ≡ false
    globalConcavityOfPsi1OpenField :
      globalConcavityOfPsi1Open ≡ true

open GlobalConcavityOfPsi1Boundary public

canonicalGlobalConcavityOfPsi1Boundary :
  GlobalConcavityOfPsi1Boundary
canonicalGlobalConcavityOfPsi1Boundary =
  globalConcavityOfPsi1BoundaryReceipt
    globalConcavityOpenStatement
    refl
    refl
    refl
    refl

record SecondaryPeakExclusionBoundary : Set where
  constructor secondaryPeakExclusionBoundaryReceipt
  field
    boundaryStatement :
      String
    boundaryStatementIsCanonical :
      boundaryStatement ≡ secondaryPeakOpenStatement
    secondaryPeakExclusionClosedField :
      secondaryPeakExclusionClosed ≡ false
    secondaryPeakExclusionProvedField :
      secondaryPeakExclusionProved ≡ false
    secondaryPeakExclusionOpenField :
      secondaryPeakExclusionOpen ≡ true

open SecondaryPeakExclusionBoundary public

canonicalSecondaryPeakExclusionBoundary :
  SecondaryPeakExclusionBoundary
canonicalSecondaryPeakExclusionBoundary =
  secondaryPeakExclusionBoundaryReceipt
    secondaryPeakOpenStatement
    refl
    refl
    refl
    refl

record TransportCommutatorDominationBoundary : Set where
  constructor transportCommutatorDominationBoundaryReceipt
  field
    boundaryStatement :
      String
    boundaryStatementIsCanonical :
      boundaryStatement ≡ transportCommutatorOpenStatement
    transportCommutatorDominationClosedField :
      transportCommutatorDominationClosed ≡ false
    transportCommutatorDominationProvedField :
      transportCommutatorDominationProved ≡ false
    transportCommutatorDominationOpenField :
      transportCommutatorDominationOpen ≡ true

open TransportCommutatorDominationBoundary public

canonicalTransportCommutatorDominationBoundary :
  TransportCommutatorDominationBoundary
canonicalTransportCommutatorDominationBoundary =
  transportCommutatorDominationBoundaryReceipt
    transportCommutatorOpenStatement
    refl
    refl
    refl
    refl

record NoBKMUpgradeBeyondSprint136Boundary : Set where
  constructor noBKMUpgradeBeyondSprint136BoundaryReceipt
  field
    sprint136ConditionalBKMStatus :
      S136.conditionalBKMFiniteForCanonicalSymmetricScenario ≡ true
    sprint136ClayPromotionStillFalse :
      S136.clayNavierStokesPromoted ≡ false
    sprint138BKMUpgradeBeyondSprint136Field :
      conditionalBKMUpgradeBeyondSprint136 ≡ false
    sprint138NoBKMUpgradeBeyondSprint136Field :
      noConditionalBKMUpgradeBeyondSprint136 ≡ true

open NoBKMUpgradeBeyondSprint136Boundary public

canonicalNoBKMUpgradeBeyondSprint136Boundary :
  NoBKMUpgradeBeyondSprint136Boundary
canonicalNoBKMUpgradeBeyondSprint136Boundary =
  noBKMUpgradeBeyondSprint136BoundaryReceipt
    refl
    refl
    refl
    refl

record FailClosedAxialMonotonicityBoundary : Set where
  constructor failClosedAxialMonotonicityBoundaryReceipt
  field
    boundaryStatement :
      String
    boundaryStatementIsCanonical :
      boundaryStatement ≡ failClosedBoundaryStatement
    openBoundaries :
      List AxialMonotonicityOpenBoundary
    openBoundariesAreCanonical :
      openBoundaries ≡ canonicalAxialMonotonicityOpenBoundaries
    promotionFlags :
      List AxialMonotonicityPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []
    noPromotionPossibleHere :
      AxialMonotonicityPromotion →
      ⊥

open FailClosedAxialMonotonicityBoundary public

canonicalFailClosedAxialMonotonicityBoundary :
  FailClosedAxialMonotonicityBoundary
canonicalFailClosedAxialMonotonicityBoundary =
  failClosedAxialMonotonicityBoundaryReceipt
    failClosedBoundaryStatement
    refl
    canonicalAxialMonotonicityOpenBoundaries
    refl
    []
    refl
    axialMonotonicityPromotionImpossibleHere

record Sprint138AxialMonotonicityStatuses : Set where
  constructor sprint138AxialMonotonicityStatuses
  field
    ledgerClosedField :
      sprint138AxialMonotonicityBlockerReductionLedgerClosed ≡ true
    sprint137GateConsumedField :
      sprint137GateConsumed ≡ true
    axialMonotonicityField :
      AxialMonotonicityOfSwirlProfile ≡ false
    axialMonotonicityStillOpenField :
      AxialMonotonicityOfSwirlProfileStillOpen ≡ true
    localPartialZU1BarrierSupportedField :
      localPartialZU1BarrierSupported ≡ true
    globalConcavityOfPsi1ClosedField :
      globalConcavityOfPsi1Closed ≡ false
    globalConcavityOfPsi1ProvedField :
      globalConcavityOfPsi1Proved ≡ false
    globalConcavityOfPsi1OpenField :
      globalConcavityOfPsi1Open ≡ true
    secondaryPeakExclusionClosedField :
      secondaryPeakExclusionClosed ≡ false
    secondaryPeakExclusionProvedField :
      secondaryPeakExclusionProved ≡ false
    secondaryPeakExclusionOpenField :
      secondaryPeakExclusionOpen ≡ true
    transportCommutatorDominationClosedField :
      transportCommutatorDominationClosed ≡ false
    transportCommutatorDominationProvedField :
      transportCommutatorDominationProved ≡ false
    transportCommutatorDominationOpenField :
      transportCommutatorDominationOpen ≡ true
    globalAxialMonotonicityTheoremField :
      globalAxialMonotonicityTheorem ≡ false
    globalAxialMonotonicityTheoremPromotedField :
      globalAxialMonotonicityTheoremPromoted ≡ false
    noGlobalAxialMonotonicityTheoremField :
      noGlobalAxialMonotonicityTheorem ≡ true
    conditionalBKMUpgradeBeyondSprint136Field :
      conditionalBKMUpgradeBeyondSprint136 ≡ false
    noConditionalBKMUpgradeBeyondSprint136Field :
      noConditionalBKMUpgradeBeyondSprint136 ≡ true
    fullClayNSSolvedField :
      full_clay_ns_solved ≡ false
    clayPromotionField :
      clayNavierStokesPromoted ≡ false

open Sprint138AxialMonotonicityStatuses public

canonicalSprint138AxialMonotonicityStatuses :
  Sprint138AxialMonotonicityStatuses
canonicalSprint138AxialMonotonicityStatuses =
  sprint138AxialMonotonicityStatuses
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record NSSprint138AxialMonotonicityBlockerReductionReceipt : Set where
  constructor nsSprint138AxialMonotonicityBlockerReductionReceipt
  field
    localBarrier :
      LocalPartialZU1BarrierSupport
    globalConcavityBoundary :
      GlobalConcavityOfPsi1Boundary
    secondaryPeakBoundary :
      SecondaryPeakExclusionBoundary
    transportCommutatorBoundary :
      TransportCommutatorDominationBoundary
    bkmUpgradeBoundary :
      NoBKMUpgradeBeyondSprint136Boundary
    failClosedBoundary :
      FailClosedAxialMonotonicityBoundary
    statuses :
      Sprint138AxialMonotonicityStatuses
    statusesAreCanonical :
      statuses ≡ canonicalSprint138AxialMonotonicityStatuses
    steps :
      List AxialMonotonicityBlockerReductionStep
    stepsAreCanonical :
      steps ≡ canonicalAxialMonotonicityBlockerReductionSteps
    receiptSummary :
      String
    receiptSummaryIsCanonical :
      receiptSummary
      ≡
      "Sprint138 records blocker reduction for AxialMonotonicityOfSwirlProfile after Sprint137: the local v=partial_z u1 barrier is supported; global concavity of psi1, secondary peak exclusion, and transport commutator domination remain open; no global axial monotonicity theorem, no BKM upgrade beyond Sprint136, and no Clay promotion are made."

open NSSprint138AxialMonotonicityBlockerReductionReceipt public

canonicalNSSprint138AxialMonotonicityBlockerReductionReceipt :
  NSSprint138AxialMonotonicityBlockerReductionReceipt
canonicalNSSprint138AxialMonotonicityBlockerReductionReceipt =
  nsSprint138AxialMonotonicityBlockerReductionReceipt
    canonicalLocalPartialZU1BarrierSupport
    canonicalGlobalConcavityOfPsi1Boundary
    canonicalSecondaryPeakExclusionBoundary
    canonicalTransportCommutatorDominationBoundary
    canonicalNoBKMUpgradeBeyondSprint136Boundary
    canonicalFailClosedAxialMonotonicityBoundary
    canonicalSprint138AxialMonotonicityStatuses
    refl
    canonicalAxialMonotonicityBlockerReductionSteps
    refl
    "Sprint138 records blocker reduction for AxialMonotonicityOfSwirlProfile after Sprint137: the local v=partial_z u1 barrier is supported; global concavity of psi1, secondary peak exclusion, and transport commutator domination remain open; no global axial monotonicity theorem, no BKM upgrade beyond Sprint136, and no Clay promotion are made."
    refl

sprint138AxialMonotonicityBlockerReductionSummary :
  LocalPartialZU1BarrierSupport
  × GlobalConcavityOfPsi1Boundary
  × SecondaryPeakExclusionBoundary
  × TransportCommutatorDominationBoundary
  × NoBKMUpgradeBeyondSprint136Boundary
  × FailClosedAxialMonotonicityBoundary
  × Sprint138AxialMonotonicityStatuses
sprint138AxialMonotonicityBlockerReductionSummary =
  canonicalLocalPartialZU1BarrierSupport ,
  canonicalGlobalConcavityOfPsi1Boundary ,
  canonicalSecondaryPeakExclusionBoundary ,
  canonicalTransportCommutatorDominationBoundary ,
  canonicalNoBKMUpgradeBeyondSprint136Boundary ,
  canonicalFailClosedAxialMonotonicityBoundary ,
  canonicalSprint138AxialMonotonicityStatuses

sprint138AllRequiredStatuses :
  (sprint138AxialMonotonicityBlockerReductionLedgerClosed ≡ true)
  × (sprint137GateConsumed ≡ true)
  × (AxialMonotonicityOfSwirlProfile ≡ false)
  × (AxialMonotonicityOfSwirlProfileStillOpen ≡ true)
  × (localPartialZU1BarrierSupported ≡ true)
  × (local_v_equals_partial_z_u1_barrier_supported ≡ true)
  × (globalConcavityOfPsi1Closed ≡ false)
  × (globalConcavityOfPsi1Proved ≡ false)
  × (globalConcavityOfPsi1Open ≡ true)
  × (secondaryPeakExclusionClosed ≡ false)
  × (secondaryPeakExclusionProved ≡ false)
  × (secondaryPeakExclusionOpen ≡ true)
  × (transportCommutatorDominationClosed ≡ false)
  × (transportCommutatorDominationProved ≡ false)
  × (transportCommutatorDominationOpen ≡ true)
  × (globalAxialMonotonicityTheorem ≡ false)
  × (globalAxialMonotonicityTheoremPromoted ≡ false)
  × (noGlobalAxialMonotonicityTheorem ≡ true)
  × (conditionalBKMUpgradeBeyondSprint136 ≡ false)
  × (noConditionalBKMUpgradeBeyondSprint136 ≡ true)
  × (full_clay_ns_solved ≡ false)
  × (clayNavierStokesPromoted ≡ false)
sprint138AllRequiredStatuses =
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl

sprint138GlobalConcavityNotProved :
  globalConcavityOfPsi1Proved ≡ false
sprint138GlobalConcavityNotProved = refl

sprint138SecondaryPeakExclusionNotProved :
  secondaryPeakExclusionProved ≡ false
sprint138SecondaryPeakExclusionNotProved = refl

sprint138TransportCommutatorDominationNotProved :
  transportCommutatorDominationProved ≡ false
sprint138TransportCommutatorDominationNotProved = refl

sprint138NoGlobalAxialMonotonicityTheorem :
  globalAxialMonotonicityTheoremPromoted ≡ false
sprint138NoGlobalAxialMonotonicityTheorem = refl

sprint138NoConditionalBKMUpgradeBeyondSprint136 :
  conditionalBKMUpgradeBeyondSprint136 ≡ false
sprint138NoConditionalBKMUpgradeBeyondSprint136 = refl
