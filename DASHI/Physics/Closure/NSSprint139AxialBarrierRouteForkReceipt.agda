module DASHI.Physics.Closure.NSSprint139AxialBarrierRouteForkReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint138AxialMonotonicityBlockerReductionReceipt
  as S138

------------------------------------------------------------------------
-- NS Sprint 139 axial-barrier route-fork receipt.
--
-- This receipt records the route fork after Sprint 138:
--
--   * the local v-barrier support remains true;
--   * the fork does not promote global axial monotonicity;
--   * three blockers remain open:
--       GlobalConcavityOfPsi1,
--       SecondaryPeakExclusion,
--       TransportCommutatorDominationForVBarrier;
--   * conditional regularity is not promoted by this fork;
--   * full_clay_ns_solved and clayNavierStokesPromoted remain false.

sprint139AxialBarrierRouteForkLedgerClosed : Bool
sprint139AxialBarrierRouteForkLedgerClosed = true

sprint138RouteForkAnchorAccepted : Bool
sprint138RouteForkAnchorAccepted = true

routeForkAfterSprint138Recorded : Bool
routeForkAfterSprint138Recorded = true

localVBarrierSupport : Bool
localVBarrierSupport = true

local_v_barrier_support : Bool
local_v_barrier_support = true

GlobalConcavityOfPsi1 : Bool
GlobalConcavityOfPsi1 = false

GlobalConcavityOfPsi1Open : Bool
GlobalConcavityOfPsi1Open = true

SecondaryPeakExclusion : Bool
SecondaryPeakExclusion = false

SecondaryPeakExclusionOpen : Bool
SecondaryPeakExclusionOpen = true

TransportCommutatorDominationForVBarrier : Bool
TransportCommutatorDominationForVBarrier = false

TransportCommutatorDominationForVBarrierOpen : Bool
TransportCommutatorDominationForVBarrierOpen = true

globalAxialMonotonicity : Bool
globalAxialMonotonicity = false

globalAxialMonotonicityProved : Bool
globalAxialMonotonicityProved = false

globalAxialMonotonicityPromoted : Bool
globalAxialMonotonicityPromoted = false

conditionalRegularityPromoted : Bool
conditionalRegularityPromoted = false

conditionalRegularityNotPromoted : Bool
conditionalRegularityNotPromoted = true

full_clay_ns_solved : Bool
full_clay_ns_solved = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

sprint139KeepsFullClayNSFalse :
  full_clay_ns_solved ≡ false
sprint139KeepsFullClayNSFalse = refl

sprint139KeepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
sprint139KeepsClayPromotionFalse = refl

data AxialBarrierRouteForkStep : Set where
  inheritSprint138AxialMonotonicityBlockerReduction :
    AxialBarrierRouteForkStep

  keepLocalVBarrierSupportTrue :
    AxialBarrierRouteForkStep

  forkFromLocalBarrierToGlobalMonotonicityAttempt :
    AxialBarrierRouteForkStep

  recordGlobalConcavityOfPsi1Open :
    AxialBarrierRouteForkStep

  recordSecondaryPeakExclusionOpen :
    AxialBarrierRouteForkStep

  recordTransportCommutatorDominationForVBarrierOpen :
    AxialBarrierRouteForkStep

  refuseGlobalAxialMonotonicityPromotion :
    AxialBarrierRouteForkStep

  refuseConditionalRegularityPromotion :
    AxialBarrierRouteForkStep

  keepClayPromotionFlagsFalse :
    AxialBarrierRouteForkStep

canonicalAxialBarrierRouteForkSteps :
  List AxialBarrierRouteForkStep
canonicalAxialBarrierRouteForkSteps =
  inheritSprint138AxialMonotonicityBlockerReduction
  ∷ keepLocalVBarrierSupportTrue
  ∷ forkFromLocalBarrierToGlobalMonotonicityAttempt
  ∷ recordGlobalConcavityOfPsi1Open
  ∷ recordSecondaryPeakExclusionOpen
  ∷ recordTransportCommutatorDominationForVBarrierOpen
  ∷ refuseGlobalAxialMonotonicityPromotion
  ∷ refuseConditionalRegularityPromotion
  ∷ keepClayPromotionFlagsFalse
  ∷ []

data AxialBarrierRouteForkBlocker : Set where
  GlobalConcavityOfPsi1Blocker :
    AxialBarrierRouteForkBlocker

  SecondaryPeakExclusionBlocker :
    AxialBarrierRouteForkBlocker

  TransportCommutatorDominationForVBarrierBlocker :
    AxialBarrierRouteForkBlocker

canonicalAxialBarrierRouteForkBlockers :
  List AxialBarrierRouteForkBlocker
canonicalAxialBarrierRouteForkBlockers =
  GlobalConcavityOfPsi1Blocker
  ∷ SecondaryPeakExclusionBlocker
  ∷ TransportCommutatorDominationForVBarrierBlocker
  ∷ []

data AxialBarrierRouteForkOpenBoundary : Set where
  globalConcavityOfPsi1NotProvedHere :
    AxialBarrierRouteForkOpenBoundary

  secondaryPeakExclusionNotProvedHere :
    AxialBarrierRouteForkOpenBoundary

  transportCommutatorDominationForVBarrierNotProvedHere :
    AxialBarrierRouteForkOpenBoundary

  globalAxialMonotonicityNotProvedHere :
    AxialBarrierRouteForkOpenBoundary

  conditionalRegularityNotPromotedHere :
    AxialBarrierRouteForkOpenBoundary

  noFullClayNavierStokesPromotionHere :
    AxialBarrierRouteForkOpenBoundary

canonicalAxialBarrierRouteForkOpenBoundaries :
  List AxialBarrierRouteForkOpenBoundary
canonicalAxialBarrierRouteForkOpenBoundaries =
  globalConcavityOfPsi1NotProvedHere
  ∷ secondaryPeakExclusionNotProvedHere
  ∷ transportCommutatorDominationForVBarrierNotProvedHere
  ∷ globalAxialMonotonicityNotProvedHere
  ∷ conditionalRegularityNotPromotedHere
  ∷ noFullClayNavierStokesPromotionHere
  ∷ []

data AxialBarrierRouteForkPromotion : Set where

axialBarrierRouteForkPromotionImpossibleHere :
  AxialBarrierRouteForkPromotion →
  ⊥
axialBarrierRouteForkPromotionImpossibleHere ()

localVBarrierStatement : String
localVBarrierStatement =
  "Sprint139 keeps local v-barrier support true after the Sprint138 blocker-reduction receipt"

routeForkStatement : String
routeForkStatement =
  "Sprint139 forks from local v-barrier support toward global axial monotonicity but records no global theorem"

threeBlockerStatement : String
threeBlockerStatement =
  "The open blockers are GlobalConcavityOfPsi1, SecondaryPeakExclusion, and TransportCommutatorDominationForVBarrier"

promotionBoundaryStatement : String
promotionBoundaryStatement =
  "Conditional regularity, full Clay Navier-Stokes, and Clay promotion are not promoted by this route fork"

record Sprint138RouteForkAnchor : Set where
  constructor sprint138RouteForkAnchorReceipt
  field
    sprint138Receipt :
      S138.NSSprint138AxialMonotonicityBlockerReductionReceipt
    sprint138ReceiptIsCanonical :
      sprint138Receipt
      ≡ S138.canonicalNSSprint138AxialMonotonicityBlockerReductionReceipt
    sprint138LocalBarrierStillSupported :
      S138.localPartialZU1BarrierSupported ≡ true
    sprint138GlobalConcavityStillOpen :
      S138.globalConcavityOfPsi1Open ≡ true
    sprint138SecondaryPeakStillOpen :
      S138.secondaryPeakExclusionOpen ≡ true
    sprint138TransportCommutatorStillOpen :
      S138.transportCommutatorDominationOpen ≡ true
    sprint138NoGlobalAxialMonotonicity :
      S138.globalAxialMonotonicityTheorem ≡ false
    sprint138NoClayPromotion :
      S138.clayNavierStokesPromoted ≡ false

open Sprint138RouteForkAnchor public

canonicalSprint138RouteForkAnchor :
  Sprint138RouteForkAnchor
canonicalSprint138RouteForkAnchor =
  sprint138RouteForkAnchorReceipt
    S138.canonicalNSSprint138AxialMonotonicityBlockerReductionReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record LocalVBarrierSupportReceipt : Set where
  constructor localVBarrierSupportReceipt
  field
    localBarrierStatement :
      String
    localBarrierStatementIsCanonical :
      localBarrierStatement ≡ localVBarrierStatement
    localVBarrierSupportField :
      localVBarrierSupport ≡ true
    local_v_barrier_supportField :
      local_v_barrier_support ≡ true
    inheritedSprint138LocalBarrierSupport :
      S138.localPartialZU1BarrierSupported ≡ true

open LocalVBarrierSupportReceipt public

canonicalLocalVBarrierSupportReceipt :
  LocalVBarrierSupportReceipt
canonicalLocalVBarrierSupportReceipt =
  localVBarrierSupportReceipt
    localVBarrierStatement
    refl
    refl
    refl
    refl

record ThreeOpenAxialBarrierBlockers : Set where
  constructor threeOpenAxialBarrierBlockersReceipt
  field
    blockerStatement :
      String
    blockerStatementIsCanonical :
      blockerStatement ≡ threeBlockerStatement
    blockers :
      List AxialBarrierRouteForkBlocker
    blockersAreCanonical :
      blockers ≡ canonicalAxialBarrierRouteForkBlockers
    globalConcavityOfPsi1Field :
      GlobalConcavityOfPsi1 ≡ false
    globalConcavityOfPsi1OpenField :
      GlobalConcavityOfPsi1Open ≡ true
    secondaryPeakExclusionField :
      SecondaryPeakExclusion ≡ false
    secondaryPeakExclusionOpenField :
      SecondaryPeakExclusionOpen ≡ true
    transportCommutatorDominationForVBarrierField :
      TransportCommutatorDominationForVBarrier ≡ false
    transportCommutatorDominationForVBarrierOpenField :
      TransportCommutatorDominationForVBarrierOpen ≡ true

open ThreeOpenAxialBarrierBlockers public

canonicalThreeOpenAxialBarrierBlockers :
  ThreeOpenAxialBarrierBlockers
canonicalThreeOpenAxialBarrierBlockers =
  threeOpenAxialBarrierBlockersReceipt
    threeBlockerStatement
    refl
    canonicalAxialBarrierRouteForkBlockers
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record GlobalAxialMonotonicityNotPromoted : Set where
  constructor globalAxialMonotonicityNotPromotedReceipt
  field
    forkStatement :
      String
    forkStatementIsCanonical :
      forkStatement ≡ routeForkStatement
    globalAxialMonotonicityField :
      globalAxialMonotonicity ≡ false
    globalAxialMonotonicityProvedField :
      globalAxialMonotonicityProved ≡ false
    globalAxialMonotonicityPromotedField :
      globalAxialMonotonicityPromoted ≡ false
    inheritedSprint138NoGlobalAxialMonotonicity :
      S138.globalAxialMonotonicityTheorem ≡ false

open GlobalAxialMonotonicityNotPromoted public

canonicalGlobalAxialMonotonicityNotPromoted :
  GlobalAxialMonotonicityNotPromoted
canonicalGlobalAxialMonotonicityNotPromoted =
  globalAxialMonotonicityNotPromotedReceipt
    routeForkStatement
    refl
    refl
    refl
    refl
    refl

record NoConditionalRegularityPromotion : Set where
  constructor noConditionalRegularityPromotionReceipt
  field
    boundaryStatement :
      String
    boundaryStatementIsCanonical :
      boundaryStatement ≡ promotionBoundaryStatement
    conditionalRegularityPromotedField :
      conditionalRegularityPromoted ≡ false
    conditionalRegularityNotPromotedField :
      conditionalRegularityNotPromoted ≡ true
    fullClayNSSolvedField :
      full_clay_ns_solved ≡ false
    clayPromotionField :
      clayNavierStokesPromoted ≡ false
    inheritedSprint138NoBKMUpgrade :
      S138.conditionalBKMUpgradeBeyondSprint136 ≡ false

open NoConditionalRegularityPromotion public

canonicalNoConditionalRegularityPromotion :
  NoConditionalRegularityPromotion
canonicalNoConditionalRegularityPromotion =
  noConditionalRegularityPromotionReceipt
    promotionBoundaryStatement
    refl
    refl
    refl
    refl
    refl
    refl

record FailClosedAxialBarrierRouteForkBoundary : Set where
  constructor failClosedAxialBarrierRouteForkBoundaryReceipt
  field
    openBoundaries :
      List AxialBarrierRouteForkOpenBoundary
    openBoundariesAreCanonical :
      openBoundaries ≡ canonicalAxialBarrierRouteForkOpenBoundaries
    promotionFlags :
      List AxialBarrierRouteForkPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []
    noPromotionPossibleHere :
      AxialBarrierRouteForkPromotion →
      ⊥

open FailClosedAxialBarrierRouteForkBoundary public

canonicalFailClosedAxialBarrierRouteForkBoundary :
  FailClosedAxialBarrierRouteForkBoundary
canonicalFailClosedAxialBarrierRouteForkBoundary =
  failClosedAxialBarrierRouteForkBoundaryReceipt
    canonicalAxialBarrierRouteForkOpenBoundaries
    refl
    []
    refl
    axialBarrierRouteForkPromotionImpossibleHere

record Sprint139AxialBarrierRouteForkStatuses : Set where
  constructor sprint139AxialBarrierRouteForkStatuses
  field
    ledgerClosedField :
      sprint139AxialBarrierRouteForkLedgerClosed ≡ true
    sprint138RouteForkAnchorAcceptedField :
      sprint138RouteForkAnchorAccepted ≡ true
    routeForkAfterSprint138RecordedField :
      routeForkAfterSprint138Recorded ≡ true
    localVBarrierSupportField :
      localVBarrierSupport ≡ true
    local_v_barrier_supportField :
      local_v_barrier_support ≡ true
    globalConcavityOfPsi1Field :
      GlobalConcavityOfPsi1 ≡ false
    globalConcavityOfPsi1OpenField :
      GlobalConcavityOfPsi1Open ≡ true
    secondaryPeakExclusionField :
      SecondaryPeakExclusion ≡ false
    secondaryPeakExclusionOpenField :
      SecondaryPeakExclusionOpen ≡ true
    transportCommutatorDominationForVBarrierField :
      TransportCommutatorDominationForVBarrier ≡ false
    transportCommutatorDominationForVBarrierOpenField :
      TransportCommutatorDominationForVBarrierOpen ≡ true
    globalAxialMonotonicityField :
      globalAxialMonotonicity ≡ false
    globalAxialMonotonicityProvedField :
      globalAxialMonotonicityProved ≡ false
    globalAxialMonotonicityPromotedField :
      globalAxialMonotonicityPromoted ≡ false
    conditionalRegularityPromotedField :
      conditionalRegularityPromoted ≡ false
    conditionalRegularityNotPromotedField :
      conditionalRegularityNotPromoted ≡ true
    fullClayNSSolvedField :
      full_clay_ns_solved ≡ false
    clayPromotionField :
      clayNavierStokesPromoted ≡ false

open Sprint139AxialBarrierRouteForkStatuses public

canonicalSprint139AxialBarrierRouteForkStatuses :
  Sprint139AxialBarrierRouteForkStatuses
canonicalSprint139AxialBarrierRouteForkStatuses =
  sprint139AxialBarrierRouteForkStatuses
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

record NSSprint139AxialBarrierRouteForkReceipt : Set where
  constructor nsSprint139AxialBarrierRouteForkReceipt
  field
    sprint138Anchor :
      Sprint138RouteForkAnchor
    localBarrier :
      LocalVBarrierSupportReceipt
    threeOpenBlockers :
      ThreeOpenAxialBarrierBlockers
    noGlobalAxialMonotonicity :
      GlobalAxialMonotonicityNotPromoted
    noConditionalRegularityPromotion :
      NoConditionalRegularityPromotion
    failClosedBoundary :
      FailClosedAxialBarrierRouteForkBoundary
    statuses :
      Sprint139AxialBarrierRouteForkStatuses
    statusesAreCanonical :
      statuses ≡ canonicalSprint139AxialBarrierRouteForkStatuses
    steps :
      List AxialBarrierRouteForkStep
    stepsAreCanonical :
      steps ≡ canonicalAxialBarrierRouteForkSteps
    receiptSummary :
      String
    receiptSummaryIsCanonical :
      receiptSummary
      ≡
      "Sprint139 forks the axial-barrier route after Sprint138: local v-barrier support stays true; GlobalConcavityOfPsi1, SecondaryPeakExclusion, and TransportCommutatorDominationForVBarrier remain open; global axial monotonicity and conditional regularity are not promoted; full_clay_ns_solved and clayNavierStokesPromoted remain false."

open NSSprint139AxialBarrierRouteForkReceipt public

canonicalNSSprint139AxialBarrierRouteForkReceipt :
  NSSprint139AxialBarrierRouteForkReceipt
canonicalNSSprint139AxialBarrierRouteForkReceipt =
  nsSprint139AxialBarrierRouteForkReceipt
    canonicalSprint138RouteForkAnchor
    canonicalLocalVBarrierSupportReceipt
    canonicalThreeOpenAxialBarrierBlockers
    canonicalGlobalAxialMonotonicityNotPromoted
    canonicalNoConditionalRegularityPromotion
    canonicalFailClosedAxialBarrierRouteForkBoundary
    canonicalSprint139AxialBarrierRouteForkStatuses
    refl
    canonicalAxialBarrierRouteForkSteps
    refl
    "Sprint139 forks the axial-barrier route after Sprint138: local v-barrier support stays true; GlobalConcavityOfPsi1, SecondaryPeakExclusion, and TransportCommutatorDominationForVBarrier remain open; global axial monotonicity and conditional regularity are not promoted; full_clay_ns_solved and clayNavierStokesPromoted remain false."
    refl

sprint139AxialBarrierRouteForkSummary :
  Sprint138RouteForkAnchor
  × LocalVBarrierSupportReceipt
  × ThreeOpenAxialBarrierBlockers
  × GlobalAxialMonotonicityNotPromoted
  × NoConditionalRegularityPromotion
  × FailClosedAxialBarrierRouteForkBoundary
  × Sprint139AxialBarrierRouteForkStatuses
sprint139AxialBarrierRouteForkSummary =
  canonicalSprint138RouteForkAnchor ,
  canonicalLocalVBarrierSupportReceipt ,
  canonicalThreeOpenAxialBarrierBlockers ,
  canonicalGlobalAxialMonotonicityNotPromoted ,
  canonicalNoConditionalRegularityPromotion ,
  canonicalFailClosedAxialBarrierRouteForkBoundary ,
  canonicalSprint139AxialBarrierRouteForkStatuses

sprint139AllRequiredStatuses :
  (sprint139AxialBarrierRouteForkLedgerClosed ≡ true)
  × (sprint138RouteForkAnchorAccepted ≡ true)
  × (routeForkAfterSprint138Recorded ≡ true)
  × (localVBarrierSupport ≡ true)
  × (local_v_barrier_support ≡ true)
  × (GlobalConcavityOfPsi1 ≡ false)
  × (GlobalConcavityOfPsi1Open ≡ true)
  × (SecondaryPeakExclusion ≡ false)
  × (SecondaryPeakExclusionOpen ≡ true)
  × (TransportCommutatorDominationForVBarrier ≡ false)
  × (TransportCommutatorDominationForVBarrierOpen ≡ true)
  × (globalAxialMonotonicity ≡ false)
  × (globalAxialMonotonicityProved ≡ false)
  × (globalAxialMonotonicityPromoted ≡ false)
  × (conditionalRegularityPromoted ≡ false)
  × (conditionalRegularityNotPromoted ≡ true)
  × (full_clay_ns_solved ≡ false)
  × (clayNavierStokesPromoted ≡ false)
sprint139AllRequiredStatuses =
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
