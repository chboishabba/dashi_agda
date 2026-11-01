module DASHI.Physics.Closure.NSSprint140ConditionalBarrierAssemblyReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint139AxialBarrierRouteForkReceipt as S139

------------------------------------------------------------------------
-- NS Sprint 140 conditional barrier-assembly receipt.
--
-- This receipt records the post-Sprint139 conditional assembly:
--
--   * it anchors to the canonical Sprint139 axial-barrier route fork;
--   * it assumes/provides the three Sprint139 open blockers compatibly:
--       GlobalConcavityOfPsi1,
--       SecondaryPeakExclusion,
--       TransportCommutatorDominationForVBarrier;
--   * under those three inputs, the local v-barrier feeds a conditional
--     monitored-route regularity surface;
--   * it does not promote unconditional global axial monotonicity;
--   * it does not construct a full Navier-Stokes solution;
--   * it does not promote the Clay Navier-Stokes claim.

sprint140ConditionalBarrierAssemblyLedgerClosed : Bool
sprint140ConditionalBarrierAssemblyLedgerClosed = true

sprint139CanonicalReceiptAnchored : Bool
sprint139CanonicalReceiptAnchored = true

postSprint139ConditionalAssemblyRecorded : Bool
postSprint139ConditionalAssemblyRecorded = true

localVBarrierFeedAccepted : Bool
localVBarrierFeedAccepted = true

local_v_barrier_can_feed_conditional_monitored_route : Bool
local_v_barrier_can_feed_conditional_monitored_route = true

GlobalConcavityOfPsi1Assumed : Bool
GlobalConcavityOfPsi1Assumed = true

GlobalConcavityOfPsi1ProvidedCompatibly : Bool
GlobalConcavityOfPsi1ProvidedCompatibly = true

SecondaryPeakExclusionAssumed : Bool
SecondaryPeakExclusionAssumed = true

SecondaryPeakExclusionProvidedCompatibly : Bool
SecondaryPeakExclusionProvidedCompatibly = true

TransportCommutatorDominationForVBarrierAssumed : Bool
TransportCommutatorDominationForVBarrierAssumed = true

TransportCommutatorDominationForVBarrierProvidedCompatibly : Bool
TransportCommutatorDominationForVBarrierProvidedCompatibly = true

threeConditionalInputsProvidedCompatibly : Bool
threeConditionalInputsProvidedCompatibly = true

conditionalMonitoredRouteRegularitySurfaceAvailable : Bool
conditionalMonitoredRouteRegularitySurfaceAvailable = true

conditionalMonitoredRouteRegularitySurfaceOnly : Bool
conditionalMonitoredRouteRegularitySurfaceOnly = true

conditionalRegularitySurfacePromotedUnconditionally : Bool
conditionalRegularitySurfacePromotedUnconditionally = false

globalAxialMonotonicity : Bool
globalAxialMonotonicity = false

globalAxialMonotonicityProved : Bool
globalAxialMonotonicityProved = false

globalAxialMonotonicityPromoted : Bool
globalAxialMonotonicityPromoted = false

unconditionalGlobalAxialMonotonicityPromoted : Bool
unconditionalGlobalAxialMonotonicityPromoted = false

fullNavierStokesSolutionConstructed : Bool
fullNavierStokesSolutionConstructed = false

full_clay_ns_solved : Bool
full_clay_ns_solved = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

sprint140KeepsGlobalAxialMonotonicityFalse :
  globalAxialMonotonicityPromoted ≡ false
sprint140KeepsGlobalAxialMonotonicityFalse = refl

sprint140KeepsFullNSSolutionFalse :
  fullNavierStokesSolutionConstructed ≡ false
sprint140KeepsFullNSSolutionFalse = refl

sprint140KeepsFullClayNSFalse :
  full_clay_ns_solved ≡ false
sprint140KeepsFullClayNSFalse = refl

sprint140KeepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
sprint140KeepsClayPromotionFalse = refl

data ConditionalBarrierAssemblyStep : Set where
  anchorSprint139CanonicalAxialBarrierRouteFork :
    ConditionalBarrierAssemblyStep

  acceptLocalVBarrierFeed :
    ConditionalBarrierAssemblyStep

  assumeGlobalConcavityOfPsi1Compatibly :
    ConditionalBarrierAssemblyStep

  assumeSecondaryPeakExclusionCompatibly :
    ConditionalBarrierAssemblyStep

  assumeTransportCommutatorDominationForVBarrierCompatibly :
    ConditionalBarrierAssemblyStep

  assembleConditionalMonitoredRoute :
    ConditionalBarrierAssemblyStep

  exposeConditionalRegularitySurface :
    ConditionalBarrierAssemblyStep

  refuseUnconditionalGlobalAxialMonotonicity :
    ConditionalBarrierAssemblyStep

  refuseFullNavierStokesSolutionClaim :
    ConditionalBarrierAssemblyStep

  keepClayPromotionFlagsFalse :
    ConditionalBarrierAssemblyStep

canonicalConditionalBarrierAssemblySteps :
  List ConditionalBarrierAssemblyStep
canonicalConditionalBarrierAssemblySteps =
  anchorSprint139CanonicalAxialBarrierRouteFork
  ∷ acceptLocalVBarrierFeed
  ∷ assumeGlobalConcavityOfPsi1Compatibly
  ∷ assumeSecondaryPeakExclusionCompatibly
  ∷ assumeTransportCommutatorDominationForVBarrierCompatibly
  ∷ assembleConditionalMonitoredRoute
  ∷ exposeConditionalRegularitySurface
  ∷ refuseUnconditionalGlobalAxialMonotonicity
  ∷ refuseFullNavierStokesSolutionClaim
  ∷ keepClayPromotionFlagsFalse
  ∷ []

data ConditionalBarrierAssemblyInput : Set where
  GlobalConcavityOfPsi1Input :
    ConditionalBarrierAssemblyInput

  SecondaryPeakExclusionInput :
    ConditionalBarrierAssemblyInput

  TransportCommutatorDominationForVBarrierInput :
    ConditionalBarrierAssemblyInput

canonicalConditionalBarrierAssemblyInputs :
  List ConditionalBarrierAssemblyInput
canonicalConditionalBarrierAssemblyInputs =
  GlobalConcavityOfPsi1Input
  ∷ SecondaryPeakExclusionInput
  ∷ TransportCommutatorDominationForVBarrierInput
  ∷ []

data ConditionalBarrierAssemblyBoundary : Set where
  conditionalSurfaceDependsOnThreeInputs :
    ConditionalBarrierAssemblyBoundary

  noUnconditionalGlobalAxialMonotonicityHere :
    ConditionalBarrierAssemblyBoundary

  noFullNavierStokesSolutionHere :
    ConditionalBarrierAssemblyBoundary

  noClayPromotionHere :
    ConditionalBarrierAssemblyBoundary

canonicalConditionalBarrierAssemblyBoundaries :
  List ConditionalBarrierAssemblyBoundary
canonicalConditionalBarrierAssemblyBoundaries =
  conditionalSurfaceDependsOnThreeInputs
  ∷ noUnconditionalGlobalAxialMonotonicityHere
  ∷ noFullNavierStokesSolutionHere
  ∷ noClayPromotionHere
  ∷ []

data ConditionalBarrierAssemblyUnconditionalPromotion : Set where

conditionalBarrierAssemblyUnconditionalPromotionImpossibleHere :
  ConditionalBarrierAssemblyUnconditionalPromotion →
  ⊥
conditionalBarrierAssemblyUnconditionalPromotionImpossibleHere ()

sprint139AnchorStatement : String
sprint139AnchorStatement =
  "Sprint140 anchors to canonical Sprint139 axial-barrier route fork receipt"

conditionalInputsStatement : String
conditionalInputsStatement =
  "GlobalConcavityOfPsi1, SecondaryPeakExclusion, and TransportCommutatorDominationForVBarrier are assumed/provided compatibly as conditional inputs"

conditionalSurfaceStatement : String
conditionalSurfaceStatement =
  "With the three compatible inputs, local v-barrier support feeds a conditional monitored-route regularity surface"

promotionBoundaryStatement : String
promotionBoundaryStatement =
  "The assembly is conditional only: no unconditional global axial monotonicity, no full Navier-Stokes solution, and no Clay promotion are recorded"

record Sprint139CanonicalAnchor : Set where
  constructor sprint139CanonicalAnchorReceipt
  field
    anchorStatement :
      String
    anchorStatementIsCanonical :
      anchorStatement ≡ sprint139AnchorStatement
    sprint139Receipt :
      S139.NSSprint139AxialBarrierRouteForkReceipt
    sprint139ReceiptIsCanonical :
      sprint139Receipt ≡ S139.canonicalNSSprint139AxialBarrierRouteForkReceipt
    sprint139LocalBarrierSupport :
      S139.localVBarrierSupport ≡ true
    sprint139GlobalConcavityWasOpen :
      S139.GlobalConcavityOfPsi1Open ≡ true
    sprint139SecondaryPeakWasOpen :
      S139.SecondaryPeakExclusionOpen ≡ true
    sprint139TransportCommutatorWasOpen :
      S139.TransportCommutatorDominationForVBarrierOpen ≡ true
    sprint139NoGlobalAxialMonotonicity :
      S139.globalAxialMonotonicityPromoted ≡ false
    sprint139NoConditionalRegularityPromotion :
      S139.conditionalRegularityPromoted ≡ false
    sprint139NoClayPromotion :
      S139.clayNavierStokesPromoted ≡ false

open Sprint139CanonicalAnchor public

canonicalSprint139CanonicalAnchor :
  Sprint139CanonicalAnchor
canonicalSprint139CanonicalAnchor =
  sprint139CanonicalAnchorReceipt
    sprint139AnchorStatement
    refl
    S139.canonicalNSSprint139AxialBarrierRouteForkReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record CompatibleConditionalBarrierInputs : Set where
  constructor compatibleConditionalBarrierInputsReceipt
  field
    inputStatement :
      String
    inputStatementIsCanonical :
      inputStatement ≡ conditionalInputsStatement
    inputs :
      List ConditionalBarrierAssemblyInput
    inputsAreCanonical :
      inputs ≡ canonicalConditionalBarrierAssemblyInputs
    globalConcavityAssumedField :
      GlobalConcavityOfPsi1Assumed ≡ true
    globalConcavityProvidedCompatiblyField :
      GlobalConcavityOfPsi1ProvidedCompatibly ≡ true
    secondaryPeakAssumedField :
      SecondaryPeakExclusionAssumed ≡ true
    secondaryPeakProvidedCompatiblyField :
      SecondaryPeakExclusionProvidedCompatibly ≡ true
    transportCommutatorAssumedField :
      TransportCommutatorDominationForVBarrierAssumed ≡ true
    transportCommutatorProvidedCompatiblyField :
      TransportCommutatorDominationForVBarrierProvidedCompatibly ≡ true
    allInputsProvidedCompatiblyField :
      threeConditionalInputsProvidedCompatibly ≡ true

open CompatibleConditionalBarrierInputs public

canonicalCompatibleConditionalBarrierInputs :
  CompatibleConditionalBarrierInputs
canonicalCompatibleConditionalBarrierInputs =
  compatibleConditionalBarrierInputsReceipt
    conditionalInputsStatement
    refl
    canonicalConditionalBarrierAssemblyInputs
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record ConditionalMonitoredRouteRegularitySurface : Set where
  constructor conditionalMonitoredRouteRegularitySurfaceReceipt
  field
    surfaceStatement :
      String
    surfaceStatementIsCanonical :
      surfaceStatement ≡ conditionalSurfaceStatement
    anchor :
      Sprint139CanonicalAnchor
    anchorIsCanonical :
      anchor ≡ canonicalSprint139CanonicalAnchor
    compatibleInputs :
      CompatibleConditionalBarrierInputs
    compatibleInputsAreCanonical :
      compatibleInputs ≡ canonicalCompatibleConditionalBarrierInputs
    localVBarrierFeedAcceptedField :
      localVBarrierFeedAccepted ≡ true
    localBarrierCanFeedConditionalRouteField :
      local_v_barrier_can_feed_conditional_monitored_route ≡ true
    conditionalSurfaceAvailableField :
      conditionalMonitoredRouteRegularitySurfaceAvailable ≡ true
    conditionalSurfaceOnlyField :
      conditionalMonitoredRouteRegularitySurfaceOnly ≡ true
    unconditionalSurfacePromotionField :
      conditionalRegularitySurfacePromotedUnconditionally ≡ false

open ConditionalMonitoredRouteRegularitySurface public

canonicalConditionalMonitoredRouteRegularitySurface :
  ConditionalMonitoredRouteRegularitySurface
canonicalConditionalMonitoredRouteRegularitySurface =
  conditionalMonitoredRouteRegularitySurfaceReceipt
    conditionalSurfaceStatement
    refl
    canonicalSprint139CanonicalAnchor
    refl
    canonicalCompatibleConditionalBarrierInputs
    refl
    refl
    refl
    refl
    refl
    refl

assembleConditionalMonitoredRouteSurfaceFromCanonicalInputs :
  (inputs : CompatibleConditionalBarrierInputs) →
  inputs ≡ canonicalCompatibleConditionalBarrierInputs →
  ConditionalMonitoredRouteRegularitySurface
assembleConditionalMonitoredRouteSurfaceFromCanonicalInputs inputs inputsAreCanonical =
  conditionalMonitoredRouteRegularitySurfaceReceipt
    conditionalSurfaceStatement
    refl
    canonicalSprint139CanonicalAnchor
    refl
    inputs
    inputsAreCanonical
    refl
    refl
    refl
    refl
    refl

canonicalConditionalAssemblyComputation :
  assembleConditionalMonitoredRouteSurfaceFromCanonicalInputs
    canonicalCompatibleConditionalBarrierInputs
    refl
  ≡ canonicalConditionalMonitoredRouteRegularitySurface
canonicalConditionalAssemblyComputation = refl

record ConditionalOnlyPromotionBoundary : Set where
  constructor conditionalOnlyPromotionBoundaryReceipt
  field
    boundaryStatement :
      String
    boundaryStatementIsCanonical :
      boundaryStatement ≡ promotionBoundaryStatement
    boundaries :
      List ConditionalBarrierAssemblyBoundary
    boundariesAreCanonical :
      boundaries ≡ canonicalConditionalBarrierAssemblyBoundaries
    globalAxialMonotonicityField :
      globalAxialMonotonicity ≡ false
    globalAxialMonotonicityProvedField :
      globalAxialMonotonicityProved ≡ false
    globalAxialMonotonicityPromotedField :
      globalAxialMonotonicityPromoted ≡ false
    unconditionalGlobalAxialMonotonicityPromotedField :
      unconditionalGlobalAxialMonotonicityPromoted ≡ false
    fullNavierStokesSolutionConstructedField :
      fullNavierStokesSolutionConstructed ≡ false
    fullClayNSSolvedField :
      full_clay_ns_solved ≡ false
    clayPromotionField :
      clayNavierStokesPromoted ≡ false
    unconditionalPromotionFlags :
      List ConditionalBarrierAssemblyUnconditionalPromotion
    unconditionalPromotionFlagsAreEmpty :
      unconditionalPromotionFlags ≡ []
    noUnconditionalPromotionPossibleHere :
      ConditionalBarrierAssemblyUnconditionalPromotion →
      ⊥

open ConditionalOnlyPromotionBoundary public

canonicalConditionalOnlyPromotionBoundary :
  ConditionalOnlyPromotionBoundary
canonicalConditionalOnlyPromotionBoundary =
  conditionalOnlyPromotionBoundaryReceipt
    promotionBoundaryStatement
    refl
    canonicalConditionalBarrierAssemblyBoundaries
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    []
    refl
    conditionalBarrierAssemblyUnconditionalPromotionImpossibleHere

record Sprint140ConditionalBarrierAssemblyStatuses : Set where
  constructor sprint140ConditionalBarrierAssemblyStatuses
  field
    ledgerClosedField :
      sprint140ConditionalBarrierAssemblyLedgerClosed ≡ true
    sprint139CanonicalReceiptAnchoredField :
      sprint139CanonicalReceiptAnchored ≡ true
    postSprint139ConditionalAssemblyRecordedField :
      postSprint139ConditionalAssemblyRecorded ≡ true
    localVBarrierFeedAcceptedField :
      localVBarrierFeedAccepted ≡ true
    localBarrierCanFeedConditionalRouteField :
      local_v_barrier_can_feed_conditional_monitored_route ≡ true
    globalConcavityAssumedField :
      GlobalConcavityOfPsi1Assumed ≡ true
    globalConcavityProvidedCompatiblyField :
      GlobalConcavityOfPsi1ProvidedCompatibly ≡ true
    secondaryPeakAssumedField :
      SecondaryPeakExclusionAssumed ≡ true
    secondaryPeakProvidedCompatiblyField :
      SecondaryPeakExclusionProvidedCompatibly ≡ true
    transportCommutatorAssumedField :
      TransportCommutatorDominationForVBarrierAssumed ≡ true
    transportCommutatorProvidedCompatiblyField :
      TransportCommutatorDominationForVBarrierProvidedCompatibly ≡ true
    allInputsProvidedCompatiblyField :
      threeConditionalInputsProvidedCompatibly ≡ true
    conditionalSurfaceAvailableField :
      conditionalMonitoredRouteRegularitySurfaceAvailable ≡ true
    conditionalSurfaceOnlyField :
      conditionalMonitoredRouteRegularitySurfaceOnly ≡ true
    unconditionalSurfacePromotionField :
      conditionalRegularitySurfacePromotedUnconditionally ≡ false
    globalAxialMonotonicityField :
      globalAxialMonotonicity ≡ false
    globalAxialMonotonicityProvedField :
      globalAxialMonotonicityProved ≡ false
    globalAxialMonotonicityPromotedField :
      globalAxialMonotonicityPromoted ≡ false
    unconditionalGlobalAxialMonotonicityPromotedField :
      unconditionalGlobalAxialMonotonicityPromoted ≡ false
    fullNavierStokesSolutionConstructedField :
      fullNavierStokesSolutionConstructed ≡ false
    fullClayNSSolvedField :
      full_clay_ns_solved ≡ false
    clayPromotionField :
      clayNavierStokesPromoted ≡ false

open Sprint140ConditionalBarrierAssemblyStatuses public

canonicalSprint140ConditionalBarrierAssemblyStatuses :
  Sprint140ConditionalBarrierAssemblyStatuses
canonicalSprint140ConditionalBarrierAssemblyStatuses =
  sprint140ConditionalBarrierAssemblyStatuses
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
    refl

record NSSprint140ConditionalBarrierAssemblyReceipt : Set where
  constructor nsSprint140ConditionalBarrierAssemblyReceipt
  field
    sprint139Anchor :
      Sprint139CanonicalAnchor
    compatibleInputs :
      CompatibleConditionalBarrierInputs
    conditionalSurface :
      ConditionalMonitoredRouteRegularitySurface
    conditionalBoundary :
      ConditionalOnlyPromotionBoundary
    statuses :
      Sprint140ConditionalBarrierAssemblyStatuses
    statusesAreCanonical :
      statuses ≡ canonicalSprint140ConditionalBarrierAssemblyStatuses
    steps :
      List ConditionalBarrierAssemblyStep
    stepsAreCanonical :
      steps ≡ canonicalConditionalBarrierAssemblySteps
    receiptSummary :
      String
    receiptSummaryIsCanonical :
      receiptSummary
      ≡
      "Sprint140 conditionally assembles the post-Sprint139 local v-barrier route: if GlobalConcavityOfPsi1, SecondaryPeakExclusion, and TransportCommutatorDominationForVBarrier are provided compatibly, then local v-barrier support feeds a conditional monitored-route regularity surface; no unconditional global axial monotonicity, full Navier-Stokes solution, or Clay promotion is recorded."

open NSSprint140ConditionalBarrierAssemblyReceipt public

canonicalNSSprint140ConditionalBarrierAssemblyReceipt :
  NSSprint140ConditionalBarrierAssemblyReceipt
canonicalNSSprint140ConditionalBarrierAssemblyReceipt =
  nsSprint140ConditionalBarrierAssemblyReceipt
    canonicalSprint139CanonicalAnchor
    canonicalCompatibleConditionalBarrierInputs
    canonicalConditionalMonitoredRouteRegularitySurface
    canonicalConditionalOnlyPromotionBoundary
    canonicalSprint140ConditionalBarrierAssemblyStatuses
    refl
    canonicalConditionalBarrierAssemblySteps
    refl
    "Sprint140 conditionally assembles the post-Sprint139 local v-barrier route: if GlobalConcavityOfPsi1, SecondaryPeakExclusion, and TransportCommutatorDominationForVBarrier are provided compatibly, then local v-barrier support feeds a conditional monitored-route regularity surface; no unconditional global axial monotonicity, full Navier-Stokes solution, or Clay promotion is recorded."
    refl

sprint140ConditionalBarrierAssemblySummary :
  Sprint139CanonicalAnchor
  × CompatibleConditionalBarrierInputs
  × ConditionalMonitoredRouteRegularitySurface
  × ConditionalOnlyPromotionBoundary
  × Sprint140ConditionalBarrierAssemblyStatuses
sprint140ConditionalBarrierAssemblySummary =
  canonicalSprint139CanonicalAnchor ,
  canonicalCompatibleConditionalBarrierInputs ,
  canonicalConditionalMonitoredRouteRegularitySurface ,
  canonicalConditionalOnlyPromotionBoundary ,
  canonicalSprint140ConditionalBarrierAssemblyStatuses

sprint140AllRequiredStatuses :
  (sprint140ConditionalBarrierAssemblyLedgerClosed ≡ true)
  × (sprint139CanonicalReceiptAnchored ≡ true)
  × (postSprint139ConditionalAssemblyRecorded ≡ true)
  × (localVBarrierFeedAccepted ≡ true)
  × (local_v_barrier_can_feed_conditional_monitored_route ≡ true)
  × (GlobalConcavityOfPsi1Assumed ≡ true)
  × (GlobalConcavityOfPsi1ProvidedCompatibly ≡ true)
  × (SecondaryPeakExclusionAssumed ≡ true)
  × (SecondaryPeakExclusionProvidedCompatibly ≡ true)
  × (TransportCommutatorDominationForVBarrierAssumed ≡ true)
  × (TransportCommutatorDominationForVBarrierProvidedCompatibly ≡ true)
  × (threeConditionalInputsProvidedCompatibly ≡ true)
  × (conditionalMonitoredRouteRegularitySurfaceAvailable ≡ true)
  × (conditionalMonitoredRouteRegularitySurfaceOnly ≡ true)
  × (conditionalRegularitySurfacePromotedUnconditionally ≡ false)
  × (globalAxialMonotonicity ≡ false)
  × (globalAxialMonotonicityProved ≡ false)
  × (globalAxialMonotonicityPromoted ≡ false)
  × (unconditionalGlobalAxialMonotonicityPromoted ≡ false)
  × (fullNavierStokesSolutionConstructed ≡ false)
  × (full_clay_ns_solved ≡ false)
  × (clayNavierStokesPromoted ≡ false)
sprint140AllRequiredStatuses =
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

sprint140ConditionalSurfaceAvailable :
  conditionalMonitoredRouteRegularitySurfaceAvailable ≡ true
sprint140ConditionalSurfaceAvailable = refl

sprint140NoUnconditionalGlobalAxialMonotonicity :
  unconditionalGlobalAxialMonotonicityPromoted ≡ false
sprint140NoUnconditionalGlobalAxialMonotonicity = refl

sprint140NoFullNavierStokesSolution :
  fullNavierStokesSolutionConstructed ≡ false
sprint140NoFullNavierStokesSolution = refl

sprint140NoClayPromotion :
  clayNavierStokesPromoted ≡ false
sprint140NoClayPromotion = refl
