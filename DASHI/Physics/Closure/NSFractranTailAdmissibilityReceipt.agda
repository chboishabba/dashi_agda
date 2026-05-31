module DASHI.Physics.Closure.NSFractranTailAdmissibilityReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Combinatorics.FractranCOL as FractranCOL

------------------------------------------------------------------------
-- FRACTRAN-to-NS tail admissibility receipt.
--
-- DASHI.Combinatorics.FractranCOL supplies a five-lane exponent-vector
-- carrier over primes 2,3,5,7,11, with rules r1122/r53/r17 and rank/energy
-- E using the active lanes for primes 2,3,7.  This receipt records only the
-- carrier-side consequence for the NS tail-dominance candidate.
--
-- Sharpened Gate 2 condition:
-- NS cascade modes whose carrier projection is FRACTRAN-admissible and
-- terminating form a decidable carrier-side nonresonance class for the tail
-- dominance candidate.
--
-- Boundary:
-- The NS-to-EV5 projection and continuous Navier-Stokes flow transfer remain
-- open.  This receipt does not prove Navier-Stokes regularity and does not
-- promote a Clay theorem.  The latest boundary is fail-closed: conditional NS
-- regularity requires projection into FRACTRAN-admissible EV5 with forward
-- simulation, quotient correctness, Lyapunov preservation, and ultrametric
-- preservation.

data NSFractranTailAdmissibilityStatus : Set where
  carrierSideReceipt_only_missingNSProjectionAndFlowTransfer :
    NSFractranTailAdmissibilityStatus

data FractranCOLInput : Set where
  ev5ExponentVectorOverPrimeLanesTwoThreeFiveSevenEleven :
    FractranCOLInput

  rule1122 :
    FractranCOLInput

  rule53 :
    FractranCOLInput

  rule17 :
    FractranCOLInput

  energyEUsesPrimeLanesTwoThreeSeven :
    FractranCOLInput

canonicalFractranCOLInputs :
  List FractranCOLInput
canonicalFractranCOLInputs =
  ev5ExponentVectorOverPrimeLanesTwoThreeFiveSevenEleven
  ∷ rule1122
  ∷ rule53
  ∷ rule17
  ∷ energyEUsesPrimeLanesTwoThreeSeven
  ∷ []

data Gate2CarrierClass : Set where
  fractranAdmissibleTerminatingCarrierNonresonance :
    Gate2CarrierClass

data OpenTransferObligation : Set where
  defineNSToEV5CarrierProjection :
    OpenTransferObligation

  proveNSToEV5ForwardSimulation :
    OpenTransferObligation

  proveNSToEV5QuotientCorrectness :
    OpenTransferObligation

  proveNSToEV5LyapunovPreservation :
    OpenTransferObligation

  proveNSToEV5UltrametricPreservation :
    OpenTransferObligation

canonicalOpenTransferObligations :
  List OpenTransferObligation
canonicalOpenTransferObligations =
  defineNSToEV5CarrierProjection
  ∷ proveNSToEV5ForwardSimulation
  ∷ proveNSToEV5QuotientCorrectness
  ∷ proveNSToEV5LyapunovPreservation
  ∷ proveNSToEV5UltrametricPreservation
  ∷ []

data PromotionToken : Set where

promotionImpossibleHere :
  PromotionToken →
  ⊥
promotionImpossibleHere ()

fractranCOLModuleName :
  String
fractranCOLModuleName =
  "DASHI.Combinatorics.FractranCOL"

fractranCarrierPrimeSummary :
  String
fractranCarrierPrimeSummary =
  "FractranCOL provides EV5 over primes 2,3,5,7,11."

fractranRuleSummary :
  String
fractranRuleSummary =
  "FractranCOL exposes the deterministic first-applicable rules r1122, r53, and r17."

fractranEnergySummary :
  String
fractranEnergySummary =
  "FractranCOL energy E is the rank over active prime lanes 2,3,7."

sharpenedGate2ConditionStatement :
  String
sharpenedGate2ConditionStatement =
  "Gate 2 sharpened: NS cascade modes whose carrier projection is FRACTRAN-admissible/terminating are a decidable carrier-side nonresonance class for the tail dominance candidate."

openBoundaryStatement :
  String
openBoundaryStatement =
  "Fail-closed open boundary: conditional NS regularity requires NS modes to project into FRACTRAN-admissible EV5 with forward simulation. Exact open obligations are forward simulation, quotient correctness, Lyapunov preservation, and ultrametric preservation, so this receipt does not prove Navier-Stokes regularity."

record NSFractranTailAdmissibilityReceipt : Set₁ where
  field
    status :
      NSFractranTailAdmissibilityStatus

    statusIsCarrierSideOnly :
      status
      ≡
      carrierSideReceipt_only_missingNSProjectionAndFlowTransfer

    sourceModule :
      String

    sourceModuleIsFractranCOL :
      sourceModule ≡ fractranCOLModuleName

    evCarrier :
      Set

    evCarrierIsEV5 :
      evCarrier ≡ FractranCOL.EV5

    carrierPrimeLanes :
      List Nat

    carrierPrimeLanesAreCanonical :
      carrierPrimeLanes ≡ (2 ∷ 3 ∷ 5 ∷ 7 ∷ 11 ∷ [])

    fractranRules :
      List FractranCOL.Rule

    fractranRulesAreCanonical :
      fractranRules
      ≡
      (FractranCOL.r1122 ∷ FractranCOL.r53 ∷ FractranCOL.r17 ∷ [])

    energy :
      FractranCOL.EV5 → Nat

    energyIsFractranCOLE :
      energy ≡ FractranCOL.E

    energyPrimeLanes :
      List Nat

    energyPrimeLanesAreCanonical :
      energyPrimeLanes ≡ (2 ∷ 3 ∷ 7 ∷ [])

    fractranInputs :
      List FractranCOLInput

    fractranInputsAreCanonical :
      fractranInputs ≡ canonicalFractranCOLInputs

    gate2CarrierClass :
      Gate2CarrierClass

    gate2CarrierClassIsCanonical :
      gate2CarrierClass
      ≡
      fractranAdmissibleTerminatingCarrierNonresonance

    gate2CarrierClassDecidable :
      Bool

    gate2CarrierClassDecidableIsTrue :
      gate2CarrierClassDecidable ≡ true

    carrierProjectionFractranAdmissibleTerminating :
      Bool

    carrierProjectionFractranAdmissibleTerminatingIsTrue :
      carrierProjectionFractranAdmissibleTerminating ≡ true

    openTransferObligations :
      List OpenTransferObligation

    openTransferObligationsAreCanonical :
      openTransferObligations ≡ canonicalOpenTransferObligations

    failClosedBoundary :
      Bool

    failClosedBoundaryIsTrue :
      failClosedBoundary ≡ true

    conditionalNSRegularityRequiresForwardSimulation :
      Bool

    conditionalNSRegularityRequiresForwardSimulationIsTrue :
      conditionalNSRegularityRequiresForwardSimulation ≡ true

    nsToEV5ProjectionProvedHere :
      Bool

    nsToEV5ProjectionProvedHereIsFalse :
      nsToEV5ProjectionProvedHere ≡ false

    continuousNSFlowTransferProvedHere :
      Bool

    continuousNSFlowTransferProvedHereIsFalse :
      continuousNSFlowTransferProvedHere ≡ false

    quotientCorrectnessProvedHere :
      Bool

    quotientCorrectnessProvedHereIsFalse :
      quotientCorrectnessProvedHere ≡ false

    lyapunovPreservationProvedHere :
      Bool

    lyapunovPreservationProvedHereIsFalse :
      lyapunovPreservationProvedHere ≡ false

    ultrametricPreservationProvedHere :
      Bool

    ultrametricPreservationProvedHereIsFalse :
      ultrametricPreservationProvedHere ≡ false

    nsRegularityProvedHere :
      Bool

    nsRegularityProvedHereIsFalse :
      nsRegularityProvedHere ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotionFlags :
      List PromotionToken

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    carrierPrimeSummary :
      String

    carrierPrimeSummaryIsCanonical :
      carrierPrimeSummary ≡ fractranCarrierPrimeSummary

    ruleSummary :
      String

    ruleSummaryIsCanonical :
      ruleSummary ≡ fractranRuleSummary

    energySummary :
      String

    energySummaryIsCanonical :
      energySummary ≡ fractranEnergySummary

    gate2ConditionSummary :
      String

    gate2ConditionSummaryIsCanonical :
      gate2ConditionSummary ≡ sharpenedGate2ConditionStatement

    boundarySummary :
      String

    boundarySummaryIsCanonical :
      boundarySummary ≡ openBoundaryStatement

open NSFractranTailAdmissibilityReceipt public

canonicalNSFractranTailAdmissibilityReceipt :
  NSFractranTailAdmissibilityReceipt
canonicalNSFractranTailAdmissibilityReceipt =
  record
    { status =
        carrierSideReceipt_only_missingNSProjectionAndFlowTransfer
    ; statusIsCarrierSideOnly =
        refl
    ; sourceModule =
        fractranCOLModuleName
    ; sourceModuleIsFractranCOL =
        refl
    ; evCarrier =
        FractranCOL.EV5
    ; evCarrierIsEV5 =
        refl
    ; carrierPrimeLanes =
        2 ∷ 3 ∷ 5 ∷ 7 ∷ 11 ∷ []
    ; carrierPrimeLanesAreCanonical =
        refl
    ; fractranRules =
        FractranCOL.r1122 ∷ FractranCOL.r53 ∷ FractranCOL.r17 ∷ []
    ; fractranRulesAreCanonical =
        refl
    ; energy =
        FractranCOL.E
    ; energyIsFractranCOLE =
        refl
    ; energyPrimeLanes =
        2 ∷ 3 ∷ 7 ∷ []
    ; energyPrimeLanesAreCanonical =
        refl
    ; fractranInputs =
        canonicalFractranCOLInputs
    ; fractranInputsAreCanonical =
        refl
    ; gate2CarrierClass =
        fractranAdmissibleTerminatingCarrierNonresonance
    ; gate2CarrierClassIsCanonical =
        refl
    ; gate2CarrierClassDecidable =
        true
    ; gate2CarrierClassDecidableIsTrue =
        refl
    ; carrierProjectionFractranAdmissibleTerminating =
        true
    ; carrierProjectionFractranAdmissibleTerminatingIsTrue =
        refl
    ; openTransferObligations =
        canonicalOpenTransferObligations
    ; openTransferObligationsAreCanonical =
        refl
    ; failClosedBoundary =
        true
    ; failClosedBoundaryIsTrue =
        refl
    ; conditionalNSRegularityRequiresForwardSimulation =
        true
    ; conditionalNSRegularityRequiresForwardSimulationIsTrue =
        refl
    ; nsToEV5ProjectionProvedHere =
        false
    ; nsToEV5ProjectionProvedHereIsFalse =
        refl
    ; continuousNSFlowTransferProvedHere =
        false
    ; continuousNSFlowTransferProvedHereIsFalse =
        refl
    ; quotientCorrectnessProvedHere =
        false
    ; quotientCorrectnessProvedHereIsFalse =
        refl
    ; lyapunovPreservationProvedHere =
        false
    ; lyapunovPreservationProvedHereIsFalse =
        refl
    ; ultrametricPreservationProvedHere =
        false
    ; ultrametricPreservationProvedHereIsFalse =
        refl
    ; nsRegularityProvedHere =
        false
    ; nsRegularityProvedHereIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; carrierPrimeSummary =
        fractranCarrierPrimeSummary
    ; carrierPrimeSummaryIsCanonical =
        refl
    ; ruleSummary =
        fractranRuleSummary
    ; ruleSummaryIsCanonical =
        refl
    ; energySummary =
        fractranEnergySummary
    ; energySummaryIsCanonical =
        refl
    ; gate2ConditionSummary =
        sharpenedGate2ConditionStatement
    ; gate2ConditionSummaryIsCanonical =
        refl
    ; boundarySummary =
        openBoundaryStatement
    ; boundarySummaryIsCanonical =
        refl
    }

nsFractranTailAdmissibilityNoProjectionTransfer :
  nsToEV5ProjectionProvedHere canonicalNSFractranTailAdmissibilityReceipt
  ≡
  false
nsFractranTailAdmissibilityNoProjectionTransfer =
  refl

nsFractranTailAdmissibilityNoContinuousTransfer :
  continuousNSFlowTransferProvedHere canonicalNSFractranTailAdmissibilityReceipt
  ≡
  false
nsFractranTailAdmissibilityNoContinuousTransfer =
  refl

nsFractranTailAdmissibilityNoRegularityProof :
  nsRegularityProvedHere canonicalNSFractranTailAdmissibilityReceipt
  ≡
  false
nsFractranTailAdmissibilityNoRegularityProof =
  refl
