module DASHI.Physics.Closure.NSToEV5ProjectionFrontierReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Maybe.Base using (Maybe)

import DASHI.Combinatorics.FractranCOL as FractranCOL

------------------------------------------------------------------------
-- NS-to-EV5 projection frontier receipt.
--
-- FRACDASH bridge checklist:
-- source semantics: Navier-Stokes shell/tail modes in H^(11/8);
-- target semantics: FractranCOL.EV5 over prime lanes 2,3,5,7,11;
-- encode candidate: v2 stores dyadic shell depth j; v3 stores cascade
-- transfer ratio / inertial flux; v5 stores vorticity stretching / helicity
-- proxy; v7 stores enstrophy and is termination-critical; v11 stores
-- phase/polarisation metadata outside the canonical FractranCOL rules;
-- decode candidate: approximate cascade depth, inertial-transfer state,
-- vorticity/helicity proxy, enstrophy tail state, and external phase data;
-- proof obligations: forward simulation, quotient correctness, Lyapunov
-- preservation against K*(nu), and ultrametric preservation.
--
-- This file closes only the carrier-side EV5/FractranCOL shape.  The latest
-- Clay-adjacent boundary is conditional and fail-closed: DASHI may support an
-- NS regularity theorem only if NS modes project into FRACTRAN-admissible EV5
-- and the projection carries a forward simulation.  This receipt does not
-- prove that transfer theorem, does not prove Navier-Stokes regularity, and
-- does not promote any Clay target.

data NSToEV5ProjectionFrontierStatus : Set where
  failClosedConditionalBoundary_carrierShapeOnly :
    NSToEV5ProjectionFrontierStatus

data SourceSemantics : Set where
  navierStokesShellTailModesInH118 :
    SourceSemantics

data TargetSemantics : Set where
  fractranCOLEV5OverPrimeLanesTwoThreeFiveSevenEleven :
    TargetSemantics

data ProjectionEncodeItem : Set where
  v2DyadicShellDepthJ :
    ProjectionEncodeItem

  v3CascadeTransferRatioInertialFlux :
    ProjectionEncodeItem

  v5VorticityStretchingHelicityProxy :
    ProjectionEncodeItem

  v7EnstrophyTerminationCritical :
    ProjectionEncodeItem

  v11PhasePolarisationOutsideCanonicalRules :
    ProjectionEncodeItem

canonicalProjectionEncodeItems :
  List ProjectionEncodeItem
canonicalProjectionEncodeItems =
  v2DyadicShellDepthJ
  ∷ v3CascadeTransferRatioInertialFlux
  ∷ v5VorticityStretchingHelicityProxy
  ∷ v7EnstrophyTerminationCritical
  ∷ v11PhasePolarisationOutsideCanonicalRules
  ∷ []

data ProjectionDecodeItem : Set where
  approximateDepthJFromV2 :
    ProjectionDecodeItem

  approximateCascadeTransferInertialFluxFromV3 :
    ProjectionDecodeItem

  approximateVorticityStretchingHelicityProxyFromV5 :
    ProjectionDecodeItem

  approximateEnstrophyTailStateFromV7 :
    ProjectionDecodeItem

  externalPhasePolarisationDataFromV11 :
    ProjectionDecodeItem

canonicalProjectionDecodeItems :
  List ProjectionDecodeItem
canonicalProjectionDecodeItems =
  approximateDepthJFromV2
  ∷ approximateCascadeTransferInertialFluxFromV3
  ∷ approximateVorticityStretchingHelicityProxyFromV5
  ∷ approximateEnstrophyTailStateFromV7
  ∷ externalPhasePolarisationDataFromV11
  ∷ []

data ProjectionProofObligation : Set where
  forwardSimulationObligation :
    ProjectionProofObligation

  quotientCorrectnessObligation :
    ProjectionProofObligation

  lyapunovPreservationAgainstKStarNuObligation :
    ProjectionProofObligation

  ultrametricPreservationObligation :
    ProjectionProofObligation

canonicalProjectionProofObligations :
  List ProjectionProofObligation
canonicalProjectionProofObligations =
  forwardSimulationObligation
  ∷ quotientCorrectnessObligation
  ∷ lyapunovPreservationAgainstKStarNuObligation
  ∷ ultrametricPreservationObligation
  ∷ []

data LaneSemantics : Set where
  v2MeansDepthJ :
    LaneSemantics

  v3MeansCascadeTransferRatioInertialFlux :
    LaneSemantics

  v5MeansVorticityStretchingHelicityProxy :
    LaneSemantics

  v7MeansEnstrophyTerminationCritical :
    LaneSemantics

  v11MeansPhasePolarisationOutsideCanonicalRules :
    LaneSemantics

canonicalLaneSemantics :
  List LaneSemantics
canonicalLaneSemantics =
  v2MeansDepthJ
  ∷ v3MeansCascadeTransferRatioInertialFlux
  ∷ v5MeansVorticityStretchingHelicityProxy
  ∷ v7MeansEnstrophyTerminationCritical
  ∷ v11MeansPhasePolarisationOutsideCanonicalRules
  ∷ []

data TerminationEnergyComponent : Set where
  energyUsesV2DepthJ :
    TerminationEnergyComponent

  energyUsesV3CascadeTransferRatioInertialFlux :
    TerminationEnergyComponent

  energyUsesV7Enstrophy :
    TerminationEnergyComponent

canonicalTerminationEnergyComponents :
  List TerminationEnergyComponent
canonicalTerminationEnergyComponents =
  energyUsesV2DepthJ
  ∷ energyUsesV3CascadeTransferRatioInertialFlux
  ∷ energyUsesV7Enstrophy
  ∷ []

data CarrierShapeItem : Set where
  ev5Carrier :
    CarrierShapeItem

  primeLaneTwo :
    CarrierShapeItem

  primeLaneThree :
    CarrierShapeItem

  primeLaneFive :
    CarrierShapeItem

  primeLaneSeven :
    CarrierShapeItem

  primeLaneEleven :
    CarrierShapeItem

  deterministicFractranCOLStep :
    CarrierShapeItem

  fractranCOLEnergyRank :
    CarrierShapeItem

canonicalCarrierShapeItems :
  List CarrierShapeItem
canonicalCarrierShapeItems =
  ev5Carrier
  ∷ primeLaneTwo
  ∷ primeLaneThree
  ∷ primeLaneFive
  ∷ primeLaneSeven
  ∷ primeLaneEleven
  ∷ deterministicFractranCOLStep
  ∷ fractranCOLEnergyRank
  ∷ []

data ProjectionPromotionToken : Set where

projectionPromotionImpossibleHere :
  ProjectionPromotionToken →
  ⊥
projectionPromotionImpossibleHere ()

h118SobolevNumerator :
  Nat
h118SobolevNumerator =
  11

h118SobolevDenominator :
  Nat
h118SobolevDenominator =
  8

fractranCOLModuleName :
  String
fractranCOLModuleName =
  "DASHI.Combinatorics.FractranCOL"

sourceSemanticsStatement :
  String
sourceSemanticsStatement =
  "Source semantics: Navier-Stokes shell/tail modes in H^(11/8)."

targetSemanticsStatement :
  String
targetSemanticsStatement =
  "Target semantics: FractranCOL.EV5 over prime lanes 2,3,5,7,11."

encodeCandidateStatement :
  String
encodeCandidateStatement =
  "Encode candidate: v2 records dyadic depth j; v3 records cascade transfer ratio / inertial flux; v5 records vorticity stretching / helicity proxy; v7 records enstrophy and is termination-critical; v11 records phase/polarisation outside canonical FractranCOL rules."

decodeCandidateStatement :
  String
decodeCandidateStatement =
  "Decode candidate: recover approximate depth j, cascade transfer / inertial flux, vorticity stretching / helicity proxy, enstrophy tail state, and external phase/polarisation data from the projected EV5 carrier."

frontierBoundaryStatement :
  String
frontierBoundaryStatement =
  "Fail-closed conditional frontier: carrier-side EV5/FractranCOL shape and NS lane semantics are recorded; DASHI may support conditional NS regularity only if NS modes project into FRACTRAN-admissible EV5 with forward simulation. Open obligations are exactly forward simulation, quotient correctness, Lyapunov preservation against K*(nu), and ultrametric preservation. No unconditional NS theorem or Clay promotion is made."

terminationEnergyStatement :
  String
terminationEnergyStatement =
  "Termination energy is FractranCOL.E = v2 + v3 + v7; v5 and v11 are non-energy metadata for this receipt."

falsificationBoundaryStatement :
  String
falsificationBoundaryStatement =
  "Falsification boundary: the NS-to-EV5 projection fails if v2 cannot track depth j, v3 cannot track cascade transfer / inertial flux, v5 cannot track vorticity stretching / helicity proxy, v7 cannot track enstrophy descent, v11 cannot remain outside canonical rules, or E differs from v2+v3+v7."

record NSToEV5ProjectionFrontierReceipt : Set₁ where
  field
    status :
      NSToEV5ProjectionFrontierStatus

    statusIsCarrierShapeOnly :
      status ≡ failClosedConditionalBoundary_carrierShapeOnly

    sourceSemantics :
      SourceSemantics

    sourceSemanticsIsNSH118 :
      sourceSemantics ≡ navierStokesShellTailModesInH118

    h118Numerator :
      Nat

    h118NumeratorIs11 :
      h118Numerator ≡ h118SobolevNumerator

    h118Denominator :
      Nat

    h118DenominatorIs8 :
      h118Denominator ≡ h118SobolevDenominator

    targetSemantics :
      TargetSemantics

    targetSemanticsIsFractranCOLEV5 :
      targetSemantics
      ≡
      fractranCOLEV5OverPrimeLanesTwoThreeFiveSevenEleven

    targetModule :
      String

    targetModuleIsFractranCOL :
      targetModule ≡ fractranCOLModuleName

    evCarrier :
      Set

    evCarrierIsFractranCOLEV5 :
      evCarrier ≡ FractranCOL.EV5

    carrierPrimeLanes :
      List Nat

    carrierPrimeLanesAreCanonical :
      carrierPrimeLanes ≡ (2 ∷ 3 ∷ 5 ∷ 7 ∷ 11 ∷ [])

    carrierShapeItems :
      List CarrierShapeItem

    carrierShapeItemsAreCanonical :
      carrierShapeItems ≡ canonicalCarrierShapeItems

    laneSemantics :
      List LaneSemantics

    laneSemanticsAreCanonical :
      laneSemantics ≡ canonicalLaneSemantics

    fractranStep :
      FractranCOL.EV5 → Maybe FractranCOL.EV5

    fractranStepIsFractranCOLStep :
      fractranStep ≡ FractranCOL.step

    fractranEnergy :
      FractranCOL.EV5 → Nat

    fractranEnergyIsFractranCOLE :
      fractranEnergy ≡ FractranCOL.E

    terminationEnergyActivePrimeLanes :
      List Nat

    terminationEnergyActivePrimeLanesAreCanonical :
      terminationEnergyActivePrimeLanes ≡ (2 ∷ 3 ∷ 7 ∷ [])

    terminationEnergyComponents :
      List TerminationEnergyComponent

    terminationEnergyComponentsAreCanonical :
      terminationEnergyComponents ≡ canonicalTerminationEnergyComponents

    carrierSideEV5FractranCOLShapeClosed :
      Bool

    carrierSideEV5FractranCOLShapeClosedIsTrue :
      carrierSideEV5FractranCOLShapeClosed ≡ true

    failClosedConditionalBoundary :
      Bool

    failClosedConditionalBoundaryIsTrue :
      failClosedConditionalBoundary ≡ true

    conditionalNSRegularityRequiresFractranAdmissibleEV5 :
      Bool

    conditionalNSRegularityRequiresFractranAdmissibleEV5IsTrue :
      conditionalNSRegularityRequiresFractranAdmissibleEV5 ≡ true

    encodeItems :
      List ProjectionEncodeItem

    encodeItemsAreCanonical :
      encodeItems ≡ canonicalProjectionEncodeItems

    decodeItems :
      List ProjectionDecodeItem

    decodeItemsAreCanonical :
      decodeItems ≡ canonicalProjectionDecodeItems

    proofObligations :
      List ProjectionProofObligation

    proofObligationsAreCanonical :
      proofObligations ≡ canonicalProjectionProofObligations

    forwardSimulationProvedHere :
      Bool

    forwardSimulationProvedHereIsFalse :
      forwardSimulationProvedHere ≡ false

    nsModesProjectIntoFractranAdmissibleEV5ProvedHere :
      Bool

    nsModesProjectIntoFractranAdmissibleEV5ProvedHereIsFalse :
      nsModesProjectIntoFractranAdmissibleEV5ProvedHere ≡ false

    quotientCorrectnessProvedHere :
      Bool

    quotientCorrectnessProvedHereIsFalse :
      quotientCorrectnessProvedHere ≡ false

    lyapunovPreservationAgainstKStarNuProvedHere :
      Bool

    lyapunovPreservationAgainstKStarNuProvedHereIsFalse :
      lyapunovPreservationAgainstKStarNuProvedHere ≡ false

    ultrametricPreservationProvedHere :
      Bool

    ultrametricPreservationProvedHereIsFalse :
      ultrametricPreservationProvedHere ≡ false

    nsProjectionTheoremProvedHere :
      Bool

    nsProjectionTheoremProvedHereIsFalse :
      nsProjectionTheoremProvedHere ≡ false

    unconditionalNSRegularityClaimedHere :
      Bool

    unconditionalNSRegularityClaimedHereIsFalse :
      unconditionalNSRegularityClaimedHere ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotionFlags :
      List ProjectionPromotionToken

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    sourceSemanticsSummary :
      String

    sourceSemanticsSummaryIsCanonical :
      sourceSemanticsSummary ≡ sourceSemanticsStatement

    targetSemanticsSummary :
      String

    targetSemanticsSummaryIsCanonical :
      targetSemanticsSummary ≡ targetSemanticsStatement

    encodeCandidateSummary :
      String

    encodeCandidateSummaryIsCanonical :
      encodeCandidateSummary ≡ encodeCandidateStatement

    decodeCandidateSummary :
      String

    decodeCandidateSummaryIsCanonical :
      decodeCandidateSummary ≡ decodeCandidateStatement

    frontierBoundary :
      String

    frontierBoundaryIsCanonical :
      frontierBoundary ≡ frontierBoundaryStatement

    terminationEnergySummary :
      String

    terminationEnergySummaryIsCanonical :
      terminationEnergySummary ≡ terminationEnergyStatement

    falsificationBoundary :
      String

    falsificationBoundaryIsCanonical :
      falsificationBoundary ≡ falsificationBoundaryStatement

open NSToEV5ProjectionFrontierReceipt public

canonicalNSToEV5ProjectionFrontierReceipt :
  NSToEV5ProjectionFrontierReceipt
canonicalNSToEV5ProjectionFrontierReceipt =
  record
    { status =
        failClosedConditionalBoundary_carrierShapeOnly
    ; statusIsCarrierShapeOnly =
        refl
    ; sourceSemantics =
        navierStokesShellTailModesInH118
    ; sourceSemanticsIsNSH118 =
        refl
    ; h118Numerator =
        11
    ; h118NumeratorIs11 =
        refl
    ; h118Denominator =
        8
    ; h118DenominatorIs8 =
        refl
    ; targetSemantics =
        fractranCOLEV5OverPrimeLanesTwoThreeFiveSevenEleven
    ; targetSemanticsIsFractranCOLEV5 =
        refl
    ; targetModule =
        fractranCOLModuleName
    ; targetModuleIsFractranCOL =
        refl
    ; evCarrier =
        FractranCOL.EV5
    ; evCarrierIsFractranCOLEV5 =
        refl
    ; carrierPrimeLanes =
        2 ∷ 3 ∷ 5 ∷ 7 ∷ 11 ∷ []
    ; carrierPrimeLanesAreCanonical =
        refl
    ; carrierShapeItems =
        canonicalCarrierShapeItems
    ; carrierShapeItemsAreCanonical =
        refl
    ; laneSemantics =
        canonicalLaneSemantics
    ; laneSemanticsAreCanonical =
        refl
    ; fractranStep =
        FractranCOL.step
    ; fractranStepIsFractranCOLStep =
        refl
    ; fractranEnergy =
        FractranCOL.E
    ; fractranEnergyIsFractranCOLE =
        refl
    ; terminationEnergyActivePrimeLanes =
        2 ∷ 3 ∷ 7 ∷ []
    ; terminationEnergyActivePrimeLanesAreCanonical =
        refl
    ; terminationEnergyComponents =
        canonicalTerminationEnergyComponents
    ; terminationEnergyComponentsAreCanonical =
        refl
    ; carrierSideEV5FractranCOLShapeClosed =
        true
    ; carrierSideEV5FractranCOLShapeClosedIsTrue =
        refl
    ; failClosedConditionalBoundary =
        true
    ; failClosedConditionalBoundaryIsTrue =
        refl
    ; conditionalNSRegularityRequiresFractranAdmissibleEV5 =
        true
    ; conditionalNSRegularityRequiresFractranAdmissibleEV5IsTrue =
        refl
    ; encodeItems =
        canonicalProjectionEncodeItems
    ; encodeItemsAreCanonical =
        refl
    ; decodeItems =
        canonicalProjectionDecodeItems
    ; decodeItemsAreCanonical =
        refl
    ; proofObligations =
        canonicalProjectionProofObligations
    ; proofObligationsAreCanonical =
        refl
    ; forwardSimulationProvedHere =
        false
    ; forwardSimulationProvedHereIsFalse =
        refl
    ; nsModesProjectIntoFractranAdmissibleEV5ProvedHere =
        false
    ; nsModesProjectIntoFractranAdmissibleEV5ProvedHereIsFalse =
        refl
    ; quotientCorrectnessProvedHere =
        false
    ; quotientCorrectnessProvedHereIsFalse =
        refl
    ; lyapunovPreservationAgainstKStarNuProvedHere =
        false
    ; lyapunovPreservationAgainstKStarNuProvedHereIsFalse =
        refl
    ; ultrametricPreservationProvedHere =
        false
    ; ultrametricPreservationProvedHereIsFalse =
        refl
    ; nsProjectionTheoremProvedHere =
        false
    ; nsProjectionTheoremProvedHereIsFalse =
        refl
    ; unconditionalNSRegularityClaimedHere =
        false
    ; unconditionalNSRegularityClaimedHereIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; sourceSemanticsSummary =
        sourceSemanticsStatement
    ; sourceSemanticsSummaryIsCanonical =
        refl
    ; targetSemanticsSummary =
        targetSemanticsStatement
    ; targetSemanticsSummaryIsCanonical =
        refl
    ; encodeCandidateSummary =
        encodeCandidateStatement
    ; encodeCandidateSummaryIsCanonical =
        refl
    ; decodeCandidateSummary =
        decodeCandidateStatement
    ; decodeCandidateSummaryIsCanonical =
        refl
    ; frontierBoundary =
        frontierBoundaryStatement
    ; frontierBoundaryIsCanonical =
        refl
    ; terminationEnergySummary =
        terminationEnergyStatement
    ; terminationEnergySummaryIsCanonical =
        refl
    ; falsificationBoundary =
        falsificationBoundaryStatement
    ; falsificationBoundaryIsCanonical =
        refl
    }

nsToEV5CarrierShapeClosedOnly :
  carrierSideEV5FractranCOLShapeClosed
    canonicalNSToEV5ProjectionFrontierReceipt
  ≡
  true
nsToEV5CarrierShapeClosedOnly =
  refl

nsToEV5ForwardSimulationRemainsOpen :
  forwardSimulationProvedHere canonicalNSToEV5ProjectionFrontierReceipt
  ≡
  false
nsToEV5ForwardSimulationRemainsOpen =
  refl

nsToEV5QuotientCorrectnessRemainsOpen :
  quotientCorrectnessProvedHere canonicalNSToEV5ProjectionFrontierReceipt
  ≡
  false
nsToEV5QuotientCorrectnessRemainsOpen =
  refl

nsToEV5TerminationEnergyUsesV2V3V7 :
  terminationEnergyActivePrimeLanes canonicalNSToEV5ProjectionFrontierReceipt
  ≡
  (2 ∷ 3 ∷ 7 ∷ [])
nsToEV5TerminationEnergyUsesV2V3V7 =
  refl

nsToEV5LyapunovPreservationRemainsOpen :
  lyapunovPreservationAgainstKStarNuProvedHere
    canonicalNSToEV5ProjectionFrontierReceipt
  ≡
  false
nsToEV5LyapunovPreservationRemainsOpen =
  refl

nsToEV5UltrametricPreservationRemainsOpen :
  ultrametricPreservationProvedHere
    canonicalNSToEV5ProjectionFrontierReceipt
  ≡
  false
nsToEV5UltrametricPreservationRemainsOpen =
  refl

nsToEV5NoNSTheoremOrClayPromotion :
  clayNavierStokesPromoted canonicalNSToEV5ProjectionFrontierReceipt
  ≡
  false
nsToEV5NoNSTheoremOrClayPromotion =
  refl
