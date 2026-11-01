module DASHI.Physics.Closure.UnifiedMarginInvariantReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.DistributedTensionFieldReceipt as Tension
import DASHI.Physics.Closure.FriendshipCarryAbsorptionReceipt as CarryAbsorption
import DASHI.Physics.Closure.NSYMParallelStructureReceipt as NSYM
import DASHI.Physics.Closure.PressureDepthCorrectionReceipt as PressureDepth

------------------------------------------------------------------------
-- Unified margin invariant receipt.
--
-- This receipt records one governance/seam-gauge analogy:
--
-- * NS theta is a seam gauge, not a proof;
-- * YM rho is a seam gauge, not a proof;
-- * dialectical carry absorbed into depth/history;
-- * braid/tension kept bounded in the negotiated middle.
--
-- The shared claim is that margin variables make failure local, typed,
-- measurable, and receipt-addressable.  It is not an analytic theorem and
-- it does not supply the analytic inhabitants for NS, YM, Gate 3, or Clay
-- promotion.

data UnifiedMarginInvariantStatus : Set where
  unifiedMarginInvariantRecorded_analogyGovernanceOnly :
    UnifiedMarginInvariantStatus

data MarginAxis : Set where
  navierStokesThetaSeamGauge :
    MarginAxis

  yangMillsRhoSeamGauge :
    MarginAxis

  dialecticalCarryAbsorbedIntoDepth :
    MarginAxis

  braidTensionBoundedInNegotiatedMiddle :
    MarginAxis

canonicalMarginAxes :
  List MarginAxis
canonicalMarginAxes =
  navierStokesThetaSeamGauge
  ∷ yangMillsRhoSeamGauge
  ∷ dialecticalCarryAbsorbedIntoDepth
  ∷ braidTensionBoundedInNegotiatedMiddle
  ∷ []

data SeamGaugeReading : Set where
  thetaIsSeamGaugeNotProof :
    SeamGaugeReading

  rhoIsSeamGaugeNotProof :
    SeamGaugeReading

canonicalSeamGaugeReadings :
  List SeamGaugeReading
canonicalSeamGaugeReadings =
  thetaIsSeamGaugeNotProof
  ∷ rhoIsSeamGaugeNotProof
  ∷ []

data MarginVariableEffect : Set where
  marginRecordedAsAbsorberMinusPromotedActivity :
    MarginVariableEffect

  failureMadeLocal :
    MarginVariableEffect

  failureMadeTyped :
    MarginVariableEffect

  failureMadeMeasurable :
    MarginVariableEffect

  failureMadeReceiptAddressable :
    MarginVariableEffect

canonicalMarginVariableEffects :
  List MarginVariableEffect
canonicalMarginVariableEffects =
  marginRecordedAsAbsorberMinusPromotedActivity
  ∷ failureMadeLocal
  ∷ failureMadeTyped
  ∷ failureMadeMeasurable
  ∷ failureMadeReceiptAddressable
  ∷ []

data UnifiedMarginFormula : Set where
  signedMarginEqualsAbsorberStrengthMinusPromotedActivity :
    UnifiedMarginFormula

data UnifiedMarginRatioFormula : Set where
  marginRatioEqualsOneMinusSeamGauge :
    UnifiedMarginRatioFormula

data L0MarginGrammarItem : Set where
  l0_1DynamicsBound :
    L0MarginGrammarItem

  l0_2SignedMarginEquivalentToRatio :
    L0MarginGrammarItem

canonicalL0MarginGrammarItems :
  List L0MarginGrammarItem
canonicalL0MarginGrammarItems =
  l0_1DynamicsBound
  ∷ l0_2SignedMarginEquivalentToRatio
  ∷ []

data FailClosedMarginSemantics : Set where
  marginPass :
    FailClosedMarginSemantics

  marginBoundary :
    FailClosedMarginSemantics

  marginFail :
    FailClosedMarginSemantics

  marginMissing :
    FailClosedMarginSemantics

canonicalFailClosedMarginSemantics :
  List FailClosedMarginSemantics
canonicalFailClosedMarginSemantics =
  marginPass
  ∷ marginBoundary
  ∷ marginFail
  ∷ marginMissing
  ∷ []

data NSMarginSide : Set where
  thetaLessThanOneSufficientProxyContinuationRoute :
    NSMarginSide

  bkmEquivalenceRemainsOpen :
    NSMarginSide

canonicalNSMarginSide :
  List NSMarginSide
canonicalNSMarginSide =
  thetaLessThanOneSufficientProxyContinuationRoute
  ∷ bkmEquivalenceRemainsOpen
  ∷ []

data YMMarginSide : Set where
  rhoLessThanOneConditionalKPMargin :
    YMMarginSide

  rgPromotionRemainsOpen :
    YMMarginSide

  gate3RemainsOpen :
    YMMarginSide

canonicalYMMarginSide :
  List YMMarginSide
canonicalYMMarginSide =
  rhoLessThanOneConditionalKPMargin
  ∷ rgPromotionRemainsOpen
  ∷ gate3RemainsOpen
  ∷ []

data SharedProofShapeStep : Set where
  chooseResidualFunctional :
    SharedProofShapeStep

  defineSignedAbsorptionMargin :
    SharedProofShapeStep

  recordSeamGaugeBelowThreshold :
    SharedProofShapeStep

  absorbOrBoundCarryTension :
    SharedProofShapeStep

  keepPromotionSeparateFromAnalogy :
    SharedProofShapeStep

canonicalSharedProofShape :
  List SharedProofShapeStep
canonicalSharedProofShape =
  chooseResidualFunctional
  ∷ defineSignedAbsorptionMargin
  ∷ recordSeamGaugeBelowThreshold
  ∷ absorbOrBoundCarryTension
  ∷ keepPromotionSeparateFromAnalogy
  ∷ []

data AnalyticInhabitantObligation : Set where
  inhabitNSThetaLessThanOneEstimate :
    AnalyticInhabitantObligation

  inhabitYMRhoLessThanOneEstimate :
    AnalyticInhabitantObligation

  inhabitDialecticalCarryAbsorptionTheoremIfPromoted :
    AnalyticInhabitantObligation

  inhabitConcreteBraidTensionBound :
    AnalyticInhabitantObligation

  inhabitGate3TransferSeparately :
    AnalyticInhabitantObligation

canonicalAnalyticInhabitantObligations :
  List AnalyticInhabitantObligation
canonicalAnalyticInhabitantObligations =
  inhabitNSThetaLessThanOneEstimate
  ∷ inhabitYMRhoLessThanOneEstimate
  ∷ inhabitDialecticalCarryAbsorptionTheoremIfPromoted
  ∷ inhabitConcreteBraidTensionBound
  ∷ inhabitGate3TransferSeparately
  ∷ []

data UnifiedMarginBoundary : Set where
  analogyProofShapeGovernanceOnly :
    UnifiedMarginBoundary

  noAnalyticInhabitantsProved :
    UnifiedMarginBoundary

  noPhysicsTheorem :
    UnifiedMarginBoundary

  noGate3Theorem :
    UnifiedMarginBoundary

  noClayPromotion :
    UnifiedMarginBoundary

  noTerminalPromotion :
    UnifiedMarginBoundary

canonicalUnifiedMarginBoundaries :
  List UnifiedMarginBoundary
canonicalUnifiedMarginBoundaries =
  analogyProofShapeGovernanceOnly
  ∷ noAnalyticInhabitantsProved
  ∷ noPhysicsTheorem
  ∷ noGate3Theorem
  ∷ noClayPromotion
  ∷ noTerminalPromotion
  ∷ []

data UnifiedMarginPromotion : Set where

unifiedMarginPromotionImpossibleHere :
  UnifiedMarginPromotion →
  ⊥
unifiedMarginPromotionImpossibleHere ()

nsThetaStatement :
  String
nsThetaStatement =
  "NS slot: theta is a seam gauge, not a proof; theta < 1 is a sufficient-proxy / continuation-route marker while BKM equivalence remains open."

ymRhoStatement :
  String
ymRhoStatement =
  "YM slot: rho is a seam gauge, not a proof; rho < 1 is a conditional KP margin while RG promotion and Gate3 remain open."

dialecticalCarryStatement :
  String
dialecticalCarryStatement =
  "Dialectical slot: absorbed carry means pressure is converted to depth/history as bookkeeping, not as an analytic theorem."

braidTensionStatement :
  String
braidTensionStatement =
  "Braid/tension slot: bounded tension means the distributed constraint field remains in the negotiated middle."

unifiedMarginStatement :
  String
unifiedMarginStatement =
  "Unified margin invariant: signed margin = absorber_strength - promoted_activity, margin ratio = 1 - seam gauge, and theta/rho are seam gauges, not proofs; margin variables make failure local, typed, measurable, and receipt-addressable while analogy/dialectic carry stays bounded without analytic inhabitants."

signedMarginFormulaStatement :
  String
signedMarginFormulaStatement =
  "signed margin = absorber_strength - promoted_activity"

marginRatioFormulaStatement :
  String
marginRatioFormulaStatement =
  "margin ratio = 1 - seam gauge"

l0_1DynamicsBoundStatement :
  String
l0_1DynamicsBoundStatement =
  "L0.1 DynamicsBound: record a bounded-dynamics margin grammar surface only; no analytic dynamics theorem is promoted."

l0_2SignedMarginEquivalentToRatioStatement :
  String
l0_2SignedMarginEquivalentToRatioStatement =
  "L0.2 SignedMarginEquivalentToRatio: signed margin and margin ratio are equivalent bookkeeping readings of the same absorber/activity margin, not a physics theorem."

failClosedMarginSemanticsStatement :
  String
failClosedMarginSemanticsStatement =
  "fail-closed margin semantics: pass means positive discharged margin, boundary means typed threshold contact, fail means negative signed margin, and missing means absent absorber/activity evidence."

record UnifiedMarginInvariantReceipt : Setω where
  field
    status :
      UnifiedMarginInvariantStatus

    statusIsAnalogyGovernanceOnly :
      status ≡ unifiedMarginInvariantRecorded_analogyGovernanceOnly

    nsymParallelReceipt :
      NSYM.NSYMParallelStructureReceipt

    nsymNSClayPromotionFalse :
      NSYM.clayNavierStokesPromoted nsymParallelReceipt ≡ false

    nsymYMClayPromotionFalse :
      NSYM.clayYangMillsPromoted nsymParallelReceipt ≡ false

    nsymTerminalClayPromotionFalse :
      NSYM.terminalClayClaimPromoted nsymParallelReceipt ≡ false

    pressureDepthReceipt :
      PressureDepth.PressureDepthCorrectionReceipt

    pressureDepthKeepsNSFalse :
      PressureDepth.navierStokesTheoremPromoted pressureDepthReceipt ≡ false

    pressureDepthKeepsClayFalse :
      PressureDepth.clayPromotionMade pressureDepthReceipt ≡ false

    carryAbsorptionReceipt :
      CarryAbsorption.FriendshipCarryAbsorptionReceipt

    carryAbsorptionRecorded :
      CarryAbsorption.includedOtherConvertsPressureToDepthHistory
        carryAbsorptionReceipt
      ≡
      true

    carryAbsorptionTheoremFalse :
      CarryAbsorption.pressureAbsorptionTheoremProved
        carryAbsorptionReceipt
      ≡
      false

    carryAbsorptionPhysicsFalse :
      CarryAbsorption.physicsTheoremClaimed carryAbsorptionReceipt ≡ false

    carryAbsorptionClayFalse :
      CarryAbsorption.clayPromotionClaimed carryAbsorptionReceipt ≡ false

    tensionReceipt :
      Tension.DistributedTensionFieldReceipt

    tensionIsDistributed :
      Tension.DistributedTensionFieldReceipt.tensionFieldKind tensionReceipt
      ≡
      Tension.distributedConstraintField

    tensionMiddleBoundRecorded :
      Tension.DistributedTensionFieldReceipt.middleTransport tensionReceipt
      ≡
      Tension.braidTransportMaintainsMiddleTension

    tensionPhysicsFalse :
      Tension.DistributedTensionFieldReceipt.physicsTheoremPromoted
        tensionReceipt
      ≡
      false

    tensionClayFalse :
      Tension.DistributedTensionFieldReceipt.clayTheoremPromoted
        tensionReceipt
      ≡
      false

    marginAxes :
      List MarginAxis

    marginAxesAreCanonical :
      marginAxes ≡ canonicalMarginAxes

    sharedProofShape :
      List SharedProofShapeStep

    sharedProofShapeIsCanonical :
      sharedProofShape ≡ canonicalSharedProofShape

    seamGaugeReadings :
      List SeamGaugeReading

    seamGaugeReadingsAreCanonical :
      seamGaugeReadings ≡ canonicalSeamGaugeReadings

    marginVariableEffects :
      List MarginVariableEffect

    marginVariableEffectsAreCanonical :
      marginVariableEffects ≡ canonicalMarginVariableEffects

    signedMarginFormula :
      UnifiedMarginFormula

    signedMarginFormulaIsCanonical :
      signedMarginFormula
      ≡
      signedMarginEqualsAbsorberStrengthMinusPromotedActivity

    marginRatioFormula :
      UnifiedMarginRatioFormula

    marginRatioFormulaIsCanonical :
      marginRatioFormula ≡ marginRatioEqualsOneMinusSeamGauge

    l0MarginGrammar :
      List L0MarginGrammarItem

    l0MarginGrammarIsCanonical :
      l0MarginGrammar ≡ canonicalL0MarginGrammarItems

    l0_1DynamicsBoundRecorded :
      Bool

    l0_1DynamicsBoundRecordedIsTrue :
      l0_1DynamicsBoundRecorded ≡ true

    l0_1DynamicsBoundPromotedToTheorem :
      Bool

    l0_1DynamicsBoundPromotedToTheoremIsFalse :
      l0_1DynamicsBoundPromotedToTheorem ≡ false

    l0_2SignedMarginEquivalentToRatioRecorded :
      Bool

    l0_2SignedMarginEquivalentToRatioRecordedIsTrue :
      l0_2SignedMarginEquivalentToRatioRecorded ≡ true

    l0_2SignedMarginEquivalentToRatioPromotedToTheorem :
      Bool

    l0_2SignedMarginEquivalentToRatioPromotedToTheoremIsFalse :
      l0_2SignedMarginEquivalentToRatioPromotedToTheorem ≡ false

    failClosedMarginSemantics :
      List FailClosedMarginSemantics

    failClosedMarginSemanticsAreCanonical :
      failClosedMarginSemantics ≡ canonicalFailClosedMarginSemantics

    nsMarginSide :
      List NSMarginSide

    nsMarginSideIsCanonical :
      nsMarginSide ≡ canonicalNSMarginSide

    ymMarginSide :
      List YMMarginSide

    ymMarginSideIsCanonical :
      ymMarginSide ≡ canonicalYMMarginSide

    nsThetaLessThanOneRecorded :
      Bool

    nsThetaLessThanOneRecordedIsTrue :
      nsThetaLessThanOneRecorded ≡ true

    nsThetaIsSeamGaugeNotProof :
      Bool

    nsThetaIsSeamGaugeNotProofIsTrue :
      nsThetaIsSeamGaugeNotProof ≡ true

    nsThetaSufficientProxyContinuationRoute :
      Bool

    nsThetaSufficientProxyContinuationRouteIsTrue :
      nsThetaSufficientProxyContinuationRoute ≡ true

    nsBKMEquivalenceProved :
      Bool

    nsBKMEquivalenceProvedIsFalse :
      nsBKMEquivalenceProved ≡ false

    nsThetaAnalyticInhabitantProved :
      Bool

    nsThetaAnalyticInhabitantProvedIsFalse :
      nsThetaAnalyticInhabitantProved ≡ false

    ymRhoLessThanOneRecorded :
      Bool

    ymRhoLessThanOneRecordedIsTrue :
      ymRhoLessThanOneRecorded ≡ true

    ymRhoIsSeamGaugeNotProof :
      Bool

    ymRhoIsSeamGaugeNotProofIsTrue :
      ymRhoIsSeamGaugeNotProof ≡ true

    ymRhoConditionalKPMargin :
      Bool

    ymRhoConditionalKPMarginIsTrue :
      ymRhoConditionalKPMargin ≡ true

    ymRGPromotionClosed :
      Bool

    ymRGPromotionClosedIsFalse :
      ymRGPromotionClosed ≡ false

    ymGate3Closed :
      Bool

    ymGate3ClosedIsFalse :
      ymGate3Closed ≡ false

    ymRhoAnalyticInhabitantProved :
      Bool

    ymRhoAnalyticInhabitantProvedIsFalse :
      ymRhoAnalyticInhabitantProved ≡ false

    dialecticalCarryAbsorbedRecorded :
      Bool

    dialecticalCarryAbsorbedRecordedIsTrue :
      dialecticalCarryAbsorbedRecorded ≡ true

    braidTensionBoundedRecorded :
      Bool

    braidTensionBoundedRecordedIsTrue :
      braidTensionBoundedRecorded ≡ true

    sameProofShapeClaimed :
      Bool

    sameProofShapeClaimedIsTrue :
      sameProofShapeClaimed ≡ true

    proofShapeIsAnalogyGovernance :
      Bool

    proofShapeIsAnalogyGovernanceIsTrue :
      proofShapeIsAnalogyGovernance ≡ true

    analogyDialecticCarryBounded :
      Bool

    analogyDialecticCarryBoundedIsTrue :
      analogyDialecticCarryBounded ≡ true

    analyticInhabitantsProved :
      Bool

    analyticInhabitantsProvedIsFalse :
      analyticInhabitantsProved ≡ false

    physicsTheoremPromoted :
      Bool

    physicsTheoremPromotedIsFalse :
      physicsTheoremPromoted ≡ false

    gate3TheoremPromoted :
      Bool

    gate3TheoremPromotedIsFalse :
      gate3TheoremPromoted ≡ false

    clayPromotionMade :
      Bool

    clayPromotionMadeIsFalse :
      clayPromotionMade ≡ false

    terminalPromotionMade :
      Bool

    terminalPromotionMadeIsFalse :
      terminalPromotionMade ≡ false

    analyticInhabitantObligations :
      List AnalyticInhabitantObligation

    analyticInhabitantObligationsAreCanonical :
      analyticInhabitantObligations
      ≡
      canonicalAnalyticInhabitantObligations

    boundaries :
      List UnifiedMarginBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalUnifiedMarginBoundaries

    promotionFlags :
      List UnifiedMarginPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    noPromotion :
      UnifiedMarginPromotion →
      ⊥

    signedMarginFormulaReading :
      String

    signedMarginFormulaReadingIsCanonical :
      signedMarginFormulaReading ≡ signedMarginFormulaStatement

    marginRatioFormulaReading :
      String

    marginRatioFormulaReadingIsCanonical :
      marginRatioFormulaReading ≡ marginRatioFormulaStatement

    l0_1DynamicsBoundReading :
      String

    l0_1DynamicsBoundReadingIsCanonical :
      l0_1DynamicsBoundReading ≡ l0_1DynamicsBoundStatement

    l0_2SignedMarginEquivalentToRatioReading :
      String

    l0_2SignedMarginEquivalentToRatioReadingIsCanonical :
      l0_2SignedMarginEquivalentToRatioReading
      ≡
      l0_2SignedMarginEquivalentToRatioStatement

    failClosedMarginSemanticsReading :
      String

    failClosedMarginSemanticsReadingIsCanonical :
      failClosedMarginSemanticsReading
      ≡
      failClosedMarginSemanticsStatement

    nsThetaReading :
      String

    nsThetaReadingIsCanonical :
      nsThetaReading ≡ nsThetaStatement

    ymRhoReading :
      String

    ymRhoReadingIsCanonical :
      ymRhoReading ≡ ymRhoStatement

    dialecticalCarryReading :
      String

    dialecticalCarryReadingIsCanonical :
      dialecticalCarryReading ≡ dialecticalCarryStatement

    braidTensionReading :
      String

    braidTensionReadingIsCanonical :
      braidTensionReading ≡ braidTensionStatement

    unifiedStatement :
      String

    unifiedStatementIsCanonical :
      unifiedStatement ≡ unifiedMarginStatement

    receiptBoundary :
      List String

open UnifiedMarginInvariantReceipt public

canonicalUnifiedMarginInvariantReceipt :
  UnifiedMarginInvariantReceipt
canonicalUnifiedMarginInvariantReceipt =
  record
    { status =
        unifiedMarginInvariantRecorded_analogyGovernanceOnly
    ; statusIsAnalogyGovernanceOnly =
        refl
    ; nsymParallelReceipt =
        NSYM.canonicalNSYMParallelStructureReceipt
    ; nsymNSClayPromotionFalse =
        refl
    ; nsymYMClayPromotionFalse =
        refl
    ; nsymTerminalClayPromotionFalse =
        refl
    ; pressureDepthReceipt =
        PressureDepth.canonicalPressureDepthCorrectionReceipt
    ; pressureDepthKeepsNSFalse =
        refl
    ; pressureDepthKeepsClayFalse =
        refl
    ; carryAbsorptionReceipt =
        CarryAbsorption.canonicalFriendshipCarryAbsorptionReceipt
    ; carryAbsorptionRecorded =
        refl
    ; carryAbsorptionTheoremFalse =
        refl
    ; carryAbsorptionPhysicsFalse =
        refl
    ; carryAbsorptionClayFalse =
        refl
    ; tensionReceipt =
        Tension.canonicalDistributedTensionFieldReceipt
    ; tensionIsDistributed =
        refl
    ; tensionMiddleBoundRecorded =
        refl
    ; tensionPhysicsFalse =
        refl
    ; tensionClayFalse =
        refl
    ; marginAxes =
        canonicalMarginAxes
    ; marginAxesAreCanonical =
        refl
    ; sharedProofShape =
        canonicalSharedProofShape
    ; sharedProofShapeIsCanonical =
        refl
    ; seamGaugeReadings =
        canonicalSeamGaugeReadings
    ; seamGaugeReadingsAreCanonical =
        refl
    ; marginVariableEffects =
        canonicalMarginVariableEffects
    ; marginVariableEffectsAreCanonical =
        refl
    ; signedMarginFormula =
        signedMarginEqualsAbsorberStrengthMinusPromotedActivity
    ; signedMarginFormulaIsCanonical =
        refl
    ; marginRatioFormula =
        marginRatioEqualsOneMinusSeamGauge
    ; marginRatioFormulaIsCanonical =
        refl
    ; l0MarginGrammar =
        canonicalL0MarginGrammarItems
    ; l0MarginGrammarIsCanonical =
        refl
    ; l0_1DynamicsBoundRecorded =
        true
    ; l0_1DynamicsBoundRecordedIsTrue =
        refl
    ; l0_1DynamicsBoundPromotedToTheorem =
        false
    ; l0_1DynamicsBoundPromotedToTheoremIsFalse =
        refl
    ; l0_2SignedMarginEquivalentToRatioRecorded =
        true
    ; l0_2SignedMarginEquivalentToRatioRecordedIsTrue =
        refl
    ; l0_2SignedMarginEquivalentToRatioPromotedToTheorem =
        false
    ; l0_2SignedMarginEquivalentToRatioPromotedToTheoremIsFalse =
        refl
    ; failClosedMarginSemantics =
        canonicalFailClosedMarginSemantics
    ; failClosedMarginSemanticsAreCanonical =
        refl
    ; nsMarginSide =
        canonicalNSMarginSide
    ; nsMarginSideIsCanonical =
        refl
    ; ymMarginSide =
        canonicalYMMarginSide
    ; ymMarginSideIsCanonical =
        refl
    ; nsThetaLessThanOneRecorded =
        true
    ; nsThetaLessThanOneRecordedIsTrue =
        refl
    ; nsThetaIsSeamGaugeNotProof =
        true
    ; nsThetaIsSeamGaugeNotProofIsTrue =
        refl
    ; nsThetaSufficientProxyContinuationRoute =
        true
    ; nsThetaSufficientProxyContinuationRouteIsTrue =
        refl
    ; nsBKMEquivalenceProved =
        false
    ; nsBKMEquivalenceProvedIsFalse =
        refl
    ; nsThetaAnalyticInhabitantProved =
        false
    ; nsThetaAnalyticInhabitantProvedIsFalse =
        refl
    ; ymRhoLessThanOneRecorded =
        true
    ; ymRhoLessThanOneRecordedIsTrue =
        refl
    ; ymRhoIsSeamGaugeNotProof =
        true
    ; ymRhoIsSeamGaugeNotProofIsTrue =
        refl
    ; ymRhoConditionalKPMargin =
        true
    ; ymRhoConditionalKPMarginIsTrue =
        refl
    ; ymRGPromotionClosed =
        false
    ; ymRGPromotionClosedIsFalse =
        refl
    ; ymGate3Closed =
        false
    ; ymGate3ClosedIsFalse =
        refl
    ; ymRhoAnalyticInhabitantProved =
        false
    ; ymRhoAnalyticInhabitantProvedIsFalse =
        refl
    ; dialecticalCarryAbsorbedRecorded =
        true
    ; dialecticalCarryAbsorbedRecordedIsTrue =
        refl
    ; braidTensionBoundedRecorded =
        true
    ; braidTensionBoundedRecordedIsTrue =
        refl
    ; sameProofShapeClaimed =
        true
    ; sameProofShapeClaimedIsTrue =
        refl
    ; proofShapeIsAnalogyGovernance =
        true
    ; proofShapeIsAnalogyGovernanceIsTrue =
        refl
    ; analogyDialecticCarryBounded =
        true
    ; analogyDialecticCarryBoundedIsTrue =
        refl
    ; analyticInhabitantsProved =
        false
    ; analyticInhabitantsProvedIsFalse =
        refl
    ; physicsTheoremPromoted =
        false
    ; physicsTheoremPromotedIsFalse =
        refl
    ; gate3TheoremPromoted =
        false
    ; gate3TheoremPromotedIsFalse =
        refl
    ; clayPromotionMade =
        false
    ; clayPromotionMadeIsFalse =
        refl
    ; terminalPromotionMade =
        false
    ; terminalPromotionMadeIsFalse =
        refl
    ; analyticInhabitantObligations =
        canonicalAnalyticInhabitantObligations
    ; analyticInhabitantObligationsAreCanonical =
        refl
    ; boundaries =
        canonicalUnifiedMarginBoundaries
    ; boundariesAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; noPromotion =
        unifiedMarginPromotionImpossibleHere
    ; signedMarginFormulaReading =
        signedMarginFormulaStatement
    ; signedMarginFormulaReadingIsCanonical =
        refl
    ; marginRatioFormulaReading =
        marginRatioFormulaStatement
    ; marginRatioFormulaReadingIsCanonical =
        refl
    ; l0_1DynamicsBoundReading =
        l0_1DynamicsBoundStatement
    ; l0_1DynamicsBoundReadingIsCanonical =
        refl
    ; l0_2SignedMarginEquivalentToRatioReading =
        l0_2SignedMarginEquivalentToRatioStatement
    ; l0_2SignedMarginEquivalentToRatioReadingIsCanonical =
        refl
    ; failClosedMarginSemanticsReading =
        failClosedMarginSemanticsStatement
    ; failClosedMarginSemanticsReadingIsCanonical =
        refl
    ; nsThetaReading =
        nsThetaStatement
    ; nsThetaReadingIsCanonical =
        refl
    ; ymRhoReading =
        ymRhoStatement
    ; ymRhoReadingIsCanonical =
        refl
    ; dialecticalCarryReading =
        dialecticalCarryStatement
    ; dialecticalCarryReadingIsCanonical =
        refl
    ; braidTensionReading =
        braidTensionStatement
    ; braidTensionReadingIsCanonical =
        refl
    ; unifiedStatement =
        unifiedMarginStatement
    ; unifiedStatementIsCanonical =
        refl
    ; receiptBoundary =
        "Records L0.1 DynamicsBound as bounded-dynamics margin grammar, not an analytic dynamics theorem"
        ∷ "Records L0.2 SignedMarginEquivalentToRatio as definitional bookkeeping, not a physics theorem"
        ∷ "Records signed margin = absorber_strength - promoted_activity"
        ∷ "Records margin ratio = 1 - seam gauge"
        ∷ "Records fail-closed pass/boundary/fail/missing margin semantics"
        ∷ "Records theta and rho as seam gauges, not proofs"
        ∷ "Records margin variables as making failure local, typed, measurable, and receipt-addressable"
        ∷ "Records NS theta<1 as a sufficient-proxy / continuation-route marker with BKM equivalence open"
        ∷ "Records YM rho<1 as a conditional KP margin with RG promotion open and Gate3 open"
        ∷ "Consumes pressure/depth and carry-absorption receipts to record carry absorbed into depth/history"
        ∷ "Consumes distributed tension receipt to record bounded braid/tension in the negotiated middle"
        ∷ "The common invariant is analogy/dialectic carry governance only"
        ∷ "No physics theorem, Gate 3 theorem, analytic inhabitant, Clay promotion, or terminal promotion follows"
        ∷ []
    }

canonicalUnifiedMarginNoAnalyticInhabitants :
  analyticInhabitantsProved canonicalUnifiedMarginInvariantReceipt ≡ false
canonicalUnifiedMarginNoAnalyticInhabitants =
  refl

canonicalUnifiedMarginNoPhysicsTheorem :
  physicsTheoremPromoted canonicalUnifiedMarginInvariantReceipt ≡ false
canonicalUnifiedMarginNoPhysicsTheorem =
  refl

canonicalUnifiedMarginNoGate3Theorem :
  gate3TheoremPromoted canonicalUnifiedMarginInvariantReceipt ≡ false
canonicalUnifiedMarginNoGate3Theorem =
  refl

canonicalUnifiedMarginNoClayPromotion :
  clayPromotionMade canonicalUnifiedMarginInvariantReceipt ≡ false
canonicalUnifiedMarginNoClayPromotion =
  refl

canonicalUnifiedMarginThetaIsSeamGauge :
  nsThetaIsSeamGaugeNotProof canonicalUnifiedMarginInvariantReceipt ≡ true
canonicalUnifiedMarginThetaIsSeamGauge =
  refl

canonicalUnifiedMarginRhoIsSeamGauge :
  ymRhoIsSeamGaugeNotProof canonicalUnifiedMarginInvariantReceipt ≡ true
canonicalUnifiedMarginRhoIsSeamGauge =
  refl

canonicalUnifiedMarginSignedFormula :
  signedMarginFormula canonicalUnifiedMarginInvariantReceipt
  ≡
  signedMarginEqualsAbsorberStrengthMinusPromotedActivity
canonicalUnifiedMarginSignedFormula =
  refl

canonicalUnifiedMarginRatioFormula :
  marginRatioFormula canonicalUnifiedMarginInvariantReceipt
  ≡
  marginRatioEqualsOneMinusSeamGauge
canonicalUnifiedMarginRatioFormula =
  refl

canonicalUnifiedMarginL0Grammar :
  l0MarginGrammar canonicalUnifiedMarginInvariantReceipt
  ≡
  canonicalL0MarginGrammarItems
canonicalUnifiedMarginL0Grammar =
  refl

canonicalUnifiedMarginL0_1DynamicsBoundRecorded :
  l0_1DynamicsBoundRecorded canonicalUnifiedMarginInvariantReceipt ≡ true
canonicalUnifiedMarginL0_1DynamicsBoundRecorded =
  refl

canonicalUnifiedMarginL0_1DynamicsBoundNotPromoted :
  l0_1DynamicsBoundPromotedToTheorem canonicalUnifiedMarginInvariantReceipt
  ≡
  false
canonicalUnifiedMarginL0_1DynamicsBoundNotPromoted =
  refl

canonicalUnifiedMarginL0_2SignedMarginEquivalentToRatioRecorded :
  l0_2SignedMarginEquivalentToRatioRecorded
    canonicalUnifiedMarginInvariantReceipt
  ≡
  true
canonicalUnifiedMarginL0_2SignedMarginEquivalentToRatioRecorded =
  refl

canonicalUnifiedMarginL0_2SignedMarginEquivalentToRatioNotPromoted :
  l0_2SignedMarginEquivalentToRatioPromotedToTheorem
    canonicalUnifiedMarginInvariantReceipt
  ≡
  false
canonicalUnifiedMarginL0_2SignedMarginEquivalentToRatioNotPromoted =
  refl

canonicalUnifiedMarginFailClosedSemantics :
  failClosedMarginSemantics canonicalUnifiedMarginInvariantReceipt
  ≡
  canonicalFailClosedMarginSemantics
canonicalUnifiedMarginFailClosedSemantics =
  refl

canonicalUnifiedMarginBKMEquivalenceOpen :
  nsBKMEquivalenceProved canonicalUnifiedMarginInvariantReceipt ≡ false
canonicalUnifiedMarginBKMEquivalenceOpen =
  refl

canonicalUnifiedMarginRGPromotionOpen :
  ymRGPromotionClosed canonicalUnifiedMarginInvariantReceipt ≡ false
canonicalUnifiedMarginRGPromotionOpen =
  refl
