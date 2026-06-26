module DASHI.Physics.Closure.NSDelta1UniformGateReductionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Fail-closed L3-a / L3-b uniform-gate reduction receipt.
--
-- This module records the remaining quantitative obstruction as a
-- conditional reduction:
--
--   L3-a residual  ->  uniform lower bound delta1 >= delta0 > 0
--
-- once the alignment ODE and pressure-correction scale are accepted.
-- The receipt explicitly keeps the L3-a closure conditional and exposes
-- L3-b as the exact live quantitative gate.  No promotion is asserted.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Status and canonical lanes.

data NSDelta1UniformGateReductionStatus : Set where
  l3aConditionalClosureReducesToL3bQuantitativeGate :
    NSDelta1UniformGateReductionStatus

data NSDelta1UniformGateReductionAssumption : Set where
  alignmentODEAccepted :
    NSDelta1UniformGateReductionAssumption
  pressureCorrectionScaleAccepted :
    NSDelta1UniformGateReductionAssumption
  l3aConditionalClosureRecorded :
    NSDelta1UniformGateReductionAssumption
  l3bExactLiveQuantitativeGateRecorded :
    NSDelta1UniformGateReductionAssumption
  delta1AtLeastDelta0PositiveTargetRecorded :
    NSDelta1UniformGateReductionAssumption
  noPromotionAuthorityRecorded :
    NSDelta1UniformGateReductionAssumption

canonicalNSDelta1UniformGateReductionAssumptions :
  List NSDelta1UniformGateReductionAssumption
canonicalNSDelta1UniformGateReductionAssumptions =
  alignmentODEAccepted
  ∷ pressureCorrectionScaleAccepted
  ∷ l3aConditionalClosureRecorded
  ∷ l3bExactLiveQuantitativeGateRecorded
  ∷ delta1AtLeastDelta0PositiveTargetRecorded
  ∷ noPromotionAuthorityRecorded
  ∷ []

nsDelta1UniformGateReductionAssumptionCount : Nat
nsDelta1UniformGateReductionAssumptionCount =
  listLength canonicalNSDelta1UniformGateReductionAssumptions

nsDelta1UniformGateReductionAssumptionCountIs6 :
  nsDelta1UniformGateReductionAssumptionCount ≡ 6
nsDelta1UniformGateReductionAssumptionCountIs6 =
  refl

data NSDelta1UniformGateReductionStage : Set where
  l3aResidualNamed :
    NSDelta1UniformGateReductionStage
  alignmentODEScaleAccepted :
    NSDelta1UniformGateReductionStage
  pressureCorrectionScaleAcceptedStage :
    NSDelta1UniformGateReductionStage
  uniformLowerBoundReductionRecorded :
    NSDelta1UniformGateReductionStage
  l3bLiveQuantitativeGateRecorded :
    NSDelta1UniformGateReductionStage
  failClosedNoPromotionRecorded :
    NSDelta1UniformGateReductionStage

canonicalNSDelta1UniformGateReductionStages :
  List NSDelta1UniformGateReductionStage
canonicalNSDelta1UniformGateReductionStages =
  l3aResidualNamed
  ∷ alignmentODEScaleAccepted
  ∷ pressureCorrectionScaleAcceptedStage
  ∷ uniformLowerBoundReductionRecorded
  ∷ l3bLiveQuantitativeGateRecorded
  ∷ failClosedNoPromotionRecorded
  ∷ []

nsDelta1UniformGateReductionStageCount : Nat
nsDelta1UniformGateReductionStageCount =
  listLength canonicalNSDelta1UniformGateReductionStages

nsDelta1UniformGateReductionStageCountIs6 :
  nsDelta1UniformGateReductionStageCount ≡ 6
nsDelta1UniformGateReductionStageCountIs6 =
  refl

data NSDelta1UniformGateReductionBlocker : Set where
  l3aResidualStillConditional :
    NSDelta1UniformGateReductionBlocker
  delta1UniformLowerBoundNotYetDischarged :
    NSDelta1UniformGateReductionBlocker
  alignmentODENotPromotedToTerminalAuthority :
    NSDelta1UniformGateReductionBlocker
  pressureCorrectionScaleNotPromotedToTerminalAuthority :
    NSDelta1UniformGateReductionBlocker
  promotionFlagsRemainFalse :
    NSDelta1UniformGateReductionBlocker

canonicalNSDelta1UniformGateReductionBlockers :
  List NSDelta1UniformGateReductionBlocker
canonicalNSDelta1UniformGateReductionBlockers =
  l3aResidualStillConditional
  ∷ delta1UniformLowerBoundNotYetDischarged
  ∷ alignmentODENotPromotedToTerminalAuthority
  ∷ pressureCorrectionScaleNotPromotedToTerminalAuthority
  ∷ promotionFlagsRemainFalse
  ∷ []

nsDelta1UniformGateReductionBlockerCount : Nat
nsDelta1UniformGateReductionBlockerCount =
  listLength canonicalNSDelta1UniformGateReductionBlockers

nsDelta1UniformGateReductionBlockerCountIs5 :
  nsDelta1UniformGateReductionBlockerCount ≡ 5
nsDelta1UniformGateReductionBlockerCountIs5 =
  refl

data NSDelta1UniformGatePromotionFlag : Set where
  l3aPromotedFlag :
    NSDelta1UniformGatePromotionFlag
  l3bPromotedFlag :
    NSDelta1UniformGatePromotionFlag
  clayPromotedFlag :
    NSDelta1UniformGatePromotionFlag
  terminalPromotedFlag :
    NSDelta1UniformGatePromotionFlag

data ORCSLPGFRow : Set where
  O_l3aConditionalClosureRecorded :
    ORCSLPGFRow
  R_reductionToUniformLowerBoundRecorded :
    ORCSLPGFRow
  C_alignmentODEAndPressureScaleAccepted :
    ORCSLPGFRow
  S_promotionFlagsRemainFalse :
    ORCSLPGFRow
  L_l3aFeedsL3bExactLiveQuantitativeGate :
    ORCSLPGFRow
  P_proveUniformLowerBoundDelta1GeDelta0Positive :
    ORCSLPGFRow
  G_liveGateStaysQuantitativeNotPromoted :
    ORCSLPGFRow
  F_failClosedResidualRemainsOpen :
    ORCSLPGFRow

canonicalORCSLPGFRows :
  List ORCSLPGFRow
canonicalORCSLPGFRows =
  O_l3aConditionalClosureRecorded
  ∷ R_reductionToUniformLowerBoundRecorded
  ∷ C_alignmentODEAndPressureScaleAccepted
  ∷ S_promotionFlagsRemainFalse
  ∷ L_l3aFeedsL3bExactLiveQuantitativeGate
  ∷ P_proveUniformLowerBoundDelta1GeDelta0Positive
  ∷ G_liveGateStaysQuantitativeNotPromoted
  ∷ F_failClosedResidualRemainsOpen
  ∷ []

nsDelta1UniformGateReductionORCSLPGFRowCount : Nat
nsDelta1UniformGateReductionORCSLPGFRowCount =
  listLength canonicalORCSLPGFRows

nsDelta1UniformGateReductionORCSLPGFRowCountIs8 :
  nsDelta1UniformGateReductionORCSLPGFRowCount ≡ 8
nsDelta1UniformGateReductionORCSLPGFRowCountIs8 =
  refl

------------------------------------------------------------------------
-- Canonical string payloads.

alignmentODEAcceptedText : String
alignmentODEAcceptedText =
  "alignment ODE scale accepted as the background analytic carrier for the L3-a residual"

pressureCorrectionScaleAcceptedText : String
pressureCorrectionScaleAcceptedText =
  "pressure-correction scale accepted as the live quantitative normalization"

l3aConditionalClosureText : String
l3aConditionalClosureText =
  "L3-a remains conditionally closed only after the alignment ODE and pressure-correction scale are accepted"

l3bExactLiveQuantitativeGateText : String
l3bExactLiveQuantitativeGateText =
  "L3-b is the exact live quantitative gate: the remaining obstruction reduces to a uniform lower bound delta1 >= delta0 > 0"

uniformLowerBoundReductionText : String
uniformLowerBoundReductionText =
  "The remaining L3-a obstruction reduces to delta1 >= delta0 > 0 once the alignment ODE / pressure-correction scale is accepted"

delta0PositiveText : String
delta0PositiveText =
  "delta0 is recorded as strictly positive"

delta1GeDelta0Text : String
delta1GeDelta0Text =
  "delta1 is recorded as at least delta0"

failClosedStatement : String
failClosedStatement =
  "Fail-closed receipt: conditional L3-a closure reduces to the live L3-b quantitative gate, with delta1 >= delta0 > 0 recorded as the remaining lower-bound requirement and all promotion flags false."

orcsLpgfSummaryText : String
orcsLpgfSummaryText =
  "O records the L3-a conditional closure residual; R records the reduction to a uniform lower bound; C records the accepted alignment ODE and pressure-correction scale; S records that promotion flags stay false; L records that L3-a feeds the exact L3-b live quantitative gate; P records the remaining delta1 >= delta0 > 0 proof obligation; G records that the gate remains quantitative and non-promoting; F records that the residual is still open in fail-closed form."

------------------------------------------------------------------------
-- Canonical receipt.

record NSDelta1UniformGateReductionReceipt : Setω where
  field
    status :
      NSDelta1UniformGateReductionStatus

    statusIsCanonical :
      status ≡ l3aConditionalClosureReducesToL3bQuantitativeGate

    assumptions :
      List NSDelta1UniformGateReductionAssumption

    assumptionsAreCanonical :
      assumptions ≡ canonicalNSDelta1UniformGateReductionAssumptions

    assumptionCount :
      Nat

    assumptionCountIs6 :
      assumptionCount ≡ 6

    stages :
      List NSDelta1UniformGateReductionStage

    stagesAreCanonical :
      stages ≡ canonicalNSDelta1UniformGateReductionStages

    stageCount :
      Nat

    stageCountIs6 :
      stageCount ≡ 6

    blockers :
      List NSDelta1UniformGateReductionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalNSDelta1UniformGateReductionBlockers

    blockerCount :
      Nat

    blockerCountIs5 :
      blockerCount ≡ 5

    l3aConditionalClosureRecordedFlag :
      Bool

    l3aConditionalClosureRecordedFlagIsTrue :
      l3aConditionalClosureRecordedFlag ≡ true

    alignmentODEAcceptedFlag :
      Bool

    alignmentODEAcceptedFlagIsTrue :
      alignmentODEAcceptedFlag ≡ true

    pressureCorrectionScaleAcceptedFlag :
      Bool

    pressureCorrectionScaleAcceptedFlagIsTrue :
      pressureCorrectionScaleAcceptedFlag ≡ true

    l3aConditionalClosureTextValue :
      String

    l3aConditionalClosureTextValueIsCanonical :
      l3aConditionalClosureTextValue ≡ l3aConditionalClosureText

    l3bExactLiveQuantitativeGate :
      Bool

    l3bExactLiveQuantitativeGateIsTrue :
      l3bExactLiveQuantitativeGate ≡ true

    l3bExactLiveQuantitativeGateTextValue :
      String

    l3bExactLiveQuantitativeGateTextValueIsCanonical :
      l3bExactLiveQuantitativeGateTextValue ≡ l3bExactLiveQuantitativeGateText

    uniformLowerBoundReductionTextValue :
      String

    uniformLowerBoundReductionTextValueIsCanonical :
      uniformLowerBoundReductionTextValue ≡ uniformLowerBoundReductionText

    delta0Positive :
      Bool

    delta0PositiveIsTrue :
      delta0Positive ≡ true

    delta1GeDelta0 :
      Bool

    delta1GeDelta0IsTrue :
      delta1GeDelta0 ≡ true

    failClosedStatementValue :
      String

    failClosedStatementValueIsCanonical :
      failClosedStatementValue ≡ failClosedStatement

    orcsLpgfRows :
      List ORCSLPGFRow

    orcsLpgfRowsAreCanonical :
      orcsLpgfRows ≡ canonicalORCSLPGFRows

    orcsLpgfRowCount :
      Nat

    orcsLpgfRowCountIs8 :
      orcsLpgfRowCount ≡ 8

    orcsLpgfSummaryTextValue :
      String

    orcsLpgfSummaryTextValueIsCanonical :
      orcsLpgfSummaryTextValue ≡ orcsLpgfSummaryText

    l3aPromoted :
      Bool

    l3aPromotedIsFalse :
      l3aPromoted ≡ false

    l3bPromoted :
      Bool

    l3bPromotedIsFalse :
      l3bPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    terminalPromoted :
      Bool

    terminalPromotedIsFalse :
      terminalPromoted ≡ false

    promotionFlags :
      List NSDelta1UniformGatePromotionFlag

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSDelta1UniformGateReductionReceipt public

canonicalNSDelta1UniformGateReductionReceipt :
  NSDelta1UniformGateReductionReceipt
canonicalNSDelta1UniformGateReductionReceipt =
  record
    { status =
        l3aConditionalClosureReducesToL3bQuantitativeGate
    ; statusIsCanonical =
        refl
    ; assumptions =
        canonicalNSDelta1UniformGateReductionAssumptions
    ; assumptionsAreCanonical =
        refl
    ; assumptionCount =
        nsDelta1UniformGateReductionAssumptionCount
    ; assumptionCountIs6 =
        refl
    ; stages =
        canonicalNSDelta1UniformGateReductionStages
    ; stagesAreCanonical =
        refl
    ; stageCount =
        nsDelta1UniformGateReductionStageCount
    ; stageCountIs6 =
        refl
    ; blockers =
        canonicalNSDelta1UniformGateReductionBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        nsDelta1UniformGateReductionBlockerCount
    ; blockerCountIs5 =
        refl
    ; l3aConditionalClosureRecordedFlag =
        true
    ; l3aConditionalClosureRecordedFlagIsTrue =
        refl
    ; alignmentODEAcceptedFlag =
        true
    ; alignmentODEAcceptedFlagIsTrue =
        refl
    ; pressureCorrectionScaleAcceptedFlag =
        true
    ; pressureCorrectionScaleAcceptedFlagIsTrue =
        refl
    ; l3aConditionalClosureTextValue =
        l3aConditionalClosureText
    ; l3aConditionalClosureTextValueIsCanonical =
        refl
    ; l3bExactLiveQuantitativeGate =
        true
    ; l3bExactLiveQuantitativeGateIsTrue =
        refl
    ; l3bExactLiveQuantitativeGateTextValue =
        l3bExactLiveQuantitativeGateText
    ; l3bExactLiveQuantitativeGateTextValueIsCanonical =
        refl
    ; uniformLowerBoundReductionTextValue =
        uniformLowerBoundReductionText
    ; uniformLowerBoundReductionTextValueIsCanonical =
        refl
    ; delta0Positive =
        true
    ; delta0PositiveIsTrue =
        refl
    ; delta1GeDelta0 =
        true
    ; delta1GeDelta0IsTrue =
        refl
    ; failClosedStatementValue =
        failClosedStatement
    ; failClosedStatementValueIsCanonical =
        refl
    ; orcsLpgfRows =
        canonicalORCSLPGFRows
    ; orcsLpgfRowsAreCanonical =
        refl
    ; orcsLpgfRowCount =
        nsDelta1UniformGateReductionORCSLPGFRowCount
    ; orcsLpgfRowCountIs8 =
        refl
    ; orcsLpgfSummaryTextValue =
        orcsLpgfSummaryText
    ; orcsLpgfSummaryTextValueIsCanonical =
        refl
    ; l3aPromoted =
        false
    ; l3aPromotedIsFalse =
        refl
    ; l3bPromoted =
        false
    ; l3bPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; terminalPromoted =
        false
    ; terminalPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "L3-a conditional closure is recorded only as a gate, not a terminal theorem"
        ∷ "alignment ODE acceptance is required before the pressure-correction scale is treated as live"
        ∷ "pressure-correction scale acceptance is the quantitative normalization carrier"
        ∷ "the remaining obstruction reduces to delta1 >= delta0 > 0"
        ∷ "L3-b is the exact live quantitative gate"
        ∷ "all promotion flags remain false"
        ∷ "no terminal, Clay, or theorem promotion is constructed"
        ∷ []
    }

nsDelta1UniformGateReductionKeepsPromotionFalse :
  l3aPromoted canonicalNSDelta1UniformGateReductionReceipt ≡ false
nsDelta1UniformGateReductionKeepsPromotionFalse =
  refl

nsDelta1UniformGateReductionKeepsL3bGateLive :
  l3bExactLiveQuantitativeGate canonicalNSDelta1UniformGateReductionReceipt ≡ true
nsDelta1UniformGateReductionKeepsL3bGateLive =
  refl

nsDelta1UniformGateReductionKeepsUniformLowerBoundClaim :
  delta1GeDelta0 canonicalNSDelta1UniformGateReductionReceipt ≡ true
nsDelta1UniformGateReductionKeepsUniformLowerBoundClaim =
  refl

------------------------------------------------------------------------
-- The receipt carries no constructive promotion path.

data NSDelta1UniformGateReductionNoPromotion : Set where

nsDelta1UniformGateReductionNoPromotion :
  NSDelta1UniformGateReductionNoPromotion →
  ⊥
nsDelta1UniformGateReductionNoPromotion ()
