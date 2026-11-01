module DASHI.Physics.Closure.NSA4UniformErrorBudgetCompositeBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSA4ExceptionalMassCompositeBoundary
  as Exceptional
import DASHI.Physics.Closure.NSBonyLipschitzAngularPushforwardBoundary
  as Bony
import DASHI.Physics.Closure.NSLowVorticityExceptionalMassRoutingBoundary
  as LowVorticity
import DASHI.Physics.Closure.NSOutputStripPreimageMeasureEstimateBoundary
  as OutputPreimage

------------------------------------------------------------------------
-- NS A4 uniform error-budget composite boundary.
--
-- This module composes four already-recorded A4 boundary surfaces into a
-- single uniform error-budget receipt:
--
--   c eta lower bound
--     - output strip / log-window losses
--     - antipodal tube losses
--     - low-vorticity and null-output discard losses
--     - Bony/Lipschitz angular perturbation losses.
--
-- It is deliberately fail-closed.  The budget ledger records the intended
-- theorem shape and the required child inputs, but it does not prove the
-- uniform lower bound, does not promote A4, does not promote A6, and does
-- not promote Navier-Stokes Clay.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported boundary anchors.

outputStripPreimageMeasureEstimateBoundaryReference : String
outputStripPreimageMeasureEstimateBoundaryReference =
  "DASHI.Physics.Closure.NSOutputStripPreimageMeasureEstimateBoundary"

a4ExceptionalMassCompositeBoundaryReference : String
a4ExceptionalMassCompositeBoundaryReference =
  "DASHI.Physics.Closure.NSA4ExceptionalMassCompositeBoundary"

bonyLipschitzAngularPushforwardBoundaryReference : String
bonyLipschitzAngularPushforwardBoundaryReference =
  "DASHI.Physics.Closure.NSBonyLipschitzAngularPushforwardBoundary"

lowVorticityExceptionalMassRoutingBoundaryReference : String
lowVorticityExceptionalMassRoutingBoundaryReference =
  "DASHI.Physics.Closure.NSLowVorticityExceptionalMassRoutingBoundary"

record ImportedUniformErrorBudgetCompositeSupport : Set where
  field
    outputPreimageBoundary :
      OutputPreimage.NSOutputStripPreimageMeasureEstimateBoundary
    outputPreimageBoundaryIsCanonical :
      outputPreimageBoundary
        ≡ OutputPreimage.canonicalNSOutputStripPreimageMeasureEstimateBoundary
    exceptionalMassBoundary :
      Exceptional.NSA4ExceptionalMassCompositeBoundary
    exceptionalMassBoundaryIsCanonical :
      exceptionalMassBoundary
        ≡ Exceptional.canonicalNSA4ExceptionalMassCompositeBoundary
    bonyPushforwardSupport :
      Bony.ImportedBonyLipschitzAngularPushforwardSupport
    bonyPushforwardSupportIsCanonical :
      bonyPushforwardSupport
        ≡ Bony.canonicalImportedBonyLipschitzAngularPushforwardSupport
    lowVorticitySupport :
      LowVorticity.ImportedLowVorticityExceptionalMassSupport
    lowVorticitySupportIsCanonical :
      lowVorticitySupport
        ≡ LowVorticity.canonicalImportedLowVorticityExceptionalMassSupport

    outputPreimageTarget :
      OutputPreimage.OutputStripPreimageMeasureEstimateTarget
    outputPreimageTargetIsCanonical :
      outputPreimageTarget
        ≡ OutputPreimage.canonicalOutputStripPreimageMeasureEstimateTarget
    exceptionalMassTarget :
      Exceptional.A4ExceptionalMassCompositeTarget
    exceptionalMassTargetIsCanonical :
      exceptionalMassTarget
        ≡ Exceptional.canonicalA4ExceptionalMassCompositeTarget
    bonyPushforwardTarget :
      Bony.BonyLipschitzAngularPushforwardTarget
    bonyPushforwardTargetIsCanonical :
      bonyPushforwardTarget
        ≡ Bony.canonicalBonyLipschitzAngularPushforwardTarget
    lowVorticityTarget :
      LowVorticity.LowVorticityExceptionalMassRoutingTarget
    lowVorticityTargetIsCanonical :
      lowVorticityTarget
        ≡ LowVorticity.canonicalLowVorticityExceptionalMassRoutingTarget

    outputPreimageBoundaryRecorded :
      OutputPreimage.NSOutputStripPreimageMeasureEstimateBoundaryRecorded
        ≡ true
    exceptionalCompositeBoundaryRecorded :
      Exceptional.NSA4ExceptionalMassCompositeBoundaryRecorded ≡ true
    bonyPushforwardBoundaryRecorded :
      Bony.NSBonyLipschitzAngularPushforwardBoundaryRecorded ≡ true
    lowVorticityBoundaryRecorded :
      LowVorticity.NSLowVorticityExceptionalMassRoutingBoundaryRecorded
        ≡ true

    outputPreimageTheoremNowTrue :
      OutputPreimage.OutputStripPreimageMeasureEstimateProved ≡ true
    exceptionalCompositeTheoremStillFalse :
      Exceptional.exceptionalMassRoutingCompositeProved ≡ false
    bonyPushforwardTheoremStillFalse :
      Bony.BonyLipschitzAngularPushforwardStabilityProved ≡ false
    lowVorticityTheoremStillFalse :
      LowVorticity.A4LowVorticityExceptionalMassRoutingProved ≡ false

canonicalImportedUniformErrorBudgetCompositeSupport :
  ImportedUniformErrorBudgetCompositeSupport
canonicalImportedUniformErrorBudgetCompositeSupport =
  record
    { outputPreimageBoundary =
        OutputPreimage.canonicalNSOutputStripPreimageMeasureEstimateBoundary
    ; outputPreimageBoundaryIsCanonical =
        refl
    ; exceptionalMassBoundary =
        Exceptional.canonicalNSA4ExceptionalMassCompositeBoundary
    ; exceptionalMassBoundaryIsCanonical =
        refl
    ; bonyPushforwardSupport =
        Bony.canonicalImportedBonyLipschitzAngularPushforwardSupport
    ; bonyPushforwardSupportIsCanonical =
        refl
    ; lowVorticitySupport =
        LowVorticity.canonicalImportedLowVorticityExceptionalMassSupport
    ; lowVorticitySupportIsCanonical =
        refl
    ; outputPreimageTarget =
        OutputPreimage.canonicalOutputStripPreimageMeasureEstimateTarget
    ; outputPreimageTargetIsCanonical =
        refl
    ; exceptionalMassTarget =
        Exceptional.canonicalA4ExceptionalMassCompositeTarget
    ; exceptionalMassTargetIsCanonical =
        refl
    ; bonyPushforwardTarget =
        Bony.canonicalBonyLipschitzAngularPushforwardTarget
    ; bonyPushforwardTargetIsCanonical =
        refl
    ; lowVorticityTarget =
        LowVorticity.canonicalLowVorticityExceptionalMassRoutingTarget
    ; lowVorticityTargetIsCanonical =
        refl
    ; outputPreimageBoundaryRecorded =
        refl
    ; exceptionalCompositeBoundaryRecorded =
        refl
    ; bonyPushforwardBoundaryRecorded =
        refl
    ; lowVorticityBoundaryRecorded =
        refl
    ; outputPreimageTheoremNowTrue =
        refl
    ; exceptionalCompositeTheoremStillFalse =
        refl
    ; bonyPushforwardTheoremStillFalse =
        refl
    ; lowVorticityTheoremStillFalse =
        refl
    }

------------------------------------------------------------------------
-- Uniform error-budget carriers.

data UniformA4PositiveMassScaleCarrier : Set where
  cEtaLowerBoundScaleFromOutputStripPreimage :
    Nat →
    OutputPreimage.OutputStripPreimageMeasureEstimateCarrier →
    OutputPreimage.A4OutputStripPreimageEstimateConsumer →
    UniformA4PositiveMassScaleCarrier

data LogWindowOutputStripErrorCarrier : Set where
  subtractOutputStripAndLogWindowMismatch :
    OutputPreimage.StripWidthJacobianBudgetCarrier →
    Exceptional.LogWindowEpsilonDeltaRoutingCarrier →
    Exceptional.A4ExceptionalMassBudgetLine →
    LogWindowOutputStripErrorCarrier

data AntipodalErrorCarrier : Set where
  subtractAntipodalTubeAndNormalizeSumDegeneracy :
    OutputPreimage.NullExceptionalBudgetCarrier →
    Exceptional.ExceptionalMassBudgetCarrier →
    Exceptional.A4ExceptionalMassBudgetLine →
    AntipodalErrorCarrier

data LowVorticityErrorCarrier : Set where
  subtractLowVorticityNullOutputAndResidualDiscard :
    LowVorticity.LowVorticityExceptionalSetCarrier →
    LowVorticity.NullOutputCHatExclusionCarrier →
    LowVorticity.LowerOrderResidualBudgetCarrier →
    Exceptional.ExceptionalMassBudgetCarrier →
    LowVorticityErrorCarrier

data BonyPerturbationErrorCarrier : Set where
  subtractBonyLipschitzAngularPushforwardPerturbation :
    Bony.AngularPerturbationEstimateCarrier →
    Bony.OffDegenerateTriadLipschitzCarrier →
    Bony.LowerOrderAngularErrorRoutingCarrier →
    Exceptional.A4ExceptionalMassBudgetLine →
    BonyPerturbationErrorCarrier

data UniformA4ErrorSubtractionLedger : Set where
  subtractFourPerturbationClassesFromCEtaLowerBound :
    UniformA4PositiveMassScaleCarrier →
    LogWindowOutputStripErrorCarrier →
    AntipodalErrorCarrier →
    LowVorticityErrorCarrier →
    BonyPerturbationErrorCarrier →
    UniformA4ErrorSubtractionLedger

data UniformA4ErrorBudgetInequalityShape : Set where
  cEtaMinusLogAntipodalLowVorticityAndBonyErrors :
    UniformA4ErrorSubtractionLedger →
    OutputPreimage.OutputStripPreimageMeasureEstimateTarget →
    Exceptional.A4ExceptionalMassCompositeTarget →
    Bony.BonyLipschitzAngularPushforwardTarget →
    LowVorticity.LowVorticityExceptionalMassRoutingTarget →
    UniformA4ErrorBudgetInequalityShape

data UniformA4FailClosedTheoremCarrier : Set where
  recordUniformBudgetButDoNotPromoteA4 :
    UniformA4ErrorBudgetInequalityShape →
    Exceptional.A4FailClosedConsumerCarrier →
    OutputPreimage.A4OutputStripPreimageEstimateConsumer →
    UniformA4FailClosedTheoremCarrier

data UniformA4ErrorBudgetCompositeTarget : Set where
  A4UniformErrorBudgetRecordedWithClosedPromotions :
    ImportedUniformErrorBudgetCompositeSupport →
    UniformA4PositiveMassScaleCarrier →
    LogWindowOutputStripErrorCarrier →
    AntipodalErrorCarrier →
    LowVorticityErrorCarrier →
    BonyPerturbationErrorCarrier →
    UniformA4ErrorSubtractionLedger →
    UniformA4ErrorBudgetInequalityShape →
    UniformA4FailClosedTheoremCarrier →
    UniformA4ErrorBudgetCompositeTarget

canonicalUniformA4PositiveMassScaleCarrier :
  UniformA4PositiveMassScaleCarrier
canonicalUniformA4PositiveMassScaleCarrier =
  cEtaLowerBoundScaleFromOutputStripPreimage
    (suc zero)
    OutputPreimage.canonicalOutputStripPreimageMeasureEstimateCarrier
    OutputPreimage.canonicalA4OutputStripPreimageEstimateConsumer

canonicalLogWindowOutputStripErrorCarrier :
  LogWindowOutputStripErrorCarrier
canonicalLogWindowOutputStripErrorCarrier =
  subtractOutputStripAndLogWindowMismatch
    OutputPreimage.canonicalStripWidthJacobianBudgetCarrier
    Exceptional.canonicalLogWindowEpsilonDeltaRouting
    Exceptional.deltaAbelLogWindowMismatchLine

canonicalAntipodalErrorCarrier :
  AntipodalErrorCarrier
canonicalAntipodalErrorCarrier =
  subtractAntipodalTubeAndNormalizeSumDegeneracy
    OutputPreimage.canonicalNullExceptionalBudgetCarrier
    Exceptional.canonicalExceptionalMassBudgetCarrier
    Exceptional.epsilonAntipodalTubeMassLine

canonicalLowVorticityErrorCarrier :
  LowVorticityErrorCarrier
canonicalLowVorticityErrorCarrier =
  subtractLowVorticityNullOutputAndResidualDiscard
    LowVorticity.canonicalLowVorticityExceptionalSet
    LowVorticity.canonicalNullOutputCHatExclusion
    LowVorticity.canonicalLowerOrderResidualBudget
    Exceptional.canonicalExceptionalMassBudgetCarrier

canonicalBonyPerturbationErrorCarrier :
  BonyPerturbationErrorCarrier
canonicalBonyPerturbationErrorCarrier =
  subtractBonyLipschitzAngularPushforwardPerturbation
    Bony.canonicalAngularPerturbationEstimateCarrier
    Bony.canonicalOffDegenerateTriadLipschitzCarrier
    Bony.canonicalLowerOrderAngularErrorRoutingCarrier
    Exceptional.bonyLipschitzAngularPerturbationLine

canonicalUniformA4ErrorSubtractionLedger :
  UniformA4ErrorSubtractionLedger
canonicalUniformA4ErrorSubtractionLedger =
  subtractFourPerturbationClassesFromCEtaLowerBound
    canonicalUniformA4PositiveMassScaleCarrier
    canonicalLogWindowOutputStripErrorCarrier
    canonicalAntipodalErrorCarrier
    canonicalLowVorticityErrorCarrier
    canonicalBonyPerturbationErrorCarrier

canonicalUniformA4ErrorBudgetInequalityShape :
  UniformA4ErrorBudgetInequalityShape
canonicalUniformA4ErrorBudgetInequalityShape =
  cEtaMinusLogAntipodalLowVorticityAndBonyErrors
    canonicalUniformA4ErrorSubtractionLedger
    OutputPreimage.canonicalOutputStripPreimageMeasureEstimateTarget
    Exceptional.canonicalA4ExceptionalMassCompositeTarget
    Bony.canonicalBonyLipschitzAngularPushforwardTarget
    LowVorticity.canonicalLowVorticityExceptionalMassRoutingTarget

canonicalUniformA4FailClosedTheoremCarrier :
  UniformA4FailClosedTheoremCarrier
canonicalUniformA4FailClosedTheoremCarrier =
  recordUniformBudgetButDoNotPromoteA4
    canonicalUniformA4ErrorBudgetInequalityShape
    Exceptional.canonicalA4FailClosedConsumerCarrier
    OutputPreimage.canonicalA4OutputStripPreimageEstimateConsumer

canonicalUniformA4ErrorBudgetCompositeTarget :
  UniformA4ErrorBudgetCompositeTarget
canonicalUniformA4ErrorBudgetCompositeTarget =
  A4UniformErrorBudgetRecordedWithClosedPromotions
    canonicalImportedUniformErrorBudgetCompositeSupport
    canonicalUniformA4PositiveMassScaleCarrier
    canonicalLogWindowOutputStripErrorCarrier
    canonicalAntipodalErrorCarrier
    canonicalLowVorticityErrorCarrier
    canonicalBonyPerturbationErrorCarrier
    canonicalUniformA4ErrorSubtractionLedger
    canonicalUniformA4ErrorBudgetInequalityShape
    canonicalUniformA4FailClosedTheoremCarrier

------------------------------------------------------------------------
-- Obligations, budget lines, blockers, and statuses.

data UniformA4ErrorBudgetCompositeObligation : Set where
  importFourA4BudgetChildBoundaries :
    UniformA4ErrorBudgetCompositeObligation
  recordCEtaLowerBoundFromOutputPreimageEstimate :
    UniformA4ErrorBudgetCompositeObligation
  subtractLogWindowAndOutputStripMismatch :
    UniformA4ErrorBudgetCompositeObligation
  subtractAntipodalTubeAndNormalizeSumDegeneracy :
    UniformA4ErrorBudgetCompositeObligation
  subtractLowVorticityNullOutputAndResidualDiscard :
    UniformA4ErrorBudgetCompositeObligation
  subtractBonyLipschitzAngularPerturbation :
    UniformA4ErrorBudgetCompositeObligation
  proveRemainingBudgetUniformAndPositive :
    UniformA4ErrorBudgetCompositeObligation
  feedUniformBudgetIntoFailClosedA4Consumer :
    UniformA4ErrorBudgetCompositeObligation
  keepA4A6ClayAndTerminalPromotionsClosed :
    UniformA4ErrorBudgetCompositeObligation

canonicalUniformA4ErrorBudgetCompositeObligations :
  List UniformA4ErrorBudgetCompositeObligation
canonicalUniformA4ErrorBudgetCompositeObligations =
  importFourA4BudgetChildBoundaries
  ∷ recordCEtaLowerBoundFromOutputPreimageEstimate
  ∷ subtractLogWindowAndOutputStripMismatch
  ∷ subtractAntipodalTubeAndNormalizeSumDegeneracy
  ∷ subtractLowVorticityNullOutputAndResidualDiscard
  ∷ subtractBonyLipschitzAngularPerturbation
  ∷ proveRemainingBudgetUniformAndPositive
  ∷ feedUniformBudgetIntoFailClosedA4Consumer
  ∷ keepA4A6ClayAndTerminalPromotionsClosed
  ∷ []

uniformA4ErrorBudgetCompositeObligationCount : Nat
uniformA4ErrorBudgetCompositeObligationCount =
  listLength canonicalUniformA4ErrorBudgetCompositeObligations

uniformA4ErrorBudgetCompositeObligationCountIs9 :
  uniformA4ErrorBudgetCompositeObligationCount ≡ 9
uniformA4ErrorBudgetCompositeObligationCountIs9 =
  refl

data UniformA4ErrorBudgetLine : Set where
  positiveCEtaLowerBoundLine :
    UniformA4ErrorBudgetLine
  logWindowOutputStripMismatchSubtractLine :
    UniformA4ErrorBudgetLine
  antipodalTubeSubtractLine :
    UniformA4ErrorBudgetLine
  lowVorticityDiscardSubtractLine :
    UniformA4ErrorBudgetLine
  nullOutputDiscardSubtractLine :
    UniformA4ErrorBudgetLine
  bonyLipschitzPerturbationSubtractLine :
    UniformA4ErrorBudgetLine
  residualUniformPositivityLine :
    UniformA4ErrorBudgetLine

canonicalUniformA4ErrorBudgetLines :
  List UniformA4ErrorBudgetLine
canonicalUniformA4ErrorBudgetLines =
  positiveCEtaLowerBoundLine
  ∷ logWindowOutputStripMismatchSubtractLine
  ∷ antipodalTubeSubtractLine
  ∷ lowVorticityDiscardSubtractLine
  ∷ nullOutputDiscardSubtractLine
  ∷ bonyLipschitzPerturbationSubtractLine
  ∷ residualUniformPositivityLine
  ∷ []

uniformA4ErrorBudgetLineCount : Nat
uniformA4ErrorBudgetLineCount =
  listLength canonicalUniformA4ErrorBudgetLines

uniformA4ErrorBudgetLineCountIs7 :
  uniformA4ErrorBudgetLineCount ≡ 7
uniformA4ErrorBudgetLineCountIs7 =
  refl

data UniformA4ErrorBudgetCompositeBlocker : Set where
  missingUniformCEtaLowerBound :
    UniformA4ErrorBudgetCompositeBlocker
  missingOutputStripPreimageMeasureTheorem :
    UniformA4ErrorBudgetCompositeBlocker
  missingLogWindowMismatchLimit :
    UniformA4ErrorBudgetCompositeBlocker
  missingAntipodalTubeMassEstimate :
    UniformA4ErrorBudgetCompositeBlocker
  missingLowVorticityExceptionalBudget :
    UniformA4ErrorBudgetCompositeBlocker
  missingNullOutputDiscardBound :
    UniformA4ErrorBudgetCompositeBlocker
  missingBonyLipschitzPerturbationBound :
    UniformA4ErrorBudgetCompositeBlocker
  missingResidualPositivityAfterSubtraction :
    UniformA4ErrorBudgetCompositeBlocker
  missingA4FourierOutputCouplingPromotion :
    UniformA4ErrorBudgetCompositeBlocker
  promotionsRemainClosed :
    UniformA4ErrorBudgetCompositeBlocker

canonicalUniformA4ErrorBudgetCompositeBlockers :
  List UniformA4ErrorBudgetCompositeBlocker
canonicalUniformA4ErrorBudgetCompositeBlockers =
  missingUniformCEtaLowerBound
  ∷ missingOutputStripPreimageMeasureTheorem
  ∷ missingLogWindowMismatchLimit
  ∷ missingAntipodalTubeMassEstimate
  ∷ missingLowVorticityExceptionalBudget
  ∷ missingNullOutputDiscardBound
  ∷ missingBonyLipschitzPerturbationBound
  ∷ missingResidualPositivityAfterSubtraction
  ∷ missingA4FourierOutputCouplingPromotion
  ∷ promotionsRemainClosed
  ∷ []

uniformA4ErrorBudgetCompositeBlockerCount : Nat
uniformA4ErrorBudgetCompositeBlockerCount =
  listLength canonicalUniformA4ErrorBudgetCompositeBlockers

uniformA4ErrorBudgetCompositeBlockerCountIs10 :
  uniformA4ErrorBudgetCompositeBlockerCount ≡ 10
uniformA4ErrorBudgetCompositeBlockerCountIs10 =
  refl

data UniformA4ErrorBudgetCompositeStatusRow : Set where
  uniformBudgetBoundaryRecordedStatus :
    UniformA4ErrorBudgetCompositeStatusRow
  fourChildSurfacesImportedStatus :
    UniformA4ErrorBudgetCompositeStatusRow
  cEtaLowerBoundScaleRecordedStatus :
    UniformA4ErrorBudgetCompositeStatusRow
  logWindowOutputStripErrorRecordedStatus :
    UniformA4ErrorBudgetCompositeStatusRow
  antipodalErrorRecordedStatus :
    UniformA4ErrorBudgetCompositeStatusRow
  lowVorticityErrorRecordedStatus :
    UniformA4ErrorBudgetCompositeStatusRow
  bonyPerturbationErrorRecordedStatus :
    UniformA4ErrorBudgetCompositeStatusRow
  subtractionLedgerRecordedStatus :
    UniformA4ErrorBudgetCompositeStatusRow
  failClosedA4ConsumerRecordedStatus :
    UniformA4ErrorBudgetCompositeStatusRow
  allTheoremAndPromotionFlagsFalseStatus :
    UniformA4ErrorBudgetCompositeStatusRow

canonicalUniformA4ErrorBudgetCompositeStatusRows :
  List UniformA4ErrorBudgetCompositeStatusRow
canonicalUniformA4ErrorBudgetCompositeStatusRows =
  uniformBudgetBoundaryRecordedStatus
  ∷ fourChildSurfacesImportedStatus
  ∷ cEtaLowerBoundScaleRecordedStatus
  ∷ logWindowOutputStripErrorRecordedStatus
  ∷ antipodalErrorRecordedStatus
  ∷ lowVorticityErrorRecordedStatus
  ∷ bonyPerturbationErrorRecordedStatus
  ∷ subtractionLedgerRecordedStatus
  ∷ failClosedA4ConsumerRecordedStatus
  ∷ allTheoremAndPromotionFlagsFalseStatus
  ∷ []

uniformA4ErrorBudgetCompositeStatusRowCount : Nat
uniformA4ErrorBudgetCompositeStatusRowCount =
  listLength canonicalUniformA4ErrorBudgetCompositeStatusRows

uniformA4ErrorBudgetCompositeStatusRowCountIs10 :
  uniformA4ErrorBudgetCompositeStatusRowCount ≡ 10
uniformA4ErrorBudgetCompositeStatusRowCountIs10 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data UniformA4ErrorBudgetCompositePromotion : Set where

uniformA4ErrorBudgetCompositePromotionImpossibleHere :
  UniformA4ErrorBudgetCompositePromotion →
  ⊥
uniformA4ErrorBudgetCompositePromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSA4UniformErrorBudgetCompositeBoundaryRecorded : Bool
NSA4UniformErrorBudgetCompositeBoundaryRecorded =
  true

uniformCEtaLowerBoundScaleRecorded : Bool
uniformCEtaLowerBoundScaleRecorded =
  true

logWindowOutputStripErrorRecorded : Bool
logWindowOutputStripErrorRecorded =
  true

antipodalErrorRecorded : Bool
antipodalErrorRecorded =
  true

lowVorticityErrorRecorded : Bool
lowVorticityErrorRecorded =
  true

bonyPerturbationErrorRecorded : Bool
bonyPerturbationErrorRecorded =
  true

uniformA4SubtractionLedgerRecorded : Bool
uniformA4SubtractionLedgerRecorded =
  true

uniformA4FailClosedTheoremCarrierRecorded : Bool
uniformA4FailClosedTheoremCarrierRecorded =
  true

uniformCEtaLowerBoundProved : Bool
uniformCEtaLowerBoundProved =
  false

logWindowOutputStripErrorBoundProved : Bool
logWindowOutputStripErrorBoundProved =
  false

antipodalErrorBoundProved : Bool
antipodalErrorBoundProved =
  false

lowVorticityErrorBoundProved : Bool
lowVorticityErrorBoundProved =
  false

bonyPerturbationErrorBoundProved : Bool
bonyPerturbationErrorBoundProved =
  false

uniformResidualPositivityProved : Bool
uniformResidualPositivityProved =
  false

uniformA4ErrorBudgetTheoremProved : Bool
uniformA4ErrorBudgetTheoremProved =
  false

A4TheoremPromoted : Bool
A4TheoremPromoted =
  false

A6TheoremPromoted : Bool
A6TheoremPromoted =
  false

fullLocalDefectMonotonicity : Bool
fullLocalDefectMonotonicity =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

recordsBoundary :
  NSA4UniformErrorBudgetCompositeBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsCEtaLowerBoundScale :
  uniformCEtaLowerBoundScaleRecorded ≡ true
recordsCEtaLowerBoundScale =
  refl

recordsLogWindowOutputStripError :
  logWindowOutputStripErrorRecorded ≡ true
recordsLogWindowOutputStripError =
  refl

recordsAntipodalError :
  antipodalErrorRecorded ≡ true
recordsAntipodalError =
  refl

recordsLowVorticityError :
  lowVorticityErrorRecorded ≡ true
recordsLowVorticityError =
  refl

recordsBonyPerturbationError :
  bonyPerturbationErrorRecorded ≡ true
recordsBonyPerturbationError =
  refl

recordsUniformA4SubtractionLedger :
  uniformA4SubtractionLedgerRecorded ≡ true
recordsUniformA4SubtractionLedger =
  refl

recordsUniformA4FailClosedTheoremCarrier :
  uniformA4FailClosedTheoremCarrierRecorded ≡ true
recordsUniformA4FailClosedTheoremCarrier =
  refl

keepsUniformCEtaLowerBoundFalse :
  uniformCEtaLowerBoundProved ≡ false
keepsUniformCEtaLowerBoundFalse =
  refl

keepsLogWindowOutputStripErrorBoundFalse :
  logWindowOutputStripErrorBoundProved ≡ false
keepsLogWindowOutputStripErrorBoundFalse =
  refl

keepsAntipodalErrorBoundFalse :
  antipodalErrorBoundProved ≡ false
keepsAntipodalErrorBoundFalse =
  refl

keepsLowVorticityErrorBoundFalse :
  lowVorticityErrorBoundProved ≡ false
keepsLowVorticityErrorBoundFalse =
  refl

keepsBonyPerturbationErrorBoundFalse :
  bonyPerturbationErrorBoundProved ≡ false
keepsBonyPerturbationErrorBoundFalse =
  refl

keepsUniformResidualPositivityFalse :
  uniformResidualPositivityProved ≡ false
keepsUniformResidualPositivityFalse =
  refl

keepsUniformA4ErrorBudgetTheoremFalse :
  uniformA4ErrorBudgetTheoremProved ≡ false
keepsUniformA4ErrorBudgetTheoremFalse =
  refl

keepsA4TheoremPromotionFalse :
  A4TheoremPromoted ≡ false
keepsA4TheoremPromotionFalse =
  refl

keepsA6TheoremPromotionFalse :
  A6TheoremPromoted ≡ false
keepsA6TheoremPromotionFalse =
  refl

keepsFullLocalDefectMonotonicityFalse :
  fullLocalDefectMonotonicity ≡ false
keepsFullLocalDefectMonotonicityFalse =
  refl

keepsFullClayNSSolvedFalse :
  fullClayNSSolved ≡ false
keepsFullClayNSSolvedFalse =
  refl

keepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
keepsClayPromotionFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F.

organizationString : String
organizationString =
  "O: NSA4UniformErrorBudgetCompositeBoundary is worker-2's disjoint A4 boundary for the uniform c eta error budget."

requirementString : String
requirementString =
  "R: Compose output-strip preimage measure, A4 exceptional mass, Bony/Lipschitz angular pushforward, and low-vorticity routing into c eta minus log-window, antipodal, low-vorticity, and Bony perturbation errors."

codeArtifactString : String
codeArtifactString =
  "C: The module exports imported support, budget carriers, a subtraction ledger, theorem-shape target, obligations, budget lines, blockers, status rows, and false-promotion witnesses."

stateString : String
stateString =
  "S: Boundary and ledger surfaces are recorded true; the uniform lower bound, all error bounds, residual positivity, A4, A6, Clay, and terminal promotion remain false."

latticeString : String
latticeString =
  "L: output preimage c eta scale < subtract log-window/output-strip mismatch < subtract antipodal loss < subtract low-vorticity/null-output loss < subtract Bony/Lipschitz perturbation < fail-closed A4 consumer."

proposalString : String
proposalString =
  "P: Promote only after proving the child estimates quantitatively and proving the residual c eta budget stays positive uniformly across the A4 parameter window."

governanceString : String
governanceString =
  "G: This receipt consumes checked child boundary records only and introduces no A4 theorem authority or downstream Clay promotion."

gapString : String
gapString =
  "F: Missing uniform c eta lower bound, strip-preimage theorem, log-window limit, antipodal mass estimate, low/null discard bounds, Bony perturbation bound, and residual positivity proof."

------------------------------------------------------------------------
-- Canonical receipt.

record NSA4UniformErrorBudgetCompositeBoundary : Set where
  field
    O-organization :
      String
    R-requirement :
      String
    C-artifact :
      String
    S-state :
      String
    L-lattice :
      String
    P-proposal :
      String
    G-governance :
      String
    F-gap :
      String
    importedSupport :
      ImportedUniformErrorBudgetCompositeSupport
    positiveMassScale :
      UniformA4PositiveMassScaleCarrier
    logWindowOutputStripError :
      LogWindowOutputStripErrorCarrier
    antipodalError :
      AntipodalErrorCarrier
    lowVorticityError :
      LowVorticityErrorCarrier
    bonyPerturbationError :
      BonyPerturbationErrorCarrier
    subtractionLedger :
      UniformA4ErrorSubtractionLedger
    inequalityShape :
      UniformA4ErrorBudgetInequalityShape
    failClosedTheoremCarrier :
      UniformA4FailClosedTheoremCarrier
    target :
      UniformA4ErrorBudgetCompositeTarget
    obligations :
      List UniformA4ErrorBudgetCompositeObligation
    obligationsCountIs9 :
      uniformA4ErrorBudgetCompositeObligationCount ≡ 9
    budgetLines :
      List UniformA4ErrorBudgetLine
    budgetLineCountIs7 :
      uniformA4ErrorBudgetLineCount ≡ 7
    blockers :
      List UniformA4ErrorBudgetCompositeBlocker
    blockerCountIs10 :
      uniformA4ErrorBudgetCompositeBlockerCount ≡ 10
    statusRows :
      List UniformA4ErrorBudgetCompositeStatusRow
    statusRowCountIs10 :
      uniformA4ErrorBudgetCompositeStatusRowCount ≡ 10
    boundaryRecordedTrue :
      NSA4UniformErrorBudgetCompositeBoundaryRecorded ≡ true
    cEtaScaleRecordedTrue :
      uniformCEtaLowerBoundScaleRecorded ≡ true
    logWindowErrorRecordedTrue :
      logWindowOutputStripErrorRecorded ≡ true
    antipodalErrorRecordedTrue :
      antipodalErrorRecorded ≡ true
    lowVorticityErrorRecordedTrue :
      lowVorticityErrorRecorded ≡ true
    bonyPerturbationErrorRecordedTrue :
      bonyPerturbationErrorRecorded ≡ true
    subtractionLedgerRecordedTrue :
      uniformA4SubtractionLedgerRecorded ≡ true
    failClosedCarrierRecordedTrue :
      uniformA4FailClosedTheoremCarrierRecorded ≡ true
    cEtaLowerBoundStillFalse :
      uniformCEtaLowerBoundProved ≡ false
    logWindowErrorBoundStillFalse :
      logWindowOutputStripErrorBoundProved ≡ false
    antipodalErrorBoundStillFalse :
      antipodalErrorBoundProved ≡ false
    lowVorticityErrorBoundStillFalse :
      lowVorticityErrorBoundProved ≡ false
    bonyPerturbationErrorBoundStillFalse :
      bonyPerturbationErrorBoundProved ≡ false
    residualPositivityStillFalse :
      uniformResidualPositivityProved ≡ false
    uniformA4TheoremStillFalse :
      uniformA4ErrorBudgetTheoremProved ≡ false
    a4PromotionStillFalse :
      A4TheoremPromoted ≡ false
    a6PromotionStillFalse :
      A6TheoremPromoted ≡ false
    localDefectStillFalse :
      fullLocalDefectMonotonicity ≡ false
    claySolvedStillFalse :
      fullClayNSSolved ≡ false
    clayPromotionStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionStillFalse :
      terminalPromotion ≡ false

canonicalNSA4UniformErrorBudgetCompositeBoundary :
  NSA4UniformErrorBudgetCompositeBoundary
canonicalNSA4UniformErrorBudgetCompositeBoundary =
  record
    { O-organization =
        organizationString
    ; R-requirement =
        requirementString
    ; C-artifact =
        codeArtifactString
    ; S-state =
        stateString
    ; L-lattice =
        latticeString
    ; P-proposal =
        proposalString
    ; G-governance =
        governanceString
    ; F-gap =
        gapString
    ; importedSupport =
        canonicalImportedUniformErrorBudgetCompositeSupport
    ; positiveMassScale =
        canonicalUniformA4PositiveMassScaleCarrier
    ; logWindowOutputStripError =
        canonicalLogWindowOutputStripErrorCarrier
    ; antipodalError =
        canonicalAntipodalErrorCarrier
    ; lowVorticityError =
        canonicalLowVorticityErrorCarrier
    ; bonyPerturbationError =
        canonicalBonyPerturbationErrorCarrier
    ; subtractionLedger =
        canonicalUniformA4ErrorSubtractionLedger
    ; inequalityShape =
        canonicalUniformA4ErrorBudgetInequalityShape
    ; failClosedTheoremCarrier =
        canonicalUniformA4FailClosedTheoremCarrier
    ; target =
        canonicalUniformA4ErrorBudgetCompositeTarget
    ; obligations =
        canonicalUniformA4ErrorBudgetCompositeObligations
    ; obligationsCountIs9 =
        refl
    ; budgetLines =
        canonicalUniformA4ErrorBudgetLines
    ; budgetLineCountIs7 =
        refl
    ; blockers =
        canonicalUniformA4ErrorBudgetCompositeBlockers
    ; blockerCountIs10 =
        refl
    ; statusRows =
        canonicalUniformA4ErrorBudgetCompositeStatusRows
    ; statusRowCountIs10 =
        refl
    ; boundaryRecordedTrue =
        refl
    ; cEtaScaleRecordedTrue =
        refl
    ; logWindowErrorRecordedTrue =
        refl
    ; antipodalErrorRecordedTrue =
        refl
    ; lowVorticityErrorRecordedTrue =
        refl
    ; bonyPerturbationErrorRecordedTrue =
        refl
    ; subtractionLedgerRecordedTrue =
        refl
    ; failClosedCarrierRecordedTrue =
        refl
    ; cEtaLowerBoundStillFalse =
        refl
    ; logWindowErrorBoundStillFalse =
        refl
    ; antipodalErrorBoundStillFalse =
        refl
    ; lowVorticityErrorBoundStillFalse =
        refl
    ; bonyPerturbationErrorBoundStillFalse =
        refl
    ; residualPositivityStillFalse =
        refl
    ; uniformA4TheoremStillFalse =
        refl
    ; a4PromotionStillFalse =
        refl
    ; a6PromotionStillFalse =
        refl
    ; localDefectStillFalse =
        refl
    ; claySolvedStillFalse =
        refl
    ; clayPromotionStillFalse =
        refl
    ; terminalPromotionStillFalse =
        refl
    }
