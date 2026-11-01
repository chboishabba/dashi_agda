module DASHI.Physics.Closure.NSA4ExceptionalMassCompositeBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSAntipodalTubeNullMassBoundary
  as Antipodal
import DASHI.Physics.Closure.NSBonyLipschitzAngularPushforwardBoundary
  as Bony
import DASHI.Physics.Closure.NSLeiRenTianFourierOutputCouplingBoundary
  as A4
import DASHI.Physics.Closure.NSLocalizedWhitneyFramePacketEstimateBoundary
  as WhitneyPacket
import DASHI.Physics.Closure.NSLowVorticityExceptionalMassRoutingBoundary
  as LowVorticity
import DASHI.Physics.Closure.NSWhitneyCouplingInequalityBoundary
  as WhitneyCoupling

------------------------------------------------------------------------
-- NS A4 exceptional-mass composite boundary.
--
-- This module composes the child surfaces needed to route exceptional mass
-- away from the A4 Lei-Ren-Tian physical-to-Fourier output coupling:
--
--   localized Whitney packet windows
--     -> epsilon/delta log-window routing
--     -> low-vorticity exceptional discard
--     -> null-output and antipodal tube discard
--     -> Bony/Lipschitz angular pushforward stability
--     -> Whitney coupling consumer
--     -> fail-closed A4 consumer
--
-- It is a proof-contract ledger only.  It records the budget interfaces and
-- exact blockers.  It does not prove the exceptional-mass estimates, does not
-- prove Whitney coupling, does not prove A4, does not prove A6, and does not
-- promote Navier-Stokes Clay.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported boundary anchors.

antipodalTubeNullMassBoundaryReference : String
antipodalTubeNullMassBoundaryReference =
  "DASHI.Physics.Closure.NSAntipodalTubeNullMassBoundary"

lowVorticityExceptionalMassRoutingBoundaryReference : String
lowVorticityExceptionalMassRoutingBoundaryReference =
  "DASHI.Physics.Closure.NSLowVorticityExceptionalMassRoutingBoundary"

bonyLipschitzAngularPushforwardBoundaryReference : String
bonyLipschitzAngularPushforwardBoundaryReference =
  "DASHI.Physics.Closure.NSBonyLipschitzAngularPushforwardBoundary"

localizedWhitneyFramePacketBoundaryReference : String
localizedWhitneyFramePacketBoundaryReference =
  "DASHI.Physics.Closure.NSLocalizedWhitneyFramePacketEstimateBoundary"

whitneyCouplingInequalityBoundaryReference : String
whitneyCouplingInequalityBoundaryReference =
  "DASHI.Physics.Closure.NSWhitneyCouplingInequalityBoundary"

parentA4BoundaryReference : String
parentA4BoundaryReference =
  "DASHI.Physics.Closure.NSLeiRenTianFourierOutputCouplingBoundary"

record ImportedExceptionalMassCompositeSupport : Set where
  field
    antipodalSupport :
      Antipodal.ImportedAntipodalTubeSupport
    antipodalSupportIsCanonical :
      antipodalSupport ≡ Antipodal.canonicalImportedAntipodalTubeSupport
    lowVorticitySupport :
      LowVorticity.ImportedLowVorticityExceptionalMassSupport
    lowVorticitySupportIsCanonical :
      lowVorticitySupport
        ≡ LowVorticity.canonicalImportedLowVorticityExceptionalMassSupport
    bonySupport :
      Bony.ImportedBonyLipschitzAngularPushforwardSupport
    bonySupportIsCanonical :
      bonySupport
        ≡ Bony.canonicalImportedBonyLipschitzAngularPushforwardSupport
    localizedWhitneySupport :
      WhitneyPacket.ImportedLocalizedWhitneyFramePacketSupport
    localizedWhitneySupportIsCanonical :
      localizedWhitneySupport
        ≡ WhitneyPacket.canonicalImportedLocalizedWhitneyFramePacketSupport
    whitneyCouplingSupport :
      WhitneyCoupling.ImportedWhitneyCouplingSupport
    whitneyCouplingSupportIsCanonical :
      whitneyCouplingSupport
        ≡ WhitneyCoupling.canonicalImportedWhitneyCouplingSupport
    parentA4Support :
      A4.ImportedLeiRenTianFourierCouplingSupport
    parentA4SupportIsCanonical :
      parentA4Support
        ≡ A4.canonicalImportedLeiRenTianFourierCouplingSupport
    childBoundariesRecorded :
      Antipodal.NSAntipodalTubeNullMassBoundaryRecorded ≡ true
    lowVorticityBoundaryRecorded :
      LowVorticity.NSLowVorticityExceptionalMassRoutingBoundaryRecorded
        ≡ true
    bonyBoundaryRecorded :
      Bony.NSBonyLipschitzAngularPushforwardBoundaryRecorded ≡ true
    localizedWhitneyBoundaryRecorded :
      WhitneyPacket.NSLocalizedWhitneyFramePacketEstimateBoundaryRecorded
        ≡ true
    whitneyCouplingBoundaryRecorded :
      WhitneyCoupling.NSWhitneyCouplingInequalityBoundaryRecorded ≡ true

canonicalImportedExceptionalMassCompositeSupport :
  ImportedExceptionalMassCompositeSupport
canonicalImportedExceptionalMassCompositeSupport =
  record
    { antipodalSupport =
        Antipodal.canonicalImportedAntipodalTubeSupport
    ; antipodalSupportIsCanonical =
        refl
    ; lowVorticitySupport =
        LowVorticity.canonicalImportedLowVorticityExceptionalMassSupport
    ; lowVorticitySupportIsCanonical =
        refl
    ; bonySupport =
        Bony.canonicalImportedBonyLipschitzAngularPushforwardSupport
    ; bonySupportIsCanonical =
        refl
    ; localizedWhitneySupport =
        WhitneyPacket.canonicalImportedLocalizedWhitneyFramePacketSupport
    ; localizedWhitneySupportIsCanonical =
        refl
    ; whitneyCouplingSupport =
        WhitneyCoupling.canonicalImportedWhitneyCouplingSupport
    ; whitneyCouplingSupportIsCanonical =
        refl
    ; parentA4Support =
        A4.canonicalImportedLeiRenTianFourierCouplingSupport
    ; parentA4SupportIsCanonical =
        refl
    ; childBoundariesRecorded =
        refl
    ; lowVorticityBoundaryRecorded =
        refl
    ; bonyBoundaryRecorded =
        refl
    ; localizedWhitneyBoundaryRecorded =
        refl
    ; whitneyCouplingBoundaryRecorded =
        refl
    }

------------------------------------------------------------------------
-- Composite routing carriers.

data LogWindowEpsilonDeltaRoutingCarrier : Set where
  routeEpsilonTubeAndDeltaWindowThroughWhitneyAbelScale :
    Nat →
    Nat →
    WhitneyPacket.LocalParabolicWindow →
    WhitneyPacket.DyadicShellWindow →
    WhitneyPacket.ScaleWindowCompatibilityControl →
    Antipodal.AbelLogWindowAntipodalCompatibility →
    Bony.AbelWindowStabilityCarrier →
    LogWindowEpsilonDeltaRoutingCarrier

data ExceptionalMassBudgetCarrier : Set where
  lowNullAntipodalMassBudget :
    LowVorticity.LowVorticityExceptionalSetCarrier →
    LowVorticity.NullOutputCHatExclusionCarrier →
    Antipodal.AntipodalTubeCarrier →
    Antipodal.AntipodalTubeMassTarget →
    LowVorticity.AbelExceptionalMassRoutingCarrier →
    LowVorticity.LowerOrderResidualBudgetCarrier →
    ExceptionalMassBudgetCarrier

data ExceptionalMassRoutingLedger : Set where
  routeExceptionalMassBeforeA4Coupling :
    LogWindowEpsilonDeltaRoutingCarrier →
    ExceptionalMassBudgetCarrier →
    Antipodal.AntipodalTubeNullMassTarget →
    LowVorticity.LowVorticityExceptionalMassRoutingTarget →
    Bony.BonyLipschitzAngularPushforwardTarget →
    ExceptionalMassRoutingLedger

data A4FailClosedConsumerCarrier : Set where
  consumeExceptionalMassLedgerIntoRecordedA4Only :
    ExceptionalMassRoutingLedger →
    WhitneyCoupling.WhitneyCouplingInequalityTarget →
    A4.FourierOutputGreatCircleTransferTarget →
    A4FailClosedConsumerCarrier

data A4ExceptionalMassCompositeTarget : Set where
  exceptionalMassRoutedButA4RemainsFailClosed :
    ImportedExceptionalMassCompositeSupport →
    LogWindowEpsilonDeltaRoutingCarrier →
    ExceptionalMassBudgetCarrier →
    ExceptionalMassRoutingLedger →
    A4FailClosedConsumerCarrier →
    A4ExceptionalMassCompositeTarget

canonicalLogWindowEpsilonDeltaRouting :
  LogWindowEpsilonDeltaRoutingCarrier
canonicalLogWindowEpsilonDeltaRouting =
  routeEpsilonTubeAndDeltaWindowThroughWhitneyAbelScale
    (suc zero)
    (suc (suc zero))
    WhitneyPacket.canonicalLocalParabolicWindow
    WhitneyPacket.canonicalDyadicShellWindow
    WhitneyPacket.canonicalScaleWindowCompatibilityControl
    Antipodal.canonicalAbelLogWindowAntipodalCompatibility
    Bony.canonicalAbelWindowStabilityCarrier

canonicalExceptionalMassBudgetCarrier :
  ExceptionalMassBudgetCarrier
canonicalExceptionalMassBudgetCarrier =
  lowNullAntipodalMassBudget
    LowVorticity.canonicalLowVorticityExceptionalSet
    LowVorticity.canonicalNullOutputCHatExclusion
    Antipodal.canonicalAntipodalTubeCarrier
    Antipodal.canonicalAbelAntipodalTubeMassTarget
    LowVorticity.canonicalAbelExceptionalMassRouting
    LowVorticity.canonicalLowerOrderResidualBudget

canonicalExceptionalMassRoutingLedger :
  ExceptionalMassRoutingLedger
canonicalExceptionalMassRoutingLedger =
  routeExceptionalMassBeforeA4Coupling
    canonicalLogWindowEpsilonDeltaRouting
    canonicalExceptionalMassBudgetCarrier
    Antipodal.canonicalAntipodalTubeNullMassTarget
    LowVorticity.canonicalLowVorticityExceptionalMassRoutingTarget
    Bony.canonicalBonyLipschitzAngularPushforwardTarget

canonicalA4FailClosedConsumerCarrier :
  A4FailClosedConsumerCarrier
canonicalA4FailClosedConsumerCarrier =
  consumeExceptionalMassLedgerIntoRecordedA4Only
    canonicalExceptionalMassRoutingLedger
    WhitneyCoupling.canonicalWhitneyCouplingInequalityTarget
    A4.canonicalFourierOutputGreatCircleTransferTarget

canonicalA4ExceptionalMassCompositeTarget :
  A4ExceptionalMassCompositeTarget
canonicalA4ExceptionalMassCompositeTarget =
  exceptionalMassRoutedButA4RemainsFailClosed
    canonicalImportedExceptionalMassCompositeSupport
    canonicalLogWindowEpsilonDeltaRouting
    canonicalExceptionalMassBudgetCarrier
    canonicalExceptionalMassRoutingLedger
    canonicalA4FailClosedConsumerCarrier

------------------------------------------------------------------------
-- Obligations, blockers, and status rows.

data A4ExceptionalMassCompositeObligation : Set where
  importFiveExceptionalMassChildBoundaries :
    A4ExceptionalMassCompositeObligation
  recordEpsilonDeltaLogWindowRouting :
    A4ExceptionalMassCompositeObligation
  recordLowVorticityExceptionalBudget :
    A4ExceptionalMassCompositeObligation
  recordNullOutputExceptionalBudget :
    A4ExceptionalMassCompositeObligation
  recordAntipodalTubeExceptionalBudget :
    A4ExceptionalMassCompositeObligation
  composeBonyLipschitzAngularStability :
    A4ExceptionalMassCompositeObligation
  feedWhitneyCouplingTargetToA4Consumer :
    A4ExceptionalMassCompositeObligation
  keepA4ConsumerFailClosed :
    A4ExceptionalMassCompositeObligation

canonicalA4ExceptionalMassCompositeObligations :
  List A4ExceptionalMassCompositeObligation
canonicalA4ExceptionalMassCompositeObligations =
  importFiveExceptionalMassChildBoundaries
  ∷ recordEpsilonDeltaLogWindowRouting
  ∷ recordLowVorticityExceptionalBudget
  ∷ recordNullOutputExceptionalBudget
  ∷ recordAntipodalTubeExceptionalBudget
  ∷ composeBonyLipschitzAngularStability
  ∷ feedWhitneyCouplingTargetToA4Consumer
  ∷ keepA4ConsumerFailClosed
  ∷ []

a4ExceptionalMassCompositeObligationCount : Nat
a4ExceptionalMassCompositeObligationCount =
  listLength canonicalA4ExceptionalMassCompositeObligations

a4ExceptionalMassCompositeObligationCountIs8 :
  a4ExceptionalMassCompositeObligationCount ≡ 8
a4ExceptionalMassCompositeObligationCountIs8 =
  refl

data A4ExceptionalMassBudgetLine : Set where
  epsilonAntipodalTubeMassLine :
    A4ExceptionalMassBudgetLine
  deltaAbelLogWindowMismatchLine :
    A4ExceptionalMassBudgetLine
  lowVorticityPacketDiscardLine :
    A4ExceptionalMassBudgetLine
  nullOutputNormalizeSumDiscardLine :
    A4ExceptionalMassBudgetLine
  bonyLipschitzAngularPerturbationLine :
    A4ExceptionalMassBudgetLine
  whitneyPacketBoundaryLeakageLine :
    A4ExceptionalMassBudgetLine
  lowerOrderResidualAbsorptionLine :
    A4ExceptionalMassBudgetLine

canonicalA4ExceptionalMassBudgetLines :
  List A4ExceptionalMassBudgetLine
canonicalA4ExceptionalMassBudgetLines =
  epsilonAntipodalTubeMassLine
  ∷ deltaAbelLogWindowMismatchLine
  ∷ lowVorticityPacketDiscardLine
  ∷ nullOutputNormalizeSumDiscardLine
  ∷ bonyLipschitzAngularPerturbationLine
  ∷ whitneyPacketBoundaryLeakageLine
  ∷ lowerOrderResidualAbsorptionLine
  ∷ []

a4ExceptionalMassBudgetLineCount : Nat
a4ExceptionalMassBudgetLineCount =
  listLength canonicalA4ExceptionalMassBudgetLines

a4ExceptionalMassBudgetLineCountIs7 :
  a4ExceptionalMassBudgetLineCount ≡ 7
a4ExceptionalMassBudgetLineCountIs7 =
  refl

data A4ExceptionalMassCompositeBlocker : Set where
  missingEpsilonTubeMassEstimate :
    A4ExceptionalMassCompositeBlocker
  missingDeltaLogWindowLimitProof :
    A4ExceptionalMassCompositeBlocker
  missingLowVorticityExceptionalBudgetProof :
    A4ExceptionalMassCompositeBlocker
  missingNullOutputMeasureBound :
    A4ExceptionalMassCompositeBlocker
  missingBonyLipschitzPushforwardProof :
    A4ExceptionalMassCompositeBlocker
  missingWhitneyCouplingInequalityProof :
    A4ExceptionalMassCompositeBlocker
  missingA4FourierOutputCouplingProof :
    A4ExceptionalMassCompositeBlocker
  promotionRemainsClosed :
    A4ExceptionalMassCompositeBlocker

canonicalA4ExceptionalMassCompositeBlockers :
  List A4ExceptionalMassCompositeBlocker
canonicalA4ExceptionalMassCompositeBlockers =
  missingEpsilonTubeMassEstimate
  ∷ missingDeltaLogWindowLimitProof
  ∷ missingLowVorticityExceptionalBudgetProof
  ∷ missingNullOutputMeasureBound
  ∷ missingBonyLipschitzPushforwardProof
  ∷ missingWhitneyCouplingInequalityProof
  ∷ missingA4FourierOutputCouplingProof
  ∷ promotionRemainsClosed
  ∷ []

a4ExceptionalMassCompositeBlockerCount : Nat
a4ExceptionalMassCompositeBlockerCount =
  listLength canonicalA4ExceptionalMassCompositeBlockers

a4ExceptionalMassCompositeBlockerCountIs8 :
  a4ExceptionalMassCompositeBlockerCount ≡ 8
a4ExceptionalMassCompositeBlockerCountIs8 =
  refl

data A4ExceptionalMassCompositeStatusRow : Set where
  compositeBoundaryRecordedStatus :
    A4ExceptionalMassCompositeStatusRow
  importedChildSurfacesRecordedStatus :
    A4ExceptionalMassCompositeStatusRow
  epsilonDeltaLogWindowRoutingRecordedStatus :
    A4ExceptionalMassCompositeStatusRow
  lowNullAntipodalBudgetRecordedStatus :
    A4ExceptionalMassCompositeStatusRow
  bonyLipschitzStabilityConsumedStatus :
    A4ExceptionalMassCompositeStatusRow
  whitneyCouplingConsumerRecordedStatus :
    A4ExceptionalMassCompositeStatusRow
  a4FailClosedConsumerRecordedStatus :
    A4ExceptionalMassCompositeStatusRow
  blockersRemainOpenStatus :
    A4ExceptionalMassCompositeStatusRow
  allProofAndPromotionFlagsFalseStatus :
    A4ExceptionalMassCompositeStatusRow

canonicalA4ExceptionalMassCompositeStatusRows :
  List A4ExceptionalMassCompositeStatusRow
canonicalA4ExceptionalMassCompositeStatusRows =
  compositeBoundaryRecordedStatus
  ∷ importedChildSurfacesRecordedStatus
  ∷ epsilonDeltaLogWindowRoutingRecordedStatus
  ∷ lowNullAntipodalBudgetRecordedStatus
  ∷ bonyLipschitzStabilityConsumedStatus
  ∷ whitneyCouplingConsumerRecordedStatus
  ∷ a4FailClosedConsumerRecordedStatus
  ∷ blockersRemainOpenStatus
  ∷ allProofAndPromotionFlagsFalseStatus
  ∷ []

a4ExceptionalMassCompositeStatusRowCount : Nat
a4ExceptionalMassCompositeStatusRowCount =
  listLength canonicalA4ExceptionalMassCompositeStatusRows

a4ExceptionalMassCompositeStatusRowCountIs9 :
  a4ExceptionalMassCompositeStatusRowCount ≡ 9
a4ExceptionalMassCompositeStatusRowCountIs9 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data A4ExceptionalMassCompositePromotion : Set where

a4ExceptionalMassCompositePromotionImpossibleHere :
  A4ExceptionalMassCompositePromotion →
  ⊥
a4ExceptionalMassCompositePromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSA4ExceptionalMassCompositeBoundaryRecorded : Bool
NSA4ExceptionalMassCompositeBoundaryRecorded =
  true

epsilonDeltaLogWindowRoutingRecorded : Bool
epsilonDeltaLogWindowRoutingRecorded =
  true

lowNullAntipodalExceptionalMassBudgetRecorded : Bool
lowNullAntipodalExceptionalMassBudgetRecorded =
  true

exceptionalMassRoutingLedgerRecorded : Bool
exceptionalMassRoutingLedgerRecorded =
  true

A4FailClosedConsumerRecorded : Bool
A4FailClosedConsumerRecorded =
  true

epsilonTubeMassEstimateProved : Bool
epsilonTubeMassEstimateProved =
  false

deltaLogWindowLimitProved : Bool
deltaLogWindowLimitProved =
  false

lowNullAntipodalExceptionalMassBudgetProved : Bool
lowNullAntipodalExceptionalMassBudgetProved =
  false

exceptionalMassRoutingCompositeProved : Bool
exceptionalMassRoutingCompositeProved =
  false

WhitneyCouplingConsumerProved : Bool
WhitneyCouplingConsumerProved =
  false

A4LeiRenTianFourierOutputCouplingProved : Bool
A4LeiRenTianFourierOutputCouplingProved =
  false

A6TriadicCompensatedLeakageIdentityProved : Bool
A6TriadicCompensatedLeakageIdentityProved =
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

recordsCompositeBoundary :
  NSA4ExceptionalMassCompositeBoundaryRecorded ≡ true
recordsCompositeBoundary =
  refl

recordsEpsilonDeltaLogWindowRouting :
  epsilonDeltaLogWindowRoutingRecorded ≡ true
recordsEpsilonDeltaLogWindowRouting =
  refl

recordsLowNullAntipodalExceptionalMassBudget :
  lowNullAntipodalExceptionalMassBudgetRecorded ≡ true
recordsLowNullAntipodalExceptionalMassBudget =
  refl

recordsExceptionalMassRoutingLedger :
  exceptionalMassRoutingLedgerRecorded ≡ true
recordsExceptionalMassRoutingLedger =
  refl

recordsA4FailClosedConsumer :
  A4FailClosedConsumerRecorded ≡ true
recordsA4FailClosedConsumer =
  refl

keepsEpsilonTubeMassEstimateFalse :
  epsilonTubeMassEstimateProved ≡ false
keepsEpsilonTubeMassEstimateFalse =
  refl

keepsDeltaLogWindowLimitFalse :
  deltaLogWindowLimitProved ≡ false
keepsDeltaLogWindowLimitFalse =
  refl

keepsLowNullAntipodalExceptionalMassBudgetFalse :
  lowNullAntipodalExceptionalMassBudgetProved ≡ false
keepsLowNullAntipodalExceptionalMassBudgetFalse =
  refl

keepsExceptionalMassRoutingCompositeFalse :
  exceptionalMassRoutingCompositeProved ≡ false
keepsExceptionalMassRoutingCompositeFalse =
  refl

keepsWhitneyCouplingConsumerFalse :
  WhitneyCouplingConsumerProved ≡ false
keepsWhitneyCouplingConsumerFalse =
  refl

keepsA4FourierOutputCouplingFalse :
  A4LeiRenTianFourierOutputCouplingProved ≡ false
keepsA4FourierOutputCouplingFalse =
  refl

keepsA6False :
  A6TriadicCompensatedLeakageIdentityProved ≡ false
keepsA6False =
  refl

keepsClayFalse :
  clayNavierStokesPromoted ≡ false
keepsClayFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F receipt.

A4ExceptionalMassCompositeORCSLPGF : List String
A4ExceptionalMassCompositeORCSLPGF =
  "O: NSA4ExceptionalMassCompositeBoundary is worker-2's fail-closed composite for A4 exceptional mass routing."
  ∷ "R: Compose antipodal tube null mass, low-vorticity/null-output routing, Bony/Lipschitz angular pushforward, localized Whitney packets, and Whitney coupling into one A4 consumer."
  ∷ "C: Exports epsilon/delta log-window routing, low/null/antipodal exceptional mass budget, Bony stability consumer, Whitney coupling consumer, A4 fail-closed consumer, obligations, blockers, status rows, and false promotion guards."
  ∷ "S: Bookkeeping surfaces are recorded true; epsilon tube mass, delta limit, exceptional budget, Whitney consumer, A4, A6, Clay, and terminal promotion remain false."
  ∷ "L: localized Whitney windows < epsilon/delta Abel routing < low/null/antipodal discard budget < Bony/Lipschitz stability < Whitney coupling < fail-closed A4."
  ∷ "P: Prove the analytic mass estimates and window limits in the child surfaces before using this composite as theorem authority."
  ∷ "G: This module consumes only checked boundary receipts and does not modify global manifests or promote downstream theorem claims."
  ∷ "F: Exceptional mass routing, Whitney coupling, A4 Fourier-output coupling, A6 residual depletion, local defect monotonicity, and NS Clay all remain open."
  ∷ []

record NSA4ExceptionalMassCompositeBoundary : Set where
  field
    moduleName :
      String
    importedSupport :
      ImportedExceptionalMassCompositeSupport
    target :
      A4ExceptionalMassCompositeTarget
    logWindowRouting :
      LogWindowEpsilonDeltaRoutingCarrier
    exceptionalBudget :
      ExceptionalMassBudgetCarrier
    routingLedger :
      ExceptionalMassRoutingLedger
    failClosedConsumer :
      A4FailClosedConsumerCarrier
    obligations :
      List A4ExceptionalMassCompositeObligation
    budgetLines :
      List A4ExceptionalMassBudgetLine
    blockers :
      List A4ExceptionalMassCompositeBlocker
    statusRows :
      List A4ExceptionalMassCompositeStatusRow
    orcslpgf :
      List String
    boundaryRecorded :
      NSA4ExceptionalMassCompositeBoundaryRecorded ≡ true
    routingRecorded :
      epsilonDeltaLogWindowRoutingRecorded ≡ true
    budgetRecorded :
      lowNullAntipodalExceptionalMassBudgetRecorded ≡ true
    consumerRecorded :
      A4FailClosedConsumerRecorded ≡ true
    epsilonTubeEstimateStillFalse :
      epsilonTubeMassEstimateProved ≡ false
    deltaLogWindowLimitStillFalse :
      deltaLogWindowLimitProved ≡ false
    exceptionalBudgetStillFalse :
      lowNullAntipodalExceptionalMassBudgetProved ≡ false
    compositeRoutingStillFalse :
      exceptionalMassRoutingCompositeProved ≡ false
    whitneyConsumerStillFalse :
      WhitneyCouplingConsumerProved ≡ false
    a4StillFalse :
      A4LeiRenTianFourierOutputCouplingProved ≡ false
    a6StillFalse :
      A6TriadicCompensatedLeakageIdentityProved ≡ false
    clayStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalStillFalse :
      terminalPromotion ≡ false

canonicalNSA4ExceptionalMassCompositeBoundary :
  NSA4ExceptionalMassCompositeBoundary
canonicalNSA4ExceptionalMassCompositeBoundary =
  record
    { moduleName =
        "DASHI.Physics.Closure.NSA4ExceptionalMassCompositeBoundary"
    ; importedSupport =
        canonicalImportedExceptionalMassCompositeSupport
    ; target =
        canonicalA4ExceptionalMassCompositeTarget
    ; logWindowRouting =
        canonicalLogWindowEpsilonDeltaRouting
    ; exceptionalBudget =
        canonicalExceptionalMassBudgetCarrier
    ; routingLedger =
        canonicalExceptionalMassRoutingLedger
    ; failClosedConsumer =
        canonicalA4FailClosedConsumerCarrier
    ; obligations =
        canonicalA4ExceptionalMassCompositeObligations
    ; budgetLines =
        canonicalA4ExceptionalMassBudgetLines
    ; blockers =
        canonicalA4ExceptionalMassCompositeBlockers
    ; statusRows =
        canonicalA4ExceptionalMassCompositeStatusRows
    ; orcslpgf =
        A4ExceptionalMassCompositeORCSLPGF
    ; boundaryRecorded =
        refl
    ; routingRecorded =
        refl
    ; budgetRecorded =
        refl
    ; consumerRecorded =
        refl
    ; epsilonTubeEstimateStillFalse =
        refl
    ; deltaLogWindowLimitStillFalse =
        refl
    ; exceptionalBudgetStillFalse =
        refl
    ; compositeRoutingStillFalse =
        refl
    ; whitneyConsumerStillFalse =
        refl
    ; a4StillFalse =
        refl
    ; a6StillFalse =
        refl
    ; clayStillFalse =
        refl
    ; terminalStillFalse =
        refl
    }
