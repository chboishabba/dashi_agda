module DASHI.Physics.Closure.NSWhitneyCouplingInequalityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSAbelTriadicDefectMeasureConstructionBoundary
  as AbelDefect
import DASHI.Physics.Closure.NSAbelTriadicStationarityConstructionBoundary
  as Stationarity
import DASHI.Physics.Closure.NSLeiRenTianFourierOutputCouplingBoundary
  as A4
import DASHI.Physics.Closure.NSLeiRenTianGreatCircleCriterionBoundary
  as LRT
import DASHI.Physics.Closure.NSLeiRenTianOutputSupportTransferBoundary
  as OutputSupport
import DASHI.Physics.Closure.NSTriadicAngularDefectSheafLeakageBoundary
  as Sheaf

------------------------------------------------------------------------
-- NS A4 Whitney coupling inequality boundary.
--
-- Child target of NSLeiRenTianFourierOutputCouplingBoundary:
--
--   physical LRT angular richness
--     -> localized Whitney/frame packet lift
--     -> Fourier triadic output pushforward
--     -> Whitney overlap lower bound
--     -> no-angular-collapse transfer
--
-- The purpose of this module is to make the Whitney overlap inequality
-- explicit as a checked Agda proof contract.  It records the remaining
-- Sard/Fubini and null-antipodal-locus gaps separately.  It does not prove
-- A4, does not prove the output-support lift, does not prove residual
-- depletion, and does not promote Clay Navier-Stokes.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support anchors.

record ImportedWhitneyCouplingSupport : Set where
  field
    parentA4Boundary :
      A4.NSLeiRenTianFourierOutputCouplingBoundary
    parentA4BoundaryIsCanonical :
      parentA4Boundary ≡ A4.canonicalNSLeiRenTianFourierOutputCouplingBoundary
    outputSupportBoundary :
      OutputSupport.NSLeiRenTianOutputSupportTransferBoundary
    outputSupportBoundaryIsCanonical :
      outputSupportBoundary
        ≡ OutputSupport.canonicalNSLeiRenTianOutputSupportTransferBoundary
    abelDefectBoundary :
      AbelDefect.NSAbelTriadicDefectMeasureConstructionBoundary
    abelDefectBoundaryIsCanonical :
      abelDefectBoundary
        ≡ AbelDefect.canonicalNSAbelTriadicDefectMeasureConstructionBoundary
    lrtGreatCircleHitting :
      LRT.GreatCircleHittingProperty
    lrtGreatCircleHittingIsCanonical :
      lrtGreatCircleHitting ≡ LRT.canonicalGreatCircleHittingProperty
    stationarityA4Recorded :
      Stationarity.A4LRTOutputSupportTransferRecorded ≡ true
    triadicOutputCondition :
      Sheaf.LeiRenTianOutputGreatCircleCondition
    triadicOutputConditionIsCanonical :
      triadicOutputCondition ≡ Sheaf.canonicalLRTOutputCondition
    parentA4Recorded :
      A4.NSLeiRenTianFourierOutputCouplingBoundaryRecorded ≡ true
    parentWhitneyTargetRecorded :
      A4.WhitneyCouplingTargetRecorded ≡ true
    parentWhitneyProofStillFalse :
      A4.WhitneyFrameCouplingInequalityProved ≡ false
    parentOutputLiftStillFalse :
      A4.outputGreatCircleSupportLiftProved ≡ false

canonicalImportedWhitneyCouplingSupport :
  ImportedWhitneyCouplingSupport
canonicalImportedWhitneyCouplingSupport =
  record
    { parentA4Boundary =
        A4.canonicalNSLeiRenTianFourierOutputCouplingBoundary
    ; parentA4BoundaryIsCanonical =
        refl
    ; outputSupportBoundary =
        OutputSupport.canonicalNSLeiRenTianOutputSupportTransferBoundary
    ; outputSupportBoundaryIsCanonical =
        refl
    ; abelDefectBoundary =
        AbelDefect.canonicalNSAbelTriadicDefectMeasureConstructionBoundary
    ; abelDefectBoundaryIsCanonical =
        refl
    ; lrtGreatCircleHitting =
        LRT.canonicalGreatCircleHittingProperty
    ; lrtGreatCircleHittingIsCanonical =
        refl
    ; stationarityA4Recorded =
        refl
    ; triadicOutputCondition =
        Sheaf.canonicalLRTOutputCondition
    ; triadicOutputConditionIsCanonical =
        refl
    ; parentA4Recorded =
        refl
    ; parentWhitneyTargetRecorded =
        refl
    ; parentWhitneyProofStillFalse =
        refl
    ; parentOutputLiftStillFalse =
        refl
    }

------------------------------------------------------------------------
-- Whitney coupling carriers.

data PhysicalRichnessMeasureCarrier : Set where
  lrtPhysicalAngularMeasureOnHighVorticitySet :
    LRT.HighVorticityDirectionSet →
    LRT.GreatCircleHittingProperty →
    PhysicalRichnessMeasureCarrier

data LocalizedFramePacketLiftCarrier : Set where
  localizedWhitneyFramePacketLift :
    PhysicalRichnessMeasureCarrier →
    A4.LocalizedFramePacketCarrier →
    Stationarity.LRTOutputSupportTransferA4Carrier →
    LocalizedFramePacketLiftCarrier

data FourierOutputPushforwardCarrier : Set where
  cHatNormalizeSumPushforward :
    A4.FourierOutputDirectionMapCarrier →
    Sheaf.AbelTriadicInteractionDefectMeasure →
    Sheaf.OutputProjection →
    FourierOutputPushforwardCarrier

data WhitneyOverlapLowerBoundCarrier : Set where
  boundedMultiplicityWhitneyOverlapLowerBound :
    LocalizedFramePacketLiftCarrier →
    FourierOutputPushforwardCarrier →
    A4.WhitneyCouplingCarrier →
    WhitneyOverlapLowerBoundCarrier

data NoAngularCollapseFromWhitneyCarrier : Set where
  whitneyLowerBoundPreventsOutputGreatCircleAvoidance :
    WhitneyOverlapLowerBoundCarrier →
    OutputSupport.NoAngularCollapseAssumption →
    A4.NoAngularCollapseTransferCarrier →
    NoAngularCollapseFromWhitneyCarrier

data WhitneyCouplingInequalityTarget : Set where
  physicalRichnessPushesToOutputRichnessWithPositiveWhitneyOverlap :
    PhysicalRichnessMeasureCarrier →
    LocalizedFramePacketLiftCarrier →
    FourierOutputPushforwardCarrier →
    WhitneyOverlapLowerBoundCarrier →
    NoAngularCollapseFromWhitneyCarrier →
    OutputSupport.FourierTriadicOutputDirectionRichness →
    WhitneyCouplingInequalityTarget

canonicalPhysicalRichnessMeasureCarrier :
  PhysicalRichnessMeasureCarrier
canonicalPhysicalRichnessMeasureCarrier =
  lrtPhysicalAngularMeasureOnHighVorticitySet
    LRT.canonicalHighVorticityDirectionSet
    LRT.canonicalGreatCircleHittingProperty

canonicalLocalizedFramePacketLiftCarrier :
  LocalizedFramePacketLiftCarrier
canonicalLocalizedFramePacketLiftCarrier =
  localizedWhitneyFramePacketLift
    canonicalPhysicalRichnessMeasureCarrier
    A4.canonicalLocalizedFramePacketCarrier
    Stationarity.canonicalA4LRTOutputSupportTransfer

canonicalFourierOutputPushforwardCarrier :
  FourierOutputPushforwardCarrier
canonicalFourierOutputPushforwardCarrier =
  cHatNormalizeSumPushforward
    A4.canonicalFourierOutputDirectionMapCarrier
    Sheaf.canonicalAbelTriadicMeasure
    Sheaf.canonicalOutputProjection

canonicalWhitneyOverlapLowerBoundCarrier :
  WhitneyOverlapLowerBoundCarrier
canonicalWhitneyOverlapLowerBoundCarrier =
  boundedMultiplicityWhitneyOverlapLowerBound
    canonicalLocalizedFramePacketLiftCarrier
    canonicalFourierOutputPushforwardCarrier
    A4.canonicalWhitneyCouplingCarrier

canonicalNoAngularCollapseFromWhitneyCarrier :
  NoAngularCollapseFromWhitneyCarrier
canonicalNoAngularCollapseFromWhitneyCarrier =
  whitneyLowerBoundPreventsOutputGreatCircleAvoidance
    canonicalWhitneyOverlapLowerBoundCarrier
    OutputSupport.canonicalNoAngularCollapseAssumption
    A4.canonicalNoAngularCollapseTransferCarrier

canonicalWhitneyCouplingInequalityTarget :
  WhitneyCouplingInequalityTarget
canonicalWhitneyCouplingInequalityTarget =
  physicalRichnessPushesToOutputRichnessWithPositiveWhitneyOverlap
    canonicalPhysicalRichnessMeasureCarrier
    canonicalLocalizedFramePacketLiftCarrier
    canonicalFourierOutputPushforwardCarrier
    canonicalWhitneyOverlapLowerBoundCarrier
    canonicalNoAngularCollapseFromWhitneyCarrier
    OutputSupport.canonicalFourierTriadicOutputDirectionRichness

------------------------------------------------------------------------
-- Exact proof obligations.

data WhitneyCouplingObligation : Set where
  constructPhysicalRichnessMeasure :
    WhitneyCouplingObligation
  liftMeasureToLocalizedWhitneyFramePackets :
    WhitneyCouplingObligation
  defineFourierOutputPushforwardByCHatNormalizeSum :
    WhitneyCouplingObligation
  removeAntipodalNullTriadsFromPushforward :
    WhitneyCouplingObligation
  proveBoundedWhitneyOverlapMultiplicity :
    WhitneyCouplingObligation
  provePositiveOverlapLowerBoundForEveryGreatCircleTest :
    WhitneyCouplingObligation
  pullBackOutputAvoidanceToPhysicalDoubleConeAvoidance :
    WhitneyCouplingObligation
  dischargeCutoffFrameAndPacketBoundaryErrors :
    WhitneyCouplingObligation
  integrateWithA4OutputSupportTransfer :
    WhitneyCouplingObligation

canonicalWhitneyCouplingObligations :
  List WhitneyCouplingObligation
canonicalWhitneyCouplingObligations =
  constructPhysicalRichnessMeasure
  ∷ liftMeasureToLocalizedWhitneyFramePackets
  ∷ defineFourierOutputPushforwardByCHatNormalizeSum
  ∷ removeAntipodalNullTriadsFromPushforward
  ∷ proveBoundedWhitneyOverlapMultiplicity
  ∷ provePositiveOverlapLowerBoundForEveryGreatCircleTest
  ∷ pullBackOutputAvoidanceToPhysicalDoubleConeAvoidance
  ∷ dischargeCutoffFrameAndPacketBoundaryErrors
  ∷ integrateWithA4OutputSupportTransfer
  ∷ []

whitneyCouplingObligationCount : Nat
whitneyCouplingObligationCount =
  listLength canonicalWhitneyCouplingObligations

whitneyCouplingObligationCountIs9 :
  whitneyCouplingObligationCount ≡ 9
whitneyCouplingObligationCountIs9 =
  refl

data WhitneyCouplingErrorTerm : Set where
  physicalAngularMassLocalizationLoss :
    WhitneyCouplingErrorTerm
  whitneyPacketBoundaryLoss :
    WhitneyCouplingErrorTerm
  localFrameVariationLoss :
    WhitneyCouplingErrorTerm
  cHatAntipodalDegeneracyLoss :
    WhitneyCouplingErrorTerm
  outputMapJacobianRegularValueLoss :
    WhitneyCouplingErrorTerm
  finiteOverlapMultiplicityLoss :
    WhitneyCouplingErrorTerm
  cutoffCommutatorLoss :
    WhitneyCouplingErrorTerm
  AbelWindowMismatchLoss :
    WhitneyCouplingErrorTerm

canonicalWhitneyCouplingErrorTerms :
  List WhitneyCouplingErrorTerm
canonicalWhitneyCouplingErrorTerms =
  physicalAngularMassLocalizationLoss
  ∷ whitneyPacketBoundaryLoss
  ∷ localFrameVariationLoss
  ∷ cHatAntipodalDegeneracyLoss
  ∷ outputMapJacobianRegularValueLoss
  ∷ finiteOverlapMultiplicityLoss
  ∷ cutoffCommutatorLoss
  ∷ AbelWindowMismatchLoss
  ∷ []

whitneyCouplingErrorTermCount : Nat
whitneyCouplingErrorTermCount =
  listLength canonicalWhitneyCouplingErrorTerms

whitneyCouplingErrorTermCountIs8 :
  whitneyCouplingErrorTermCount ≡ 8
whitneyCouplingErrorTermCountIs8 =
  refl

data SardFubiniGap : Set where
  proveAntipodalLocusHasZeroAbelMass :
    SardFubiniGap
  proveSardRegularValueSlicingForCHatMap :
    SardFubiniGap
  proveFubiniDisintegrationAcrossWhitneyPackets :
    SardFubiniGap
  proveJacobianLowerBoundAwayFromDegenerateTriads :
    SardFubiniGap
  proveQualitativeLRTSupportSufficesWithoutDensityEquivalence :
    SardFubiniGap
  proveBonyLipschitzControlOfAngularPushforward :
    SardFubiniGap
  proveNullAndLowVorticityExceptionalSetsDoNotCarryDefectMass :
    SardFubiniGap

canonicalSardFubiniGaps :
  List SardFubiniGap
canonicalSardFubiniGaps =
  proveAntipodalLocusHasZeroAbelMass
  ∷ proveSardRegularValueSlicingForCHatMap
  ∷ proveFubiniDisintegrationAcrossWhitneyPackets
  ∷ proveJacobianLowerBoundAwayFromDegenerateTriads
  ∷ proveQualitativeLRTSupportSufficesWithoutDensityEquivalence
  ∷ proveBonyLipschitzControlOfAngularPushforward
  ∷ proveNullAndLowVorticityExceptionalSetsDoNotCarryDefectMass
  ∷ []

sardFubiniGapCount : Nat
sardFubiniGapCount =
  listLength canonicalSardFubiniGaps

sardFubiniGapCountIs7 :
  sardFubiniGapCount ≡ 7
sardFubiniGapCountIs7 =
  refl

data WhitneyCouplingStatusRow : Set where
  childBoundaryRecordedStatus :
    WhitneyCouplingStatusRow
  physicalRichnessMeasureRecordedStatus :
    WhitneyCouplingStatusRow
  localizedFramePacketLiftRecordedStatus :
    WhitneyCouplingStatusRow
  FourierOutputPushforwardRecordedStatus :
    WhitneyCouplingStatusRow
  WhitneyOverlapLowerBoundRecordedStatus :
    WhitneyCouplingStatusRow
  noAngularCollapseTransferRecordedStatus :
    WhitneyCouplingStatusRow
  SardFubiniGapsRemainOpenStatus :
    WhitneyCouplingStatusRow
  allProofAndPromotionFlagsRemainFalseStatus :
    WhitneyCouplingStatusRow

canonicalWhitneyCouplingStatusRows :
  List WhitneyCouplingStatusRow
canonicalWhitneyCouplingStatusRows =
  childBoundaryRecordedStatus
  ∷ physicalRichnessMeasureRecordedStatus
  ∷ localizedFramePacketLiftRecordedStatus
  ∷ FourierOutputPushforwardRecordedStatus
  ∷ WhitneyOverlapLowerBoundRecordedStatus
  ∷ noAngularCollapseTransferRecordedStatus
  ∷ SardFubiniGapsRemainOpenStatus
  ∷ allProofAndPromotionFlagsRemainFalseStatus
  ∷ []

whitneyCouplingStatusRowCount : Nat
whitneyCouplingStatusRowCount =
  listLength canonicalWhitneyCouplingStatusRows

whitneyCouplingStatusRowCountIs8 :
  whitneyCouplingStatusRowCount ≡ 8
whitneyCouplingStatusRowCountIs8 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data WhitneyCouplingPromotion : Set where

whitneyCouplingPromotionImpossibleHere :
  WhitneyCouplingPromotion →
  ⊥
whitneyCouplingPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSWhitneyCouplingInequalityBoundaryRecorded : Bool
NSWhitneyCouplingInequalityBoundaryRecorded =
  true

physicalRichnessMeasureRecorded : Bool
physicalRichnessMeasureRecorded =
  true

localizedFramePacketLiftRecorded : Bool
localizedFramePacketLiftRecorded =
  true

FourierOutputPushforwardRecorded : Bool
FourierOutputPushforwardRecorded =
  true

WhitneyOverlapLowerBoundTargetRecorded : Bool
WhitneyOverlapLowerBoundTargetRecorded =
  true

noAngularCollapseFromWhitneyRecorded : Bool
noAngularCollapseFromWhitneyRecorded =
  true

SardFubiniGapListRecorded : Bool
SardFubiniGapListRecorded =
  true

physicalRichnessMeasureConstructed : Bool
physicalRichnessMeasureConstructed =
  false

localizedFramePacketLiftProved : Bool
localizedFramePacketLiftProved =
  false

FourierOutputPushforwardProved : Bool
FourierOutputPushforwardProved =
  false

WhitneyOverlapLowerBoundProved : Bool
WhitneyOverlapLowerBoundProved =
  false

SardFubiniStepProved : Bool
SardFubiniStepProved =
  false

noAngularCollapseFromWhitneyProved : Bool
noAngularCollapseFromWhitneyProved =
  false

A4WhitneyCouplingInequalityProved : Bool
A4WhitneyCouplingInequalityProved =
  false

A4LeiRenTianFourierOutputCouplingProved : Bool
A4LeiRenTianFourierOutputCouplingProved =
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
  NSWhitneyCouplingInequalityBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsPhysicalRichnessMeasure :
  physicalRichnessMeasureRecorded ≡ true
recordsPhysicalRichnessMeasure =
  refl

recordsLocalizedFramePacketLift :
  localizedFramePacketLiftRecorded ≡ true
recordsLocalizedFramePacketLift =
  refl

recordsFourierOutputPushforward :
  FourierOutputPushforwardRecorded ≡ true
recordsFourierOutputPushforward =
  refl

recordsWhitneyOverlapLowerBoundTarget :
  WhitneyOverlapLowerBoundTargetRecorded ≡ true
recordsWhitneyOverlapLowerBoundTarget =
  refl

recordsNoAngularCollapseFromWhitney :
  noAngularCollapseFromWhitneyRecorded ≡ true
recordsNoAngularCollapseFromWhitney =
  refl

recordsSardFubiniGapList :
  SardFubiniGapListRecorded ≡ true
recordsSardFubiniGapList =
  refl

keepsPhysicalRichnessMeasureConstructedFalse :
  physicalRichnessMeasureConstructed ≡ false
keepsPhysicalRichnessMeasureConstructedFalse =
  refl

keepsLocalizedFramePacketLiftFalse :
  localizedFramePacketLiftProved ≡ false
keepsLocalizedFramePacketLiftFalse =
  refl

keepsFourierOutputPushforwardFalse :
  FourierOutputPushforwardProved ≡ false
keepsFourierOutputPushforwardFalse =
  refl

keepsWhitneyOverlapLowerBoundFalse :
  WhitneyOverlapLowerBoundProved ≡ false
keepsWhitneyOverlapLowerBoundFalse =
  refl

keepsSardFubiniStepFalse :
  SardFubiniStepProved ≡ false
keepsSardFubiniStepFalse =
  refl

keepsNoAngularCollapseFromWhitneyFalse :
  noAngularCollapseFromWhitneyProved ≡ false
keepsNoAngularCollapseFromWhitneyFalse =
  refl

keepsA4WhitneyCouplingFalse :
  A4WhitneyCouplingInequalityProved ≡ false
keepsA4WhitneyCouplingFalse =
  refl

keepsA4FourierOutputCouplingFalse :
  A4LeiRenTianFourierOutputCouplingProved ≡ false
keepsA4FourierOutputCouplingFalse =
  refl

keepsClaySolvedFalse :
  fullClayNSSolved ≡ false
keepsClaySolvedFalse =
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
  "O: Worker-4 child boundary isolates the A4 Whitney coupling inequality between physical LRT angular measure and Fourier output-direction pushforward."

requirementString : String
requirementString =
  "R: Record physical richness, localized frame packet lift, c-hat Fourier pushforward, Whitney overlap lower bound, no-collapse transfer, and remaining Sard/Fubini gaps."

codeArtifactString : String
codeArtifactString =
  "C: NSWhitneyCouplingInequalityBoundary imports A4 parent, LRT criterion, Abel defect construction, stationarity, output support, and triadic sheaf carriers."

stateString : String
stateString =
  "S: Boundary is checked and fail-closed; the Whitney overlap inequality, Sard/Fubini slicing, and output-support lift remain unproved."

latticeString : String
latticeString =
  "L: recorded child target -> Whitney overlap lower bound -> no-angular-collapse transfer -> A4 Fourier output coupling -> A5 bias support."

proposalString : String
proposalString =
  "P: Promote only after proving the overlap lower bound, null-antipodal exclusion, Sard/Fubini slicing, and Bony-Lipschitz angular pushforward control."

governanceString : String
governanceString =
  "G: Governance remains fail-closed: recorded surfaces are true, while all theorem, A4, Clay, and terminal promotion flags are false."

gapString : String
gapString =
  "F: Remaining gaps are the seven Sard/Fubini obligations plus proof of the positive Whitney overlap lower bound and integration into A4."

------------------------------------------------------------------------
-- Canonical receipt.

record NSWhitneyCouplingInequalityBoundary : Set where
  constructor nsWhitneyCouplingInequalityBoundary
  field
    importedSupport :
      ImportedWhitneyCouplingSupport
    importedSupportIsCanonical :
      importedSupport ≡ canonicalImportedWhitneyCouplingSupport
    physicalRichness :
      PhysicalRichnessMeasureCarrier
    physicalRichnessIsCanonical :
      physicalRichness ≡ canonicalPhysicalRichnessMeasureCarrier
    localizedFramePacketLift :
      LocalizedFramePacketLiftCarrier
    localizedFramePacketLiftIsCanonical :
      localizedFramePacketLift ≡ canonicalLocalizedFramePacketLiftCarrier
    fourierOutputPushforward :
      FourierOutputPushforwardCarrier
    fourierOutputPushforwardIsCanonical :
      fourierOutputPushforward ≡ canonicalFourierOutputPushforwardCarrier
    whitneyOverlapLowerBound :
      WhitneyOverlapLowerBoundCarrier
    whitneyOverlapLowerBoundIsCanonical :
      whitneyOverlapLowerBound ≡ canonicalWhitneyOverlapLowerBoundCarrier
    noAngularCollapseFromWhitney :
      NoAngularCollapseFromWhitneyCarrier
    noAngularCollapseFromWhitneyIsCanonical :
      noAngularCollapseFromWhitney ≡ canonicalNoAngularCollapseFromWhitneyCarrier
    target :
      WhitneyCouplingInequalityTarget
    targetIsCanonical :
      target ≡ canonicalWhitneyCouplingInequalityTarget
    obligations :
      List WhitneyCouplingObligation
    obligationsAreCanonical :
      obligations ≡ canonicalWhitneyCouplingObligations
    errorTerms :
      List WhitneyCouplingErrorTerm
    errorTermsAreCanonical :
      errorTerms ≡ canonicalWhitneyCouplingErrorTerms
    sardFubiniGaps :
      List SardFubiniGap
    sardFubiniGapsAreCanonical :
      sardFubiniGaps ≡ canonicalSardFubiniGaps
    statuses :
      List WhitneyCouplingStatusRow
    statusesAreCanonical :
      statuses ≡ canonicalWhitneyCouplingStatusRows
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ gapString
    boundaryRecorded :
      NSWhitneyCouplingInequalityBoundaryRecorded ≡ true
    physicalMeasureRecorded :
      physicalRichnessMeasureRecorded ≡ true
    framePacketLiftRecorded :
      localizedFramePacketLiftRecorded ≡ true
    outputPushforwardRecorded :
      FourierOutputPushforwardRecorded ≡ true
    overlapTargetRecorded :
      WhitneyOverlapLowerBoundTargetRecorded ≡ true
    noCollapseRecorded :
      noAngularCollapseFromWhitneyRecorded ≡ true
    gapListRecorded :
      SardFubiniGapListRecorded ≡ true
    physicalMeasureConstructedFalse :
      physicalRichnessMeasureConstructed ≡ false
    framePacketLiftFalse :
      localizedFramePacketLiftProved ≡ false
    outputPushforwardFalse :
      FourierOutputPushforwardProved ≡ false
    overlapLowerBoundFalse :
      WhitneyOverlapLowerBoundProved ≡ false
    sardFubiniFalse :
      SardFubiniStepProved ≡ false
    noCollapseProofFalse :
      noAngularCollapseFromWhitneyProved ≡ false
    A4WhitneyCouplingFalse :
      A4WhitneyCouplingInequalityProved ≡ false
    A4FourierCouplingFalse :
      A4LeiRenTianFourierOutputCouplingProved ≡ false
    claySolvedFalse :
      fullClayNSSolved ≡ false
    clayPromotionFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

open NSWhitneyCouplingInequalityBoundary public

canonicalNSWhitneyCouplingInequalityBoundary :
  NSWhitneyCouplingInequalityBoundary
canonicalNSWhitneyCouplingInequalityBoundary =
  nsWhitneyCouplingInequalityBoundary
    canonicalImportedWhitneyCouplingSupport
    refl
    canonicalPhysicalRichnessMeasureCarrier
    refl
    canonicalLocalizedFramePacketLiftCarrier
    refl
    canonicalFourierOutputPushforwardCarrier
    refl
    canonicalWhitneyOverlapLowerBoundCarrier
    refl
    canonicalNoAngularCollapseFromWhitneyCarrier
    refl
    canonicalWhitneyCouplingInequalityTarget
    refl
    canonicalWhitneyCouplingObligations
    refl
    canonicalWhitneyCouplingErrorTerms
    refl
    canonicalSardFubiniGaps
    refl
    canonicalWhitneyCouplingStatusRows
    refl
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
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
