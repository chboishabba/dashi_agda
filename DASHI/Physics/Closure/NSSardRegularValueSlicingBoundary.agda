module DASHI.Physics.Closure.NSSardRegularValueSlicingBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSFourierOutputPushforwardBoundary
  as Pushforward
import DASHI.Physics.Closure.NSLocalizedWhitneyFramePacketEstimateBoundary
  as Packet
import DASHI.Physics.Closure.NSWhitneyCouplingInequalityBoundary
  as Whitney

------------------------------------------------------------------------
-- NS A4 Sard regular-value slicing boundary.
--
-- Child target of the Fourier-output pushforward and Whitney-coupling
-- surfaces:
--
--   Phi(theta1,theta2) = normalize(theta1 + theta2)
--
-- on non-antipodal angular pairs.  The analytic sublemma to prove is that
-- regular output values of Phi admit controlled slices through localized
-- Whitney angular packets, with the critical values and antipodal
-- degeneracy discarded as null sets, and with the resulting slices
-- compatible with output great-circle strip tests.
--
-- This module records the proof contract only.  It does not provide a
-- smooth chart atlas, does not prove derivative rank, does not prove Sard,
-- does not prove strip slicing, does not complete A4, and does not promote
-- Navier-Stokes Clay.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support anchors.

record ImportedSardRegularValueSlicingSupport : Set where
  field
    fourierOutputPushforwardBoundary :
      Pushforward.FourierOutputPushforwardTarget
    fourierOutputPushforwardBoundaryIsCanonical :
      fourierOutputPushforwardBoundary
        ≡ Pushforward.canonicalFourierOutputPushforwardTarget
    phiMap :
      Pushforward.FourierOutputPhiMap
    phiMapIsCanonical :
      phiMap ≡ Pushforward.canonicalFourierOutputPhiMap
    antipodalExclusion :
      Pushforward.AntipodalExclusionCarrier
    antipodalExclusionIsCanonical :
      antipodalExclusion ≡ Pushforward.canonicalAntipodalExclusionCarrier
    offAntipodalLipschitzControl :
      Pushforward.OffAntipodalLipschitzControl
    offAntipodalLipschitzControlIsCanonical :
      offAntipodalLipschitzControl
        ≡ Pushforward.canonicalOffAntipodalLipschitzControl
    sardFubiniParentObligation :
      Pushforward.SardFubiniNullSetObligation
    sardFubiniParentObligationIsCanonical :
      sardFubiniParentObligation
        ≡ Pushforward.canonicalSardFubiniNullSetObligation
    localizedWhitneyPacketTarget :
      Packet.LocalizedWhitneyFramePacketEstimateTarget
    localizedWhitneyPacketTargetIsCanonical :
      localizedWhitneyPacketTarget
        ≡ Packet.canonicalLocalizedWhitneyFramePacketEstimateTarget
    whitneyCouplingTarget :
      Whitney.WhitneyCouplingInequalityTarget
    whitneyCouplingTargetIsCanonical :
      whitneyCouplingTarget ≡ Whitney.canonicalWhitneyCouplingInequalityTarget
    parentSardStillFalse :
      Pushforward.SardFubiniAntipodalNullSetProved ≡ false
    parentPushforwardStillFalse :
      Pushforward.FourierOutputPushforwardTheoremProved ≡ false
    parentWhitneySardStillFalse :
      Whitney.SardFubiniStepProved ≡ false
    parentWhitneyCouplingStillFalse :
      Whitney.A4WhitneyCouplingInequalityProved ≡ false

canonicalImportedSardRegularValueSlicingSupport :
  ImportedSardRegularValueSlicingSupport
canonicalImportedSardRegularValueSlicingSupport =
  record
    { fourierOutputPushforwardBoundary =
        Pushforward.canonicalFourierOutputPushforwardTarget
    ; fourierOutputPushforwardBoundaryIsCanonical =
        refl
    ; phiMap =
        Pushforward.canonicalFourierOutputPhiMap
    ; phiMapIsCanonical =
        refl
    ; antipodalExclusion =
        Pushforward.canonicalAntipodalExclusionCarrier
    ; antipodalExclusionIsCanonical =
        refl
    ; offAntipodalLipschitzControl =
        Pushforward.canonicalOffAntipodalLipschitzControl
    ; offAntipodalLipschitzControlIsCanonical =
        refl
    ; sardFubiniParentObligation =
        Pushforward.canonicalSardFubiniNullSetObligation
    ; sardFubiniParentObligationIsCanonical =
        refl
    ; localizedWhitneyPacketTarget =
        Packet.canonicalLocalizedWhitneyFramePacketEstimateTarget
    ; localizedWhitneyPacketTargetIsCanonical =
        refl
    ; whitneyCouplingTarget =
        Whitney.canonicalWhitneyCouplingInequalityTarget
    ; whitneyCouplingTargetIsCanonical =
        refl
    ; parentSardStillFalse =
        refl
    ; parentPushforwardStillFalse =
        refl
    ; parentWhitneySardStillFalse =
        refl
    ; parentWhitneyCouplingStillFalse =
        refl
    }

------------------------------------------------------------------------
-- Sard/slicing carriers.

data SmoothChartAtlasCarrier : Set where
  smoothChartsForNonAntipodalAngularPairDomain :
    Pushforward.InputAngularPairCarrier →
    Pushforward.AntipodalExclusionCarrier →
    SmoothChartAtlasCarrier

data PhiDifferentialCarrier : Set where
  derivativeOfNormalizeSumInLocalCharts :
    SmoothChartAtlasCarrier →
    Pushforward.FourierOutputPhiMap →
    PhiDifferentialCarrier

data RegularValueCarrier : Set where
  outputDirectionRegularForPhiAwayFromAntipodalLocus :
    PhiDifferentialCarrier →
    Pushforward.OffAntipodalLipschitzControl →
    RegularValueCarrier

data CriticalSetAwayFromAntipodalCarrier : Set where
  rankDropSetForDPhiInNonAntipodalDomain :
    PhiDifferentialCarrier →
    Pushforward.AntipodalExclusionCarrier →
    CriticalSetAwayFromAntipodalCarrier

data SardExceptionalSetCarrier : Set where
  criticalValuesOfPhiHaveSphericalMeasureZero :
    CriticalSetAwayFromAntipodalCarrier →
    RegularValueCarrier →
    SardExceptionalSetCarrier

data WhitneyPacketSliceCarrier : Set where
  preimageSliceThroughLocalizedWhitneyAngularPackets :
    RegularValueCarrier →
    Packet.LocalizedWhitneyFramePacketEstimateTarget →
    Whitney.LocalizedFramePacketLiftCarrier →
    WhitneyPacketSliceCarrier

data OutputGreatCircleStripCarrier : Set where
  greatCircleStripTestForRegularOutputDirection :
    RegularValueCarrier →
    Whitney.FourierOutputPushforwardCarrier →
    OutputGreatCircleStripCarrier

data StripSlicingEstimateCarrier : Set where
  PhiPreimageOfOutputStripControlledByWhitneyPacketSlices :
    WhitneyPacketSliceCarrier →
    OutputGreatCircleStripCarrier →
    Whitney.WhitneyOverlapLowerBoundCarrier →
    StripSlicingEstimateCarrier

data SardRegularValueSlicingTarget : Set where
  regularValueSlicesFeedWhitneyOutputStripCoupling :
    SmoothChartAtlasCarrier →
    PhiDifferentialCarrier →
    RegularValueCarrier →
    CriticalSetAwayFromAntipodalCarrier →
    SardExceptionalSetCarrier →
    WhitneyPacketSliceCarrier →
    OutputGreatCircleStripCarrier →
    StripSlicingEstimateCarrier →
    Whitney.WhitneyCouplingInequalityTarget →
    SardRegularValueSlicingTarget

canonicalSmoothChartAtlasCarrier :
  SmoothChartAtlasCarrier
canonicalSmoothChartAtlasCarrier =
  smoothChartsForNonAntipodalAngularPairDomain
    Pushforward.canonicalInputAngularPairCarrier
    Pushforward.canonicalAntipodalExclusionCarrier

canonicalPhiDifferentialCarrier :
  PhiDifferentialCarrier
canonicalPhiDifferentialCarrier =
  derivativeOfNormalizeSumInLocalCharts
    canonicalSmoothChartAtlasCarrier
    Pushforward.canonicalFourierOutputPhiMap

canonicalRegularValueCarrier :
  RegularValueCarrier
canonicalRegularValueCarrier =
  outputDirectionRegularForPhiAwayFromAntipodalLocus
    canonicalPhiDifferentialCarrier
    Pushforward.canonicalOffAntipodalLipschitzControl

canonicalCriticalSetAwayFromAntipodalCarrier :
  CriticalSetAwayFromAntipodalCarrier
canonicalCriticalSetAwayFromAntipodalCarrier =
  rankDropSetForDPhiInNonAntipodalDomain
    canonicalPhiDifferentialCarrier
    Pushforward.canonicalAntipodalExclusionCarrier

canonicalSardExceptionalSetCarrier :
  SardExceptionalSetCarrier
canonicalSardExceptionalSetCarrier =
  criticalValuesOfPhiHaveSphericalMeasureZero
    canonicalCriticalSetAwayFromAntipodalCarrier
    canonicalRegularValueCarrier

canonicalWhitneyPacketSliceCarrier :
  WhitneyPacketSliceCarrier
canonicalWhitneyPacketSliceCarrier =
  preimageSliceThroughLocalizedWhitneyAngularPackets
    canonicalRegularValueCarrier
    Packet.canonicalLocalizedWhitneyFramePacketEstimateTarget
    Whitney.canonicalLocalizedFramePacketLiftCarrier

canonicalOutputGreatCircleStripCarrier :
  OutputGreatCircleStripCarrier
canonicalOutputGreatCircleStripCarrier =
  greatCircleStripTestForRegularOutputDirection
    canonicalRegularValueCarrier
    Whitney.canonicalFourierOutputPushforwardCarrier

canonicalStripSlicingEstimateCarrier :
  StripSlicingEstimateCarrier
canonicalStripSlicingEstimateCarrier =
  PhiPreimageOfOutputStripControlledByWhitneyPacketSlices
    canonicalWhitneyPacketSliceCarrier
    canonicalOutputGreatCircleStripCarrier
    Whitney.canonicalWhitneyOverlapLowerBoundCarrier

canonicalSardRegularValueSlicingTarget :
  SardRegularValueSlicingTarget
canonicalSardRegularValueSlicingTarget =
  regularValueSlicesFeedWhitneyOutputStripCoupling
    canonicalSmoothChartAtlasCarrier
    canonicalPhiDifferentialCarrier
    canonicalRegularValueCarrier
    canonicalCriticalSetAwayFromAntipodalCarrier
    canonicalSardExceptionalSetCarrier
    canonicalWhitneyPacketSliceCarrier
    canonicalOutputGreatCircleStripCarrier
    canonicalStripSlicingEstimateCarrier
    Whitney.canonicalWhitneyCouplingInequalityTarget

------------------------------------------------------------------------
-- Exact obligations and blockers.

data SardRegularValueSlicingObligation : Set where
  constructSmoothAtlasOnS2ProductMinusAntipodalDiagonal :
    SardRegularValueSlicingObligation
  expressPhiNormalizeSumInCharts :
    SardRegularValueSlicingObligation
  computeDerivativeOfNormalizeSum :
    SardRegularValueSlicingObligation
  characterizeCriticalSetAwayFromAntipodalLocus :
    SardRegularValueSlicingObligation
  proveDerivativeRankAtRegularOutputValues :
    SardRegularValueSlicingObligation
  applySardToCriticalValuesOfPhi :
    SardRegularValueSlicingObligation
  disintegrateRegularPreimagesAcrossWhitneyPackets :
    SardRegularValueSlicingObligation
  estimateOutputGreatCircleStripSlices :
    SardRegularValueSlicingObligation
  feedSliceEstimateIntoWhitneyCoupling :
    SardRegularValueSlicingObligation

canonicalSardRegularValueSlicingObligations :
  List SardRegularValueSlicingObligation
canonicalSardRegularValueSlicingObligations =
  constructSmoothAtlasOnS2ProductMinusAntipodalDiagonal
  ∷ expressPhiNormalizeSumInCharts
  ∷ computeDerivativeOfNormalizeSum
  ∷ characterizeCriticalSetAwayFromAntipodalLocus
  ∷ proveDerivativeRankAtRegularOutputValues
  ∷ applySardToCriticalValuesOfPhi
  ∷ disintegrateRegularPreimagesAcrossWhitneyPackets
  ∷ estimateOutputGreatCircleStripSlices
  ∷ feedSliceEstimateIntoWhitneyCoupling
  ∷ []

sardRegularValueSlicingObligationCount : Nat
sardRegularValueSlicingObligationCount =
  listLength canonicalSardRegularValueSlicingObligations

sardRegularValueSlicingObligationCountIs9 :
  sardRegularValueSlicingObligationCount ≡ 9
sardRegularValueSlicingObligationCountIs9 =
  refl

data SardRegularValueSlicingBlocker : Set where
  missingSmoothChartAtlas :
    SardRegularValueSlicingBlocker
  missingDerivativeRankProof :
    SardRegularValueSlicingBlocker
  missingCriticalValueNullSetProof :
    SardRegularValueSlicingBlocker
  missingStripSlicingEstimate :
    SardRegularValueSlicingBlocker
  missingWhitneyPacketDisintegration :
    SardRegularValueSlicingBlocker
  missingCompatibilityWithOutputGreatCircleStrips :
    SardRegularValueSlicingBlocker
  missingA4Completion :
    SardRegularValueSlicingBlocker
  missingClayPromotion :
    SardRegularValueSlicingBlocker

canonicalSardRegularValueSlicingBlockers :
  List SardRegularValueSlicingBlocker
canonicalSardRegularValueSlicingBlockers =
  missingSmoothChartAtlas
  ∷ missingDerivativeRankProof
  ∷ missingCriticalValueNullSetProof
  ∷ missingStripSlicingEstimate
  ∷ missingWhitneyPacketDisintegration
  ∷ missingCompatibilityWithOutputGreatCircleStrips
  ∷ missingA4Completion
  ∷ missingClayPromotion
  ∷ []

sardRegularValueSlicingBlockerCount : Nat
sardRegularValueSlicingBlockerCount =
  listLength canonicalSardRegularValueSlicingBlockers

sardRegularValueSlicingBlockerCountIs8 :
  sardRegularValueSlicingBlockerCount ≡ 8
sardRegularValueSlicingBlockerCountIs8 =
  refl

data SardRegularValueSlicingStatusRow : Set where
  childBoundaryRecordedStatus :
    SardRegularValueSlicingStatusRow
  smoothChartAtlasTargetRecordedStatus :
    SardRegularValueSlicingStatusRow
  PhiDifferentialTargetRecordedStatus :
    SardRegularValueSlicingStatusRow
  regularValueCarrierRecordedStatus :
    SardRegularValueSlicingStatusRow
  criticalSetAwayFromAntipodalRecordedStatus :
    SardRegularValueSlicingStatusRow
  SardExceptionalSetTargetRecordedStatus :
    SardRegularValueSlicingStatusRow
  WhitneyPacketSliceTargetRecordedStatus :
    SardRegularValueSlicingStatusRow
  outputGreatCircleStripCompatibilityRecordedStatus :
    SardRegularValueSlicingStatusRow
  allProofAndPromotionFlagsRemainFalseStatus :
    SardRegularValueSlicingStatusRow

canonicalSardRegularValueSlicingStatusRows :
  List SardRegularValueSlicingStatusRow
canonicalSardRegularValueSlicingStatusRows =
  childBoundaryRecordedStatus
  ∷ smoothChartAtlasTargetRecordedStatus
  ∷ PhiDifferentialTargetRecordedStatus
  ∷ regularValueCarrierRecordedStatus
  ∷ criticalSetAwayFromAntipodalRecordedStatus
  ∷ SardExceptionalSetTargetRecordedStatus
  ∷ WhitneyPacketSliceTargetRecordedStatus
  ∷ outputGreatCircleStripCompatibilityRecordedStatus
  ∷ allProofAndPromotionFlagsRemainFalseStatus
  ∷ []

sardRegularValueSlicingStatusRowCount : Nat
sardRegularValueSlicingStatusRowCount =
  listLength canonicalSardRegularValueSlicingStatusRows

sardRegularValueSlicingStatusRowCountIs9 :
  sardRegularValueSlicingStatusRowCount ≡ 9
sardRegularValueSlicingStatusRowCountIs9 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data SardRegularValueSlicingPromotion : Set where

sardRegularValueSlicingPromotionImpossibleHere :
  SardRegularValueSlicingPromotion →
  ⊥
sardRegularValueSlicingPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSSardRegularValueSlicingBoundaryRecorded : Bool
NSSardRegularValueSlicingBoundaryRecorded =
  true

smoothChartAtlasTargetRecorded : Bool
smoothChartAtlasTargetRecorded =
  true

PhiDifferentialTargetRecorded : Bool
PhiDifferentialTargetRecorded =
  true

regularValueSlicingTargetRecorded : Bool
regularValueSlicingTargetRecorded =
  true

criticalSetAwayFromAntipodalTargetRecorded : Bool
criticalSetAwayFromAntipodalTargetRecorded =
  true

SardExceptionalSetTargetRecorded : Bool
SardExceptionalSetTargetRecorded =
  true

WhitneyPacketSliceTargetRecorded : Bool
WhitneyPacketSliceTargetRecorded =
  true

outputGreatCircleStripCompatibilityRecorded : Bool
outputGreatCircleStripCompatibilityRecorded =
  true

smoothChartAtlasConstructed : Bool
smoothChartAtlasConstructed =
  false

derivativeRankProofCompleted : Bool
derivativeRankProofCompleted =
  false

criticalValueNullSetProofCompleted : Bool
criticalValueNullSetProofCompleted =
  false

stripSlicingEstimateProved : Bool
stripSlicingEstimateProved =
  false

SardRegularValueSlicingProved : Bool
SardRegularValueSlicingProved =
  false

A4WhitneyCouplingInequalityProved : Bool
A4WhitneyCouplingInequalityProved =
  false

A4LeiRenTianFourierOutputCouplingProved : Bool
A4LeiRenTianFourierOutputCouplingProved =
  false

triadicCompensatedLeakageIdentityProved : Bool
triadicCompensatedLeakageIdentityProved =
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
  NSSardRegularValueSlicingBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsSmoothChartAtlasTarget :
  smoothChartAtlasTargetRecorded ≡ true
recordsSmoothChartAtlasTarget =
  refl

recordsPhiDifferentialTarget :
  PhiDifferentialTargetRecorded ≡ true
recordsPhiDifferentialTarget =
  refl

recordsRegularValueSlicingTarget :
  regularValueSlicingTargetRecorded ≡ true
recordsRegularValueSlicingTarget =
  refl

recordsCriticalSetAwayFromAntipodalTarget :
  criticalSetAwayFromAntipodalTargetRecorded ≡ true
recordsCriticalSetAwayFromAntipodalTarget =
  refl

recordsSardExceptionalSetTarget :
  SardExceptionalSetTargetRecorded ≡ true
recordsSardExceptionalSetTarget =
  refl

recordsWhitneyPacketSliceTarget :
  WhitneyPacketSliceTargetRecorded ≡ true
recordsWhitneyPacketSliceTarget =
  refl

recordsOutputGreatCircleStripCompatibility :
  outputGreatCircleStripCompatibilityRecorded ≡ true
recordsOutputGreatCircleStripCompatibility =
  refl

keepsSmoothChartAtlasConstructedFalse :
  smoothChartAtlasConstructed ≡ false
keepsSmoothChartAtlasConstructedFalse =
  refl

keepsDerivativeRankProofFalse :
  derivativeRankProofCompleted ≡ false
keepsDerivativeRankProofFalse =
  refl

keepsCriticalValueNullSetProofFalse :
  criticalValueNullSetProofCompleted ≡ false
keepsCriticalValueNullSetProofFalse =
  refl

keepsStripSlicingEstimateFalse :
  stripSlicingEstimateProved ≡ false
keepsStripSlicingEstimateFalse =
  refl

keepsSardRegularValueSlicingFalse :
  SardRegularValueSlicingProved ≡ false
keepsSardRegularValueSlicingFalse =
  refl

keepsA4WhitneyCouplingFalse :
  A4WhitneyCouplingInequalityProved ≡ false
keepsA4WhitneyCouplingFalse =
  refl

keepsA4FourierOutputCouplingFalse :
  A4LeiRenTianFourierOutputCouplingProved ≡ false
keepsA4FourierOutputCouplingFalse =
  refl

keepsTriadicCompensatedLeakageFalse :
  triadicCompensatedLeakageIdentityProved ≡ false
keepsTriadicCompensatedLeakageFalse =
  refl

keepsFullLocalDefectMonotonicityFalse :
  fullLocalDefectMonotonicity ≡ false
keepsFullLocalDefectMonotonicityFalse =
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
-- Canonical boundary receipt.

record NSSardRegularValueSlicingBoundary : Set where
  field
    importedSupport :
      ImportedSardRegularValueSlicingSupport
    target :
      SardRegularValueSlicingTarget
    obligations :
      List SardRegularValueSlicingObligation
    obligationCountIsCanonical :
      sardRegularValueSlicingObligationCount ≡ 9
    blockers :
      List SardRegularValueSlicingBlocker
    blockerCountIsCanonical :
      sardRegularValueSlicingBlockerCount ≡ 8
    statuses :
      List SardRegularValueSlicingStatusRow
    statusCountIsCanonical :
      sardRegularValueSlicingStatusRowCount ≡ 9
    boundaryRecordedTrue :
      NSSardRegularValueSlicingBoundaryRecorded ≡ true
    smoothChartAtlasTargetRecordedTrue :
      smoothChartAtlasTargetRecorded ≡ true
    PhiDifferentialTargetRecordedTrue :
      PhiDifferentialTargetRecorded ≡ true
    regularValueSlicingTargetRecordedTrue :
      regularValueSlicingTargetRecorded ≡ true
    criticalSetAwayFromAntipodalTargetRecordedTrue :
      criticalSetAwayFromAntipodalTargetRecorded ≡ true
    SardExceptionalSetTargetRecordedTrue :
      SardExceptionalSetTargetRecorded ≡ true
    WhitneyPacketSliceTargetRecordedTrue :
      WhitneyPacketSliceTargetRecorded ≡ true
    outputGreatCircleStripCompatibilityRecordedTrue :
      outputGreatCircleStripCompatibilityRecorded ≡ true
    smoothChartAtlasConstructedFalse :
      smoothChartAtlasConstructed ≡ false
    derivativeRankProofCompletedFalse :
      derivativeRankProofCompleted ≡ false
    criticalValueNullSetProofCompletedFalse :
      criticalValueNullSetProofCompleted ≡ false
    stripSlicingEstimateProvedFalse :
      stripSlicingEstimateProved ≡ false
    SardRegularValueSlicingProvedFalse :
      SardRegularValueSlicingProved ≡ false
    A4WhitneyCouplingInequalityProvedFalse :
      A4WhitneyCouplingInequalityProved ≡ false
    A4LeiRenTianFourierOutputCouplingProvedFalse :
      A4LeiRenTianFourierOutputCouplingProved ≡ false
    triadicCompensatedLeakageIdentityProvedFalse :
      triadicCompensatedLeakageIdentityProved ≡ false
    fullClayNSSolvedFalse :
      fullClayNSSolved ≡ false
    clayNavierStokesPromotedFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

canonicalNSSardRegularValueSlicingBoundary :
  NSSardRegularValueSlicingBoundary
canonicalNSSardRegularValueSlicingBoundary =
  record
    { importedSupport =
        canonicalImportedSardRegularValueSlicingSupport
    ; target =
        canonicalSardRegularValueSlicingTarget
    ; obligations =
        canonicalSardRegularValueSlicingObligations
    ; obligationCountIsCanonical =
        refl
    ; blockers =
        canonicalSardRegularValueSlicingBlockers
    ; blockerCountIsCanonical =
        refl
    ; statuses =
        canonicalSardRegularValueSlicingStatusRows
    ; statusCountIsCanonical =
        refl
    ; boundaryRecordedTrue =
        refl
    ; smoothChartAtlasTargetRecordedTrue =
        refl
    ; PhiDifferentialTargetRecordedTrue =
        refl
    ; regularValueSlicingTargetRecordedTrue =
        refl
    ; criticalSetAwayFromAntipodalTargetRecordedTrue =
        refl
    ; SardExceptionalSetTargetRecordedTrue =
        refl
    ; WhitneyPacketSliceTargetRecordedTrue =
        refl
    ; outputGreatCircleStripCompatibilityRecordedTrue =
        refl
    ; smoothChartAtlasConstructedFalse =
        refl
    ; derivativeRankProofCompletedFalse =
        refl
    ; criticalValueNullSetProofCompletedFalse =
        refl
    ; stripSlicingEstimateProvedFalse =
        refl
    ; SardRegularValueSlicingProvedFalse =
        refl
    ; A4WhitneyCouplingInequalityProvedFalse =
        refl
    ; A4LeiRenTianFourierOutputCouplingProvedFalse =
        refl
    ; triadicCompensatedLeakageIdentityProvedFalse =
        refl
    ; fullClayNSSolvedFalse =
        refl
    ; clayNavierStokesPromotedFalse =
        refl
    ; terminalPromotionFalse =
        refl
    }
