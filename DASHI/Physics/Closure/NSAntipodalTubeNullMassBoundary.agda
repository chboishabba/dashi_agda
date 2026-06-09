module DASHI.Physics.Closure.NSAntipodalTubeNullMassBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSFourierOutputPushforwardBoundary
  as Pushforward
import DASHI.Physics.Closure.NSLeiRenTianFourierOutputCouplingBoundary
  as A4
import DASHI.Physics.Closure.NSLocalizedWhitneyFramePacketEstimateBoundary
  as WhitneyPacket
import DASHI.Physics.Closure.NSWhitneyCouplingInequalityBoundary
  as WhitneyCoupling

------------------------------------------------------------------------
-- NS A4 antipodal tube null-mass boundary.
--
-- Child target of the Fourier-output pushforward and Whitney-coupling
-- surfaces:
--
--   A_epsilon = { (theta1,theta2) : |theta1 + theta2| < epsilon }
--
-- must be discarded before applying
--
--   c-hat = normalize(theta1 + theta2).
--
-- The analytic obligation is either a quantitative product/angular tube
-- estimate mass(A_epsilon) = O(epsilon^2), or the weaker Abel-window form
-- used by A4: the normalized Abel defect mass of A_epsilon vanishes as
-- epsilon -> 0 and the log window is refined.
--
-- This module is a checked proof-contract only.  It records the antipodal
-- locus, tube target, compatibility with Whitney packets and Abel log
-- windows, and the exact blockers.  It does not prove the tube volume
-- estimate, does not prove the Fubini/Sard transfer, does not prove A4,
-- and does not promote Navier-Stokes Clay.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support anchors.

fourierPushforwardBoundaryReference : String
fourierPushforwardBoundaryReference =
  "DASHI.Physics.Closure.NSFourierOutputPushforwardBoundary"

whitneyPacketBoundaryReference : String
whitneyPacketBoundaryReference =
  "DASHI.Physics.Closure.NSLocalizedWhitneyFramePacketEstimateBoundary"

whitneyCouplingBoundaryReference : String
whitneyCouplingBoundaryReference =
  "DASHI.Physics.Closure.NSWhitneyCouplingInequalityBoundary"

parentA4BoundaryReference : String
parentA4BoundaryReference =
  "DASHI.Physics.Closure.NSLeiRenTianFourierOutputCouplingBoundary"

record ImportedAntipodalTubeSupport : Set where
  field
    pushforwardSupport :
      Pushforward.ImportedFourierOutputPushforwardSupport
    pushforwardSupportIsCanonical :
      pushforwardSupport
        ≡ Pushforward.canonicalImportedFourierOutputPushforwardSupport
    phiMap :
      Pushforward.FourierOutputPhiMap
    phiMapIsCanonical :
      phiMap ≡ Pushforward.canonicalFourierOutputPhiMap
    antipodalExclusion :
      Pushforward.AntipodalExclusionCarrier
    antipodalExclusionIsCanonical :
      antipodalExclusion ≡ Pushforward.canonicalAntipodalExclusionCarrier
    localizedPacketSupport :
      WhitneyPacket.ImportedLocalizedWhitneyFramePacketSupport
    localizedPacketSupportIsCanonical :
      localizedPacketSupport
        ≡ WhitneyPacket.canonicalImportedLocalizedWhitneyFramePacketSupport
    scaleWindowCompatibility :
      WhitneyPacket.ScaleWindowCompatibilityControl
    scaleWindowCompatibilityIsCanonical :
      scaleWindowCompatibility
        ≡ WhitneyPacket.canonicalScaleWindowCompatibilityControl
    whitneyCouplingSupport :
      WhitneyCoupling.ImportedWhitneyCouplingSupport
    whitneyCouplingSupportIsCanonical :
      whitneyCouplingSupport
        ≡ WhitneyCoupling.canonicalImportedWhitneyCouplingSupport
    parentA4Boundary :
      A4.NSLeiRenTianFourierOutputCouplingBoundary
    parentA4BoundaryIsCanonical :
      parentA4Boundary ≡ A4.canonicalNSLeiRenTianFourierOutputCouplingBoundary
    pushforwardAntipodalTargetStillOpen :
      Pushforward.SardFubiniAntipodalNullSetProved ≡ false
    whitneySardFubiniStepStillOpen :
      WhitneyCoupling.SardFubiniStepProved ≡ false

canonicalImportedAntipodalTubeSupport :
  ImportedAntipodalTubeSupport
canonicalImportedAntipodalTubeSupport =
  record
    { pushforwardSupport =
        Pushforward.canonicalImportedFourierOutputPushforwardSupport
    ; pushforwardSupportIsCanonical =
        refl
    ; phiMap =
        Pushforward.canonicalFourierOutputPhiMap
    ; phiMapIsCanonical =
        refl
    ; antipodalExclusion =
        Pushforward.canonicalAntipodalExclusionCarrier
    ; antipodalExclusionIsCanonical =
        refl
    ; localizedPacketSupport =
        WhitneyPacket.canonicalImportedLocalizedWhitneyFramePacketSupport
    ; localizedPacketSupportIsCanonical =
        refl
    ; scaleWindowCompatibility =
        WhitneyPacket.canonicalScaleWindowCompatibilityControl
    ; scaleWindowCompatibilityIsCanonical =
        refl
    ; whitneyCouplingSupport =
        WhitneyCoupling.canonicalImportedWhitneyCouplingSupport
    ; whitneyCouplingSupportIsCanonical =
        refl
    ; parentA4Boundary =
        A4.canonicalNSLeiRenTianFourierOutputCouplingBoundary
    ; parentA4BoundaryIsCanonical =
        refl
    ; pushforwardAntipodalTargetStillOpen =
        refl
    ; whitneySardFubiniStepStillOpen =
        refl
    }

------------------------------------------------------------------------
-- Antipodal tube carriers.

data AntipodalLocusCarrier : Set where
  thetaOnePlusThetaTwoEqualsZero :
    Pushforward.InputAngularPairCarrier →
    AntipodalLocusCarrier

data AntipodalTubeCarrier : Set where
  epsilonTubeAroundAntipodalLocus :
    Nat →
    AntipodalLocusCarrier →
    AntipodalTubeCarrier

data AntipodalTubeMassTarget : Set where
  productAngularTubeMassIsQuadratic :
    AntipodalTubeCarrier →
    AntipodalTubeMassTarget
  AbelWindowAntipodalMassVanishes :
    AntipodalTubeCarrier →
    WhitneyPacket.ScaleWindowCompatibilityControl →
    AntipodalTubeMassTarget

data NormalizeSumDomainExclusion : Set where
  cHatNormalizeSumDefinedOffAntipodalTube :
    Pushforward.FourierOutputPhiMap →
    Pushforward.AntipodalExclusionCarrier →
    AntipodalTubeCarrier →
    NormalizeSumDomainExclusion

data WhitneyPacketAntipodalCompatibility : Set where
  WhitneyPacketsRespectAntipodalTubeDiscard :
    WhitneyPacket.WhitneyAngularCapCover →
    WhitneyPacket.FramePacket →
    WhitneyPacket.AnnularExclusionControl →
    AntipodalTubeCarrier →
    WhitneyPacketAntipodalCompatibility

data AbelLogWindowAntipodalCompatibility : Set where
  AbelLogWindowDiscardCommutesWithWhitneyRefinement :
    WhitneyPacket.LocalParabolicWindow →
    WhitneyPacket.DyadicShellWindow →
    WhitneyPacket.ScaleWindowCompatibilityControl →
    AntipodalTubeMassTarget →
    AbelLogWindowAntipodalCompatibility

data AntipodalTubeNullMassTarget : Set where
  discardAntipodalTubeBeforeFourierOutputPushforward :
    AntipodalLocusCarrier →
    AntipodalTubeCarrier →
    AntipodalTubeMassTarget →
    NormalizeSumDomainExclusion →
    WhitneyPacketAntipodalCompatibility →
    AbelLogWindowAntipodalCompatibility →
    Pushforward.SardFubiniNullSetObligation →
    WhitneyCoupling.SardFubiniGap →
    AntipodalTubeNullMassTarget

canonicalAntipodalLocusCarrier :
  AntipodalLocusCarrier
canonicalAntipodalLocusCarrier =
  thetaOnePlusThetaTwoEqualsZero
    Pushforward.canonicalInputAngularPairCarrier

canonicalAntipodalTubeCarrier :
  AntipodalTubeCarrier
canonicalAntipodalTubeCarrier =
  epsilonTubeAroundAntipodalLocus
    (suc zero)
    canonicalAntipodalLocusCarrier

canonicalQuadraticAntipodalTubeMassTarget :
  AntipodalTubeMassTarget
canonicalQuadraticAntipodalTubeMassTarget =
  productAngularTubeMassIsQuadratic
    canonicalAntipodalTubeCarrier

canonicalAbelAntipodalTubeMassTarget :
  AntipodalTubeMassTarget
canonicalAbelAntipodalTubeMassTarget =
  AbelWindowAntipodalMassVanishes
    canonicalAntipodalTubeCarrier
    WhitneyPacket.canonicalScaleWindowCompatibilityControl

canonicalNormalizeSumDomainExclusion :
  NormalizeSumDomainExclusion
canonicalNormalizeSumDomainExclusion =
  cHatNormalizeSumDefinedOffAntipodalTube
    Pushforward.canonicalFourierOutputPhiMap
    Pushforward.canonicalAntipodalExclusionCarrier
    canonicalAntipodalTubeCarrier

canonicalWhitneyPacketAntipodalCompatibility :
  WhitneyPacketAntipodalCompatibility
canonicalWhitneyPacketAntipodalCompatibility =
  WhitneyPacketsRespectAntipodalTubeDiscard
    WhitneyPacket.canonicalWhitneyAngularCapCover
    WhitneyPacket.canonicalFramePacket
    WhitneyPacket.canonicalAnnularExclusionControl
    canonicalAntipodalTubeCarrier

canonicalAbelLogWindowAntipodalCompatibility :
  AbelLogWindowAntipodalCompatibility
canonicalAbelLogWindowAntipodalCompatibility =
  AbelLogWindowDiscardCommutesWithWhitneyRefinement
    WhitneyPacket.canonicalLocalParabolicWindow
    WhitneyPacket.canonicalDyadicShellWindow
    WhitneyPacket.canonicalScaleWindowCompatibilityControl
    canonicalAbelAntipodalTubeMassTarget

canonicalAntipodalTubeNullMassTarget :
  AntipodalTubeNullMassTarget
canonicalAntipodalTubeNullMassTarget =
  discardAntipodalTubeBeforeFourierOutputPushforward
    canonicalAntipodalLocusCarrier
    canonicalAntipodalTubeCarrier
    canonicalAbelAntipodalTubeMassTarget
    canonicalNormalizeSumDomainExclusion
    canonicalWhitneyPacketAntipodalCompatibility
    canonicalAbelLogWindowAntipodalCompatibility
    Pushforward.canonicalSardFubiniNullSetObligation
    WhitneyCoupling.proveAntipodalLocusHasZeroAbelMass

------------------------------------------------------------------------
-- Obligations, error terms, blockers, and status rows.

data AntipodalTubeNullMassObligation : Set where
  defineAntipodalLocusThetaOnePlusThetaTwoZero :
    AntipodalTubeNullMassObligation
  defineEpsilonTubeAroundAntipodalLocus :
    AntipodalTubeNullMassObligation
  proveProductAngularTubeMassQuadratic :
    AntipodalTubeNullMassObligation
  proveAntipodalTubeMassVanishesInAbelWindow :
    AntipodalTubeNullMassObligation
  restrictNormalizeSumMapToTubeComplement :
    AntipodalTubeNullMassObligation
  proveWhitneyPacketsRespectTubeDiscard :
    AntipodalTubeNullMassObligation
  proveFubiniTransferFromProductMassToPacketMass :
    AntipodalTubeNullMassObligation
  proveDiscardCommutesWithAbelLogWindowRefinement :
    AntipodalTubeNullMassObligation
  feedNullMassIntoWhitneyCouplingInequality :
    AntipodalTubeNullMassObligation

canonicalAntipodalTubeNullMassObligations :
  List AntipodalTubeNullMassObligation
canonicalAntipodalTubeNullMassObligations =
  defineAntipodalLocusThetaOnePlusThetaTwoZero
  ∷ defineEpsilonTubeAroundAntipodalLocus
  ∷ proveProductAngularTubeMassQuadratic
  ∷ proveAntipodalTubeMassVanishesInAbelWindow
  ∷ restrictNormalizeSumMapToTubeComplement
  ∷ proveWhitneyPacketsRespectTubeDiscard
  ∷ proveFubiniTransferFromProductMassToPacketMass
  ∷ proveDiscardCommutesWithAbelLogWindowRefinement
  ∷ feedNullMassIntoWhitneyCouplingInequality
  ∷ []

antipodalTubeNullMassObligationCount : Nat
antipodalTubeNullMassObligationCount =
  listLength canonicalAntipodalTubeNullMassObligations

antipodalTubeNullMassObligationCountIs9 :
  antipodalTubeNullMassObligationCount ≡ 9
antipodalTubeNullMassObligationCountIs9 =
  refl

data AntipodalTubeErrorTerm : Set where
  productTubeVolumeError :
    AntipodalTubeErrorTerm
  packetUniformityLoss :
    AntipodalTubeErrorTerm
  FubiniDisintegrationLoss :
    AntipodalTubeErrorTerm
  AbelWindowRefinementLoss :
    AntipodalTubeErrorTerm
  normalizeSumDegeneracyLoss :
    AntipodalTubeErrorTerm
  WhitneyPacketBoundaryLoss :
    AntipodalTubeErrorTerm

canonicalAntipodalTubeErrorTerms :
  List AntipodalTubeErrorTerm
canonicalAntipodalTubeErrorTerms =
  productTubeVolumeError
  ∷ packetUniformityLoss
  ∷ FubiniDisintegrationLoss
  ∷ AbelWindowRefinementLoss
  ∷ normalizeSumDegeneracyLoss
  ∷ WhitneyPacketBoundaryLoss
  ∷ []

antipodalTubeErrorTermCount : Nat
antipodalTubeErrorTermCount =
  listLength canonicalAntipodalTubeErrorTerms

antipodalTubeErrorTermCountIs6 :
  antipodalTubeErrorTermCount ≡ 6
antipodalTubeErrorTermCountIs6 =
  refl

data AntipodalTubeBlocker : Set where
  missingTubeVolumeEstimate :
    AntipodalTubeBlocker
  missingPacketUniformBound :
    AntipodalTubeBlocker
  missingFubiniTransfer :
    AntipodalTubeBlocker
  missingScaleWindowCompatibility :
    AntipodalTubeBlocker
  missingIntegrationIntoFourierPushforward :
    AntipodalTubeBlocker
  missingA4WhitneyCouplingCompletion :
    AntipodalTubeBlocker
  missingClayPromotion :
    AntipodalTubeBlocker

canonicalAntipodalTubeBlockers :
  List AntipodalTubeBlocker
canonicalAntipodalTubeBlockers =
  missingTubeVolumeEstimate
  ∷ missingPacketUniformBound
  ∷ missingFubiniTransfer
  ∷ missingScaleWindowCompatibility
  ∷ missingIntegrationIntoFourierPushforward
  ∷ missingA4WhitneyCouplingCompletion
  ∷ missingClayPromotion
  ∷ []

antipodalTubeBlockerCount : Nat
antipodalTubeBlockerCount =
  listLength canonicalAntipodalTubeBlockers

antipodalTubeBlockerCountIs7 :
  antipodalTubeBlockerCount ≡ 7
antipodalTubeBlockerCountIs7 =
  refl

data AntipodalTubeStatusRow : Set where
  boundaryRecordedStatus :
    AntipodalTubeStatusRow
  antipodalLocusRecordedStatus :
    AntipodalTubeStatusRow
  epsilonTubeRecordedStatus :
    AntipodalTubeStatusRow
  quadraticTubeMassTargetRecordedStatus :
    AntipodalTubeStatusRow
  AbelWindowVanishTargetRecordedStatus :
    AntipodalTubeStatusRow
  normalizeSumDomainExclusionRecordedStatus :
    AntipodalTubeStatusRow
  WhitneyPacketCompatibilityRecordedStatus :
    AntipodalTubeStatusRow
  scaleWindowCompatibilityRecordedStatus :
    AntipodalTubeStatusRow
  blockersRecordedStatus :
    AntipodalTubeStatusRow
  allProofAndPromotionFlagsFalseStatus :
    AntipodalTubeStatusRow

canonicalAntipodalTubeStatusRows :
  List AntipodalTubeStatusRow
canonicalAntipodalTubeStatusRows =
  boundaryRecordedStatus
  ∷ antipodalLocusRecordedStatus
  ∷ epsilonTubeRecordedStatus
  ∷ quadraticTubeMassTargetRecordedStatus
  ∷ AbelWindowVanishTargetRecordedStatus
  ∷ normalizeSumDomainExclusionRecordedStatus
  ∷ WhitneyPacketCompatibilityRecordedStatus
  ∷ scaleWindowCompatibilityRecordedStatus
  ∷ blockersRecordedStatus
  ∷ allProofAndPromotionFlagsFalseStatus
  ∷ []

antipodalTubeStatusRowCount : Nat
antipodalTubeStatusRowCount =
  listLength canonicalAntipodalTubeStatusRows

antipodalTubeStatusRowCountIs10 :
  antipodalTubeStatusRowCount ≡ 10
antipodalTubeStatusRowCountIs10 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data AntipodalTubePromotion : Set where

antipodalTubePromotionImpossibleHere :
  AntipodalTubePromotion →
  ⊥
antipodalTubePromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSAntipodalTubeNullMassBoundaryRecorded : Bool
NSAntipodalTubeNullMassBoundaryRecorded =
  true

antipodalLocusThetaOnePlusThetaTwoZeroRecorded : Bool
antipodalLocusThetaOnePlusThetaTwoZeroRecorded =
  true

epsilonTubeAroundAntipodalLocusRecorded : Bool
epsilonTubeAroundAntipodalLocusRecorded =
  true

quadraticTubeMassTargetRecorded : Bool
quadraticTubeMassTargetRecorded =
  true

AbelWindowVanishTargetRecorded : Bool
AbelWindowVanishTargetRecorded =
  true

normalizeSumDomainExclusionRecorded : Bool
normalizeSumDomainExclusionRecorded =
  true

WhitneyPacketAntipodalCompatibilityRecorded : Bool
WhitneyPacketAntipodalCompatibilityRecorded =
  true

AbelLogWindowCompatibilityRecorded : Bool
AbelLogWindowCompatibilityRecorded =
  true

antipodalTubeBlockersRecorded : Bool
antipodalTubeBlockersRecorded =
  true

tubeVolumeEstimateProved : Bool
tubeVolumeEstimateProved =
  false

packetUniformBoundProved : Bool
packetUniformBoundProved =
  false

FubiniTransferProved : Bool
FubiniTransferProved =
  false

scaleWindowCompatibilityProved : Bool
scaleWindowCompatibilityProved =
  false

antipodalTubeNullMassProved : Bool
antipodalTubeNullMassProved =
  false

FourierOutputPushforwardAntipodalDiscardProved : Bool
FourierOutputPushforwardAntipodalDiscardProved =
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
  NSAntipodalTubeNullMassBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsAntipodalLocus :
  antipodalLocusThetaOnePlusThetaTwoZeroRecorded ≡ true
recordsAntipodalLocus =
  refl

recordsEpsilonTube :
  epsilonTubeAroundAntipodalLocusRecorded ≡ true
recordsEpsilonTube =
  refl

recordsQuadraticTubeMassTarget :
  quadraticTubeMassTargetRecorded ≡ true
recordsQuadraticTubeMassTarget =
  refl

recordsAbelWindowVanishTarget :
  AbelWindowVanishTargetRecorded ≡ true
recordsAbelWindowVanishTarget =
  refl

recordsNormalizeSumDomainExclusion :
  normalizeSumDomainExclusionRecorded ≡ true
recordsNormalizeSumDomainExclusion =
  refl

recordsWhitneyPacketAntipodalCompatibility :
  WhitneyPacketAntipodalCompatibilityRecorded ≡ true
recordsWhitneyPacketAntipodalCompatibility =
  refl

recordsAbelLogWindowCompatibility :
  AbelLogWindowCompatibilityRecorded ≡ true
recordsAbelLogWindowCompatibility =
  refl

recordsAntipodalTubeBlockers :
  antipodalTubeBlockersRecorded ≡ true
recordsAntipodalTubeBlockers =
  refl

keepsTubeVolumeEstimateFalse :
  tubeVolumeEstimateProved ≡ false
keepsTubeVolumeEstimateFalse =
  refl

keepsPacketUniformBoundFalse :
  packetUniformBoundProved ≡ false
keepsPacketUniformBoundFalse =
  refl

keepsFubiniTransferFalse :
  FubiniTransferProved ≡ false
keepsFubiniTransferFalse =
  refl

keepsScaleWindowCompatibilityFalse :
  scaleWindowCompatibilityProved ≡ false
keepsScaleWindowCompatibilityFalse =
  refl

keepsAntipodalTubeNullMassFalse :
  antipodalTubeNullMassProved ≡ false
keepsAntipodalTubeNullMassFalse =
  refl

keepsFourierOutputPushforwardAntipodalDiscardFalse :
  FourierOutputPushforwardAntipodalDiscardProved ≡ false
keepsFourierOutputPushforwardAntipodalDiscardFalse =
  refl

keepsA4WhitneyCouplingInequalityFalse :
  A4WhitneyCouplingInequalityProved ≡ false
keepsA4WhitneyCouplingInequalityFalse =
  refl

keepsA4LeiRenTianFourierOutputCouplingFalse :
  A4LeiRenTianFourierOutputCouplingProved ≡ false
keepsA4LeiRenTianFourierOutputCouplingFalse =
  refl

keepsFullLocalDefectMonotonicityFalse :
  fullLocalDefectMonotonicity ≡ false
keepsFullLocalDefectMonotonicityFalse =
  refl

keepsFullClayNSFalse :
  fullClayNSSolved ≡ false
keepsFullClayNSFalse =
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
-- Boundary record.

record NSAntipodalTubeNullMassBoundary : Set where
  field
    importedSupport :
      ImportedAntipodalTubeSupport
    antipodalLocus :
      AntipodalLocusCarrier
    antipodalTube :
      AntipodalTubeCarrier
    quadraticMassTarget :
      AntipodalTubeMassTarget
    AbelWindowMassTarget :
      AntipodalTubeMassTarget
    normalizeSumExclusion :
      NormalizeSumDomainExclusion
    WhitneyPacketCompatibility :
      WhitneyPacketAntipodalCompatibility
    AbelWindowCompatibility :
      AbelLogWindowAntipodalCompatibility
    nullMassTarget :
      AntipodalTubeNullMassTarget
    obligations :
      List AntipodalTubeNullMassObligation
    obligationsCountIs9 :
      antipodalTubeNullMassObligationCount ≡ 9
    errorTerms :
      List AntipodalTubeErrorTerm
    errorTermCountIs6 :
      antipodalTubeErrorTermCount ≡ 6
    blockers :
      List AntipodalTubeBlocker
    blockerCountIs7 :
      antipodalTubeBlockerCount ≡ 7
    statusRows :
      List AntipodalTubeStatusRow
    statusRowCountIs10 :
      antipodalTubeStatusRowCount ≡ 10
    boundaryRecordedTrue :
      NSAntipodalTubeNullMassBoundaryRecorded ≡ true
    tubeVolumeEstimateStillFalse :
      tubeVolumeEstimateProved ≡ false
    packetUniformBoundStillFalse :
      packetUniformBoundProved ≡ false
    FubiniTransferStillFalse :
      FubiniTransferProved ≡ false
    scaleWindowCompatibilityStillFalse :
      scaleWindowCompatibilityProved ≡ false
    nullMassStillFalse :
      antipodalTubeNullMassProved ≡ false
    FourierDiscardStillFalse :
      FourierOutputPushforwardAntipodalDiscardProved ≡ false
    A4WhitneyCouplingStillFalse :
      A4WhitneyCouplingInequalityProved ≡ false
    A4CouplingStillFalse :
      A4LeiRenTianFourierOutputCouplingProved ≡ false
    ClayNSStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionStillFalse :
      terminalPromotion ≡ false

canonicalNSAntipodalTubeNullMassBoundary :
  NSAntipodalTubeNullMassBoundary
canonicalNSAntipodalTubeNullMassBoundary =
  record
    { importedSupport =
        canonicalImportedAntipodalTubeSupport
    ; antipodalLocus =
        canonicalAntipodalLocusCarrier
    ; antipodalTube =
        canonicalAntipodalTubeCarrier
    ; quadraticMassTarget =
        canonicalQuadraticAntipodalTubeMassTarget
    ; AbelWindowMassTarget =
        canonicalAbelAntipodalTubeMassTarget
    ; normalizeSumExclusion =
        canonicalNormalizeSumDomainExclusion
    ; WhitneyPacketCompatibility =
        canonicalWhitneyPacketAntipodalCompatibility
    ; AbelWindowCompatibility =
        canonicalAbelLogWindowAntipodalCompatibility
    ; nullMassTarget =
        canonicalAntipodalTubeNullMassTarget
    ; obligations =
        canonicalAntipodalTubeNullMassObligations
    ; obligationsCountIs9 =
        refl
    ; errorTerms =
        canonicalAntipodalTubeErrorTerms
    ; errorTermCountIs6 =
        refl
    ; blockers =
        canonicalAntipodalTubeBlockers
    ; blockerCountIs7 =
        refl
    ; statusRows =
        canonicalAntipodalTubeStatusRows
    ; statusRowCountIs10 =
        refl
    ; boundaryRecordedTrue =
        refl
    ; tubeVolumeEstimateStillFalse =
        refl
    ; packetUniformBoundStillFalse =
        refl
    ; FubiniTransferStillFalse =
        refl
    ; scaleWindowCompatibilityStillFalse =
        refl
    ; nullMassStillFalse =
        refl
    ; FourierDiscardStillFalse =
        refl
    ; A4WhitneyCouplingStillFalse =
        refl
    ; A4CouplingStillFalse =
        refl
    ; ClayNSStillFalse =
        refl
    ; terminalPromotionStillFalse =
        refl
    }
