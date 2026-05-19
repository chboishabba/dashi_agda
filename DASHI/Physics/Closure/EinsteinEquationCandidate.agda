module DASHI.Physics.Closure.EinsteinEquationCandidate where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Unit using (⊤; tt)

import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as DET
import DASHI.Physics.Closure.W4CalibrationRatioZPeakReceiptRequestSurface as W4Anchor
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as W4External
import DASHI.Physics.Closure.W4PhysicalCalibrationObligationSurface as W4
import DASHI.Physics.Closure.W5PDFCarrierExternalIntakeRequest as W5PDFIntake

------------------------------------------------------------------------
-- Discrete Einstein-equation obligation surface.
--
-- Revised GR framing:
-- * the current flat-vacuum surface is correct;
-- * non-flat connection/source terms are not constructed here;
-- * any non-flat/source route is gated on W4 matter coupling;
-- * the target equation is only the obligation shape
--     G_mu_nu = 8pi T_mu_nu.
--
-- This module does not claim Bianchi, continuum limit, non-flat connection,
-- GR recovery, or promotion into a downstream GR/QFT closure receipt.

data EinsteinEquationCandidateStatus : Set where
  flatVacuumCorrectW4MatterCouplingNeeded :
    EinsteinEquationCandidateStatus

data EinsteinEquationFirstMissingField : Set where
  missingW4MatterCouplingReceipt :
    EinsteinEquationFirstMissingField
  missingW4SourcedNonFlatConnection :
    EinsteinEquationFirstMissingField
  missingW4StressEnergyTensor :
    EinsteinEquationFirstMissingField
  missingDiscreteEinsteinEquationLaw :
    EinsteinEquationFirstMissingField

data EinsteinEquationMatterCouplingQueueField : Set where
  missingW4AnchorReceipt :
    EinsteinEquationMatterCouplingQueueField
  missingW4CalibrationAuthority :
    EinsteinEquationMatterCouplingQueueField
  missingMergedW4W5ExternalPDFIntake :
    EinsteinEquationMatterCouplingQueueField
  missingAcceptedDYPDFBackedW4Adequacy :
    EinsteinEquationMatterCouplingQueueField
  missingW4MatterField :
    EinsteinEquationMatterCouplingQueueField
  missingW4StressEnergyTensorFromMatterField :
    EinsteinEquationMatterCouplingQueueField
  missingDiscreteEinsteinEquationLawFromStressEnergy :
    EinsteinEquationMatterCouplingQueueField

data AcceptedDYPDFBackedW4Adequacy : Set where

acceptedDYPDFBackedW4AdequacyImpossibleHere :
  AcceptedDYPDFBackedW4Adequacy →
  ⊥
acceptedDYPDFBackedW4AdequacyImpossibleHere ()

data W4MatterStressEnergyInterfaceStatus : Set where
  blockedAwaitingW4AuthorityBackedMatterAndStressEnergy :
    W4MatterStressEnergyInterfaceStatus

data W4MatterStressEnergyInterfaceMissingField : Set where
  missingW4AnchorArtifactReceiptForMatterStress :
    W4MatterStressEnergyInterfaceMissingField
  missingW4CalibrationAuthorityForMatterStress :
    W4MatterStressEnergyInterfaceMissingField
  missingW4W5PDFIntakeForMatterStress :
    W4MatterStressEnergyInterfaceMissingField
  missingAcceptedDYPDFBackedAdequacyForMatterStress :
    W4MatterStressEnergyInterfaceMissingField
  missingW4AuthorityBackedMatterField :
    W4MatterStressEnergyInterfaceMissingField
  missingW4AuthorityBackedStressEnergyTensor :
    W4MatterStressEnergyInterfaceMissingField

canonicalW4MatterStressEnergyInterfaceMissingFields :
  List W4MatterStressEnergyInterfaceMissingField
canonicalW4MatterStressEnergyInterfaceMissingFields =
  missingW4AnchorArtifactReceiptForMatterStress
  ∷ missingW4CalibrationAuthorityForMatterStress
  ∷ missingW4W5PDFIntakeForMatterStress
  ∷ missingAcceptedDYPDFBackedAdequacyForMatterStress
  ∷ missingW4AuthorityBackedMatterField
  ∷ missingW4AuthorityBackedStressEnergyTensor
  ∷ []

record W4MatterStressEnergyInterfaceReceipt : Setω where
  field
    w4AnchorReceipt :
      W4Anchor.W4SameRecordZPeakT21T22ArtifactReceiptRequest

    w4CalibrationAuthorityReceipt :
      W4External.Candidate256PhysicalCalibrationExternalReceipt

    mergedW4W5ExternalPDFIntake :
      W5PDFIntake.W5PDFCarrierExternalIntakeRequest

    acceptedDYLuminosityConvention :
      W4.AcceptedDYLuminosityConvention

    acceptedDYPDFBackedW4Adequacy :
      AcceptedDYPDFBackedW4Adequacy

    MatterField :
      Set

    StressEnergyTensor :
      MatterField →
      Set

    matterFieldFromW4 :
      (anchor :
        W4Anchor.W4SameRecordZPeakT21T22ArtifactReceiptRequest) →
      (calibration :
        W4External.Candidate256PhysicalCalibrationExternalReceipt) →
      (pdfIntake :
        W5PDFIntake.W5PDFCarrierExternalIntakeRequest) →
      (dyConvention :
        W4.AcceptedDYLuminosityConvention) →
      (adequacy :
        AcceptedDYPDFBackedW4Adequacy) →
      MatterField

    matterFieldUsesReceiptFields :
      matterFieldFromW4
        w4AnchorReceipt
        w4CalibrationAuthorityReceipt
        mergedW4W5ExternalPDFIntake
        acceptedDYLuminosityConvention
        acceptedDYPDFBackedW4Adequacy
      ≡
      matterFieldFromW4
        w4AnchorReceipt
        w4CalibrationAuthorityReceipt
        mergedW4W5ExternalPDFIntake
        acceptedDYLuminosityConvention
        acceptedDYPDFBackedW4Adequacy

    stressEnergyTensorFromW4 :
      (anchor :
        W4Anchor.W4SameRecordZPeakT21T22ArtifactReceiptRequest) →
      (calibration :
        W4External.Candidate256PhysicalCalibrationExternalReceipt) →
      (pdfIntake :
        W5PDFIntake.W5PDFCarrierExternalIntakeRequest) →
      (dyConvention :
        W4.AcceptedDYLuminosityConvention) →
      (adequacy :
        AcceptedDYPDFBackedW4Adequacy) →
      (matter : MatterField) →
      matter
      ≡
      matterFieldFromW4
        anchor
        calibration
        pdfIntake
        dyConvention
        adequacy →
      StressEnergyTensor matter

    stressEnergyTensorUsesW4MatterField :
      stressEnergyTensorFromW4
        w4AnchorReceipt
        w4CalibrationAuthorityReceipt
        mergedW4W5ExternalPDFIntake
        acceptedDYLuminosityConvention
        acceptedDYPDFBackedW4Adequacy
        (matterFieldFromW4
          w4AnchorReceipt
          w4CalibrationAuthorityReceipt
          mergedW4W5ExternalPDFIntake
          acceptedDYLuminosityConvention
          acceptedDYPDFBackedW4Adequacy)
        refl
      ≡
      stressEnergyTensorFromW4
        w4AnchorReceipt
        w4CalibrationAuthorityReceipt
        mergedW4W5ExternalPDFIntake
        acceptedDYLuminosityConvention
        acceptedDYPDFBackedW4Adequacy
        (matterFieldFromW4
          w4AnchorReceipt
          w4CalibrationAuthorityReceipt
          mergedW4W5ExternalPDFIntake
          acceptedDYLuminosityConvention
          acceptedDYPDFBackedW4Adequacy)
        refl

    interfaceBoundary :
      List String

w4MatterStressEnergyInterfaceReceiptImpossibleHere :
  W4MatterStressEnergyInterfaceReceipt →
  ⊥
w4MatterStressEnergyInterfaceReceiptImpossibleHere receipt =
  W4External.candidate256PhysicalCalibrationExternalReceiptImpossibleHere
    (W4MatterStressEnergyInterfaceReceipt.w4CalibrationAuthorityReceipt
      receipt)

w4MatterStressEnergyInterfaceReceiptImpossibleWithoutAcceptedDYAdequacy :
  W4MatterStressEnergyInterfaceReceipt →
  ⊥
w4MatterStressEnergyInterfaceReceiptImpossibleWithoutAcceptedDYAdequacy
  receipt =
  acceptedDYPDFBackedW4AdequacyImpossibleHere
    (W4MatterStressEnergyInterfaceReceipt.acceptedDYPDFBackedW4Adequacy
      receipt)

stressEnergyPromotionImpossibleWithoutW4CalibrationAnchorAndAdequacy :
  W4MatterStressEnergyInterfaceReceipt →
  ⊥
stressEnergyPromotionImpossibleWithoutW4CalibrationAnchorAndAdequacy =
  w4MatterStressEnergyInterfaceReceiptImpossibleHere

record W4MatterStressEnergyInterfaceDiagnostic : Setω where
  field
    status :
      W4MatterStressEnergyInterfaceStatus

    firstMissing :
      W4MatterStressEnergyInterfaceMissingField

    firstMissingIsW4AnchorArtifactReceipt :
      firstMissing
      ≡
      missingW4AnchorArtifactReceiptForMatterStress

    orderedMissingFields :
      List W4MatterStressEnergyInterfaceMissingField

    orderedMissingFieldsAreCanonical :
      orderedMissingFields
      ≡
      canonicalW4MatterStressEnergyInterfaceMissingFields

    requiredReceiptName :
      String

    matterFieldFunctionName :
      String

    stressEnergyTensorFunctionName :
      String

    authorityGateName :
      String

    acceptedDYAdequacyGateName :
      String

    interfaceBoundary :
      List String

    nonPromotionBoundary :
      List String

    impossibleReceiptHere :
      W4MatterStressEnergyInterfaceReceipt →
      ⊥

    impossibleReceiptWithoutAcceptedDYAdequacy :
      W4MatterStressEnergyInterfaceReceipt →
      ⊥

    noStressEnergyPromotionWithoutW4CalibrationAnchorAndAdequacy :
      W4MatterStressEnergyInterfaceReceipt →
      ⊥

canonicalW4MatterStressEnergyInterfaceDiagnostic :
  W4MatterStressEnergyInterfaceDiagnostic
canonicalW4MatterStressEnergyInterfaceDiagnostic =
  record
    { status =
        blockedAwaitingW4AuthorityBackedMatterAndStressEnergy
    ; firstMissing =
        missingW4AnchorArtifactReceiptForMatterStress
    ; firstMissingIsW4AnchorArtifactReceipt =
        refl
    ; orderedMissingFields =
        canonicalW4MatterStressEnergyInterfaceMissingFields
    ; orderedMissingFieldsAreCanonical =
        refl
    ; requiredReceiptName =
        "DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
    ; matterFieldFunctionName =
        "matterFieldFromW4"
    ; stressEnergyTensorFunctionName =
        "stressEnergyTensorFromW4"
    ; authorityGateName =
        "DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus"
    ; acceptedDYAdequacyGateName =
        "DASHI.Physics.Closure.EinsteinEquationCandidate.AcceptedDYPDFBackedW4Adequacy"
    ; interfaceBoundary =
        "matterFieldFromW4 must consume the W4 t21/t22 anchor receipt, Candidate256 external calibration receipt, merged W4/W5 PDF intake, accepted DY convention, and accepted DY/PDF-backed W4 adequacy"
        ∷ "stressEnergyTensorFromW4 must consume the same W4/W5/DY adequacy receipt tuple and a matter field definitionally tied to matterFieldFromW4"
        ∷ "No MatterField value is constructed without those receipt arguments"
        ∷ "No StressEnergyTensor value is constructed without W4 anchor, W4 calibration authority, accepted DY/PDF-backed adequacy, and a W4-derived matter field"
        ∷ []
    ; nonPromotionBoundary =
        "This diagnostic does not construct Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "This diagnostic does not construct AcceptedDYLuminosityConvention"
        ∷ "This diagnostic does not construct AcceptedDYPDFBackedW4Adequacy"
        ∷ "This diagnostic does not construct W4MatterStressEnergyInterfaceReceipt"
        ∷ "This diagnostic does not assert a stress-energy receipt"
        ∷ "This diagnostic does not promote GR, W4, W5, W8, or GR/QFT closure"
        ∷ []
    ; impossibleReceiptHere =
        w4MatterStressEnergyInterfaceReceiptImpossibleHere
    ; impossibleReceiptWithoutAcceptedDYAdequacy =
        w4MatterStressEnergyInterfaceReceiptImpossibleWithoutAcceptedDYAdequacy
    ; noStressEnergyPromotionWithoutW4CalibrationAnchorAndAdequacy =
        stressEnergyPromotionImpossibleWithoutW4CalibrationAnchorAndAdequacy
    }

w4MatterStressEnergyInterfaceExactFirstMissing :
  W4MatterStressEnergyInterfaceDiagnostic.firstMissing
    canonicalW4MatterStressEnergyInterfaceDiagnostic
  ≡
  missingW4AnchorArtifactReceiptForMatterStress
w4MatterStressEnergyInterfaceExactFirstMissing = refl

record W4StressEnergyConsumerCarrier
  (receipt : W4MatterStressEnergyInterfaceReceipt) : Setω where
  field
    matter :
      W4MatterStressEnergyInterfaceReceipt.MatterField receipt

    stressEnergy :
      W4MatterStressEnergyInterfaceReceipt.StressEnergyTensor receipt matter

    matterIsFromW4 :
      matter
      ≡
      W4MatterStressEnergyInterfaceReceipt.matterFieldFromW4
        receipt
        (W4MatterStressEnergyInterfaceReceipt.w4AnchorReceipt receipt)
        (W4MatterStressEnergyInterfaceReceipt.w4CalibrationAuthorityReceipt
          receipt)
        (W4MatterStressEnergyInterfaceReceipt.mergedW4W5ExternalPDFIntake
          receipt)
        (W4MatterStressEnergyInterfaceReceipt.acceptedDYLuminosityConvention
          receipt)
        (W4MatterStressEnergyInterfaceReceipt.acceptedDYPDFBackedW4Adequacy
          receipt)

    stressEnergyIsFromW4 :
      stressEnergy
      ≡
      W4MatterStressEnergyInterfaceReceipt.stressEnergyTensorFromW4
        receipt
        (W4MatterStressEnergyInterfaceReceipt.w4AnchorReceipt receipt)
        (W4MatterStressEnergyInterfaceReceipt.w4CalibrationAuthorityReceipt
          receipt)
        (W4MatterStressEnergyInterfaceReceipt.mergedW4W5ExternalPDFIntake
          receipt)
        (W4MatterStressEnergyInterfaceReceipt.acceptedDYLuminosityConvention
          receipt)
        (W4MatterStressEnergyInterfaceReceipt.acceptedDYPDFBackedW4Adequacy
          receipt)
        matter
        matterIsFromW4

record W4DiscreteGREquationLawObligation
  (receipt : W4MatterStressEnergyInterfaceReceipt) : Setω where
  field
    curvatureCarrier :
      Set

    einsteinEquationCarrier :
      Set

    einsteinEquationConsumer :
      W4StressEnergyConsumerCarrier receipt →
      curvatureCarrier →
      einsteinEquationCarrier

    grEquationLaw :
      einsteinEquationCarrier →
      Set

    grEquationLawAtConsumer :
      (stressEnergy :
        W4StressEnergyConsumerCarrier receipt) →
      (curvature :
        curvatureCarrier) →
      grEquationLaw
        (einsteinEquationConsumer stressEnergy curvature)

    equationTargetLabel :
      String

    consumerBoundary :
      List String

canonicalEinsteinEquationFirstMissingFields :
  List EinsteinEquationFirstMissingField
canonicalEinsteinEquationFirstMissingFields =
  missingW4MatterCouplingReceipt
  ∷ missingW4SourcedNonFlatConnection
  ∷ missingW4StressEnergyTensor
  ∷ missingDiscreteEinsteinEquationLaw
  ∷ []

canonicalEinsteinEquationMatterCouplingQueue :
  List EinsteinEquationMatterCouplingQueueField
canonicalEinsteinEquationMatterCouplingQueue =
  missingW4AnchorReceipt
  ∷ missingW4CalibrationAuthority
  ∷ missingMergedW4W5ExternalPDFIntake
  ∷ missingAcceptedDYPDFBackedW4Adequacy
  ∷ missingW4MatterField
  ∷ missingW4StressEnergyTensorFromMatterField
  ∷ missingDiscreteEinsteinEquationLawFromStressEnergy
  ∷ []

data EinsteinEquationUnsupportedClaim : Set where
  unsupportedBianchiClaim :
    EinsteinEquationUnsupportedClaim
  unsupportedContinuumLimitClaim :
    EinsteinEquationUnsupportedClaim
  unsupportedNonFlatConnectionClaim :
    EinsteinEquationUnsupportedClaim
  unsupportedGRRecoveryClaim :
    EinsteinEquationUnsupportedClaim

canonicalEinsteinEquationUnsupportedClaims :
  List EinsteinEquationUnsupportedClaim
canonicalEinsteinEquationUnsupportedClaims =
  unsupportedBianchiClaim
  ∷ unsupportedContinuumLimitClaim
  ∷ unsupportedNonFlatConnectionClaim
  ∷ unsupportedGRRecoveryClaim
  ∷ []

record EinsteinEquationCandidateObligationSurface : Setω where
  field
    status :
      EinsteinEquationCandidateStatus

    flatVacuumSurface :
      DET.DiscreteEinsteinTensorCandidateSurface

    flatVacuumCondition :
      DET.DiscreteEinsteinTensorCandidateSurface.flatCurvatureCondition
        flatVacuumSurface

    discreteEinsteinTensorDiagnostic :
      DET.DiscreteEinsteinTensorCandidateDiagnostic

    w4MatterCouplingGate :
      W4.W4PhysicalCalibrationObligationSurface

    w4AnchorName :
      String

    equationTargetLabel :
      String

    sourceTermLabel :
      String

    firstMissing :
      EinsteinEquationFirstMissingField

    orderedFirstMissingFields :
      List EinsteinEquationFirstMissingField

    matterCouplingQueue :
      List EinsteinEquationMatterCouplingQueueField

    nextMatterCouplingQueueField :
      EinsteinEquationMatterCouplingQueueField

    nextQueueFieldIsW4Anchor :
      nextMatterCouplingQueueField
      ≡
      missingW4AnchorReceipt

    postAnchorNextQueueField :
      EinsteinEquationMatterCouplingQueueField

    postAnchorNextIsW4CalibrationAuthority :
      postAnchorNextQueueField
      ≡
      missingW4CalibrationAuthority

    requiredPostAuthorityInterfaceName :
      String

    postAuthorityNextQueueField :
      EinsteinEquationMatterCouplingQueueField

    postAuthorityNextIsMergedW4W5ExternalPDFIntake :
      postAuthorityNextQueueField
      ≡
      missingMergedW4W5ExternalPDFIntake

    mergedW4W5ExternalPDFIntakeRequest :
      W5PDFIntake.W5PDFCarrierExternalIntakeRequest

    postPDFIntakeNextQueueField :
      EinsteinEquationMatterCouplingQueueField

    postPDFIntakeNextIsAcceptedDYPDFBackedW4Adequacy :
      postPDFIntakeNextQueueField
      ≡
      missingAcceptedDYPDFBackedW4Adequacy

    firstActionableGRBlockerAfterSharedW4W5Dependencies :
      String

    postSharedW4W5NextQueueField :
      EinsteinEquationMatterCouplingQueueField

    postSharedW4W5NextIsMatterField :
      postSharedW4W5NextQueueField
      ≡
      missingW4MatterField

    firstMissingIsW4MatterCoupling :
      firstMissing
      ≡
      missingW4MatterCouplingReceipt

    unsupportedClaims :
      List EinsteinEquationUnsupportedClaim

    obligationBoundary :
      List String

    nonPromotionBoundary :
      List String

canonicalEinsteinEquationCandidateObligationSurface :
  EinsteinEquationCandidateObligationSurface
canonicalEinsteinEquationCandidateObligationSurface =
  record
    { status =
        flatVacuumCorrectW4MatterCouplingNeeded
    ; flatVacuumSurface =
        DET.flatOnlyDiscreteEinsteinTensorCandidateSurface
    ; flatVacuumCondition =
        tt
    ; discreteEinsteinTensorDiagnostic =
        DET.canonicalDiscreteEinsteinTensorCandidateDiagnostic
    ; w4MatterCouplingGate =
        W4.canonicalW4PhysicalCalibrationObligationSurface
    ; w4AnchorName =
        W4.W4PhysicalCalibrationObligationSurface.zPeakAnchorName
          W4.canonicalW4PhysicalCalibrationObligationSurface
    ; equationTargetLabel =
        "G_mu_nu = 8pi T_mu_nu"
    ; sourceTermLabel =
        "T_mu_nu must come from W4 matter coupling before a non-flat GR target can be consumed"
    ; firstMissing =
        missingW4MatterCouplingReceipt
    ; orderedFirstMissingFields =
        canonicalEinsteinEquationFirstMissingFields
    ; matterCouplingQueue =
        canonicalEinsteinEquationMatterCouplingQueue
    ; nextMatterCouplingQueueField =
        missingW4AnchorReceipt
    ; nextQueueFieldIsW4Anchor =
        refl
    ; postAnchorNextQueueField =
        missingW4CalibrationAuthority
    ; postAnchorNextIsW4CalibrationAuthority =
        refl
    ; requiredPostAuthorityInterfaceName =
        "DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
    ; postAuthorityNextQueueField =
        missingMergedW4W5ExternalPDFIntake
    ; postAuthorityNextIsMergedW4W5ExternalPDFIntake =
        refl
    ; mergedW4W5ExternalPDFIntakeRequest =
        W5PDFIntake.canonicalW5PDFCarrierExternalIntakeRequest
    ; postPDFIntakeNextQueueField =
        missingAcceptedDYPDFBackedW4Adequacy
    ; postPDFIntakeNextIsAcceptedDYPDFBackedW4Adequacy =
        refl
    ; firstActionableGRBlockerAfterSharedW4W5Dependencies =
        "DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
    ; postSharedW4W5NextQueueField =
        missingW4MatterField
    ; postSharedW4W5NextIsMatterField =
        refl
    ; firstMissingIsW4MatterCoupling =
        refl
    ; unsupportedClaims =
        canonicalEinsteinEquationUnsupportedClaims
    ; obligationBoundary =
        "Flat vacuum is the currently correct local GR surface"
        ∷ "The target equation is recorded only as G_mu_nu = 8pi T_mu_nu"
        ∷ "The first W4 gate is the W4 anchor receipt"
        ∷ "After the W4 anchor exists, the next typed GR action is W4 calibration authority"
        ∷ "After W4 calibration authority, the merged W4+W5 external PDF intake is required before matter is available"
        ∷ "After merged W4+W5 external PDF intake, accepted DY/PDF-backed W4 adequacy is required before matterFieldFromW4 is admissible"
        ∷ "After W4 anchor, calibration authority, merged W4+W5 external PDF intake, and accepted DY/PDF-backed W4 adequacy, the first actionable GR blocker is W4MatterStressEnergyInterfaceReceipt"
        ∷ "T_mu_nu is gated on a W4 matter field and stress-energy tensor"
        ∷ "Any non-flat connection must be sourced through the W4 matter-coupling queue"
        ∷ "The current W4 surface remains an obligation surface, not a supplied matter-coupling receipt"
        ∷ []
    ; nonPromotionBoundary =
        "This module does not construct a non-flat connection"
        ∷ "This module does not prove Bianchi"
        ∷ "This module does not prove a continuum limit"
        ∷ "This module does not prove GR recovery"
        ∷ "This module does not inhabit a GR/QFT closure-promotion receipt"
        ∷ []
    }

einsteinEquationCandidateExactFirstMissing :
  EinsteinEquationCandidateObligationSurface.firstMissing
    canonicalEinsteinEquationCandidateObligationSurface
  ≡
  missingW4MatterCouplingReceipt
einsteinEquationCandidateExactFirstMissing = refl

einsteinEquationCandidateStatusIsObligationOnly :
  EinsteinEquationCandidateObligationSurface.status
    canonicalEinsteinEquationCandidateObligationSurface
  ≡
  flatVacuumCorrectW4MatterCouplingNeeded
einsteinEquationCandidateStatusIsObligationOnly = refl
