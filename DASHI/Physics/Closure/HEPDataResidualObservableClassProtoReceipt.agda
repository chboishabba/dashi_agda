module DASHI.Physics.Closure.HEPDataResidualObservableClassProtoReceipt where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataResidualBridgeAuthorityGate as Gate
import DASHI.Physics.Closure.HEPDataResidualObservableClassCandidateDiagnostic as Candidate
import DASHI.Physics.Closure.HEPDataResidualObservableClassRequest as Class
import DASHI.Physics.Closure.HEPDataResidualProviderPayloadIntake as Intake
import DASHI.Physics.Closure.HEPDataResidualProviderReceiptRequestPack as Pack

------------------------------------------------------------------------
-- HEPData residual observable-class proto-receipt.
--
-- This module turns the phistar_50_76 residual observable-class candidate into
-- a provider-facing proto-receipt surface.  It is deliberately not the accepted
-- residualObservableClassReceipt: it only packages the candidate fields in the
-- order the provider chain requires and records that the authority gate still
-- rejects promotion until the remaining residual receipts are supplied.

data HEPDataResidualObservableClassProtoReceiptStatus : Set where
  protoReceiptAssembledButAuthorityRejected :
    HEPDataResidualObservableClassProtoReceiptStatus

data HEPDataResidualObservableClassProtoReceiptField : Set where
  protoResidualObservableKind :
    HEPDataResidualObservableClassProtoReceiptField
  protoBaselineOrInvarianceModel :
    HEPDataResidualObservableClassProtoReceiptField
  protoResidualDefinition :
    HEPDataResidualObservableClassProtoReceiptField
  protoUncertaintyOrCovarianceHandling :
    HEPDataResidualObservableClassProtoReceiptField
  protoSelectionReceiptDependency :
    HEPDataResidualObservableClassProtoReceiptField
  protoCalibrationDependency :
    HEPDataResidualObservableClassProtoReceiptField
  protoProjectionTarget :
    HEPDataResidualObservableClassProtoReceiptField
  protoComparisonLawTarget :
    HEPDataResidualObservableClassProtoReceiptField
  protoNonCollapseJustification :
    HEPDataResidualObservableClassProtoReceiptField
  protoAcceptedAuthorityRouteDependency :
    HEPDataResidualObservableClassProtoReceiptField

canonicalHEPDataResidualObservableClassProtoReceiptFields :
  List HEPDataResidualObservableClassProtoReceiptField
canonicalHEPDataResidualObservableClassProtoReceiptFields =
  protoResidualObservableKind
  ∷ protoBaselineOrInvarianceModel
  ∷ protoResidualDefinition
  ∷ protoUncertaintyOrCovarianceHandling
  ∷ protoSelectionReceiptDependency
  ∷ protoCalibrationDependency
  ∷ protoProjectionTarget
  ∷ protoComparisonLawTarget
  ∷ protoNonCollapseJustification
  ∷ protoAcceptedAuthorityRouteDependency
  ∷ []

record HEPDataResidualObservableClassProtoReceipt : Setω where
  field
    status :
      HEPDataResidualObservableClassProtoReceiptStatus

    candidateDiagnostic :
      Candidate.HEPDataResidualObservableClassCandidateDiagnostic

    providerReceiptRequestPack :
      Pack.HEPDataResidualProviderReceiptRequestPack

    providerPayloadIntake :
      Intake.HEPDataResidualProviderPayloadIntakeFilter

    residualAuthorityGate :
      Gate.HEPDataResidualBridgeAuthorityGate

    protoReceiptFields :
      List HEPDataResidualObservableClassProtoReceiptField

    protoReceiptFieldsAreCanonical :
      protoReceiptFields
      ≡
      canonicalHEPDataResidualObservableClassProtoReceiptFields

    proposedClassSurface :
      Class.HEPDataResidualObservableClassRequestSurface

    proposedClassSurfaceMatchesCandidate :
      proposedClassSurface
      ≡
      Candidate.HEPDataResidualObservableClassCandidateDiagnostic.proposedClassSurface
        candidateDiagnostic

    boundProviderReceipt :
      Pack.HEPDataResidualProviderRequiredReceipt

    boundProviderReceiptIsResidualObservableClass :
      boundProviderReceipt
      ≡
      Pack.residualObservableClassReceipt

    firstMissingReceipt :
      Pack.HEPDataResidualProviderFirstMissingReceipt

    firstMissingReceiptIsResidualObservableClass :
      firstMissingReceipt
      ≡
      Pack.firstMissingResidualObservableClass

    intakeStatus :
      Intake.HEPDataResidualProviderPayloadIntakeStatus

    intakeStatusIsRejectedAtResidualObservableClass :
      intakeStatus
      ≡
      Intake.intakeRejectedAtFirstMissingReceipt
        Pack.firstMissingResidualObservableClass

    authorityGateStatus :
      Gate.HEPDataResidualBridgeAuthorityGateStatus

    authorityGateStatusIsBlocked :
      authorityGateStatus
      ≡
      Gate.blockedAwaitingResidualAuthorityReceiptChain

    externalizableProviderPayload :
      List String

    stillMissingProviderReceipts :
      List Pack.HEPDataResidualProviderRequiredReceipt

    stillMissingProviderReceiptsAreCanonical :
      stillMissingProviderReceipts
      ≡
      Pack.canonicalHEPDataResidualProviderRequiredReceipts

    protoReceiptBoundary :
      List String

canonicalHEPDataResidualObservableClassProtoReceipt :
  HEPDataResidualObservableClassProtoReceipt
canonicalHEPDataResidualObservableClassProtoReceipt =
  record
    { status =
        protoReceiptAssembledButAuthorityRejected
    ; candidateDiagnostic =
        Candidate.canonicalHEPDataResidualObservableClassCandidateDiagnostic
    ; providerReceiptRequestPack =
        Pack.canonicalHEPDataResidualProviderReceiptRequestPack
    ; providerPayloadIntake =
        Intake.canonicalHEPDataResidualProviderPayloadIntakeFilter
    ; residualAuthorityGate =
        Gate.canonicalHEPDataResidualBridgeAuthorityGate
    ; protoReceiptFields =
        canonicalHEPDataResidualObservableClassProtoReceiptFields
    ; protoReceiptFieldsAreCanonical =
        refl
    ; proposedClassSurface =
        Candidate.HEPDataResidualObservableClassCandidateDiagnostic.proposedClassSurface
          Candidate.canonicalHEPDataResidualObservableClassCandidateDiagnostic
    ; proposedClassSurfaceMatchesCandidate =
        refl
    ; boundProviderReceipt =
        Pack.residualObservableClassReceipt
    ; boundProviderReceiptIsResidualObservableClass =
        refl
    ; firstMissingReceipt =
        Pack.firstMissingResidualObservableClass
    ; firstMissingReceiptIsResidualObservableClass =
        refl
    ; intakeStatus =
        Intake.intakeRejectedAtFirstMissingReceipt
          Pack.firstMissingResidualObservableClass
    ; intakeStatusIsRejectedAtResidualObservableClass =
        refl
    ; authorityGateStatus =
        Gate.blockedAwaitingResidualAuthorityReceiptChain
    ; authorityGateStatusIsBlocked =
        refl
    ; externalizableProviderPayload =
        "residualObservableKind = fluctuationProfile"
        ∷ "observableName = phistar_50_76"
        ∷ "HEPData publication record = ins2079374"
        ∷ "table DOI = 10.17182/hepdata.115656.v1/t19"
        ∷ "table name = phistar mass 50-76"
        ∷ "baselineOrInvarianceModel = candidate-only adjacent-bin equality/null local-invariance baseline"
        ∷ "residualDefinition = candidate-only observed y bin0 minus observed y bin1, with diagonal-covariance normalized pull"
        ∷ "nonCollapseJustification = normalized artifact value 188.4 at x=0.002 differs from 185.09 at x=0.006; raw upstream t19 values require adapter-transform receipt"
        ∷ "authorityRouteDependency = accepted HEPData-to-ITIR authority route still missing"
        ∷ []
    ; stillMissingProviderReceipts =
        Pack.canonicalHEPDataResidualProviderRequiredReceipts
    ; stillMissingProviderReceiptsAreCanonical =
        refl
    ; protoReceiptBoundary =
        "This is a proto-receipt assembled from local candidate evidence"
        ∷ "It is externalizable as the proposed residualObservableClassReceipt payload"
        ∷ "It does not construct an accepted provider receipt"
        ∷ "It does not pass residual provider payload intake"
        ∷ "It does not construct an accepted HEPData authority route"
        ∷ "It does not construct calibration, covariance, projection, comparison-law, non-collapse witness, W3, W4, W5, or W8 promotion receipts"
        ∷ []
    }
