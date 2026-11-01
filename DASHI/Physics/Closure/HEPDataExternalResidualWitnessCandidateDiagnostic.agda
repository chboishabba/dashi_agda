module DASHI.Physics.Closure.HEPDataExternalResidualWitnessCandidateDiagnostic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataExternalResidualWitnessPayload as Payload
import DASHI.Physics.Closure.HEPDataResidualProviderReceiptRequestPack as Pack

------------------------------------------------------------------------
-- HEPData external residual witness candidate diagnostic.
--
-- This module records the current best local candidate for the concrete
-- nonCollapseWitnessReceipt payload.  It is evidence-pointer grade only:
-- checksums and two non-identical local bins are named, but the provider-grade
-- residual observable class, authority route, and external non-collapse
-- receipt are still absent.

data HEPDataExternalResidualWitnessCandidateStatus : Set where
  localCandidateFoundButProviderReceiptMissing :
    HEPDataExternalResidualWitnessCandidateStatus

data HEPDataExternalResidualWitnessCandidateField : Set where
  candidateRecordIdentity :
    HEPDataExternalResidualWitnessCandidateField
  candidateLocalArtifact :
    HEPDataExternalResidualWitnessCandidateField
  candidateSourceNPZ :
    HEPDataExternalResidualWitnessCandidateField
  candidateMetricsArtifact :
    HEPDataExternalResidualWitnessCandidateField
  candidateCertificationArtifact :
    HEPDataExternalResidualWitnessCandidateField
  candidateObservationPair :
    HEPDataExternalResidualWitnessCandidateField
  candidateResidualDefinition :
    HEPDataExternalResidualWitnessCandidateField
  candidateNonCollapseDelta :
    HEPDataExternalResidualWitnessCandidateField
  candidateFirstMissingReceipt :
    HEPDataExternalResidualWitnessCandidateField

canonicalHEPDataExternalResidualWitnessCandidateFields :
  List HEPDataExternalResidualWitnessCandidateField
canonicalHEPDataExternalResidualWitnessCandidateFields =
  candidateRecordIdentity
  ∷ candidateLocalArtifact
  ∷ candidateSourceNPZ
  ∷ candidateMetricsArtifact
  ∷ candidateCertificationArtifact
  ∷ candidateObservationPair
  ∷ candidateResidualDefinition
  ∷ candidateNonCollapseDelta
  ∷ candidateFirstMissingReceipt
  ∷ []

record ChecksumedLocalArtifact : Set where
  field
    path :
      String

    digestAlgorithm :
      String

    digestValue :
      String

record CandidateObservationOrBin : Set where
  field
    binIndex :
      String

    xValue :
      String

    yValue :
      String

    covarianceDiagonal :
      String

record HEPDataExternalResidualWitnessCandidateDiagnostic : Setω where
  field
    status :
      HEPDataExternalResidualWitnessCandidateStatus

    payloadDiagnostic :
      Payload.HEPDataExternalResidualWitnessPayloadDiagnostic

    candidateFields :
      List HEPDataExternalResidualWitnessCandidateField

    candidateFieldsAreCanonical :
      candidateFields
      ≡
      canonicalHEPDataExternalResidualWitnessCandidateFields

    sourceRecordId :
      String

    sourceTableDoi :
      String

    sourceTableName :
      String

    sourceRecordDescription :
      String

    localArtifact :
      ChecksumedLocalArtifact

    sourceNPZ :
      ChecksumedLocalArtifact

    sourceMetricsCSV :
      ChecksumedLocalArtifact

    sourceCertificationJSON :
      ChecksumedLocalArtifact

    leftObservation :
      CandidateObservationOrBin

    rightObservation :
      CandidateObservationOrBin

    baselineOrInvarianceModel :
      String

    residualDefinition :
      String

    candidateResidualDelta :
      String

    candidateNormalizedPull :
      String

    candidateNonCollapseSummary :
      String

    providerFirstMissingReceipt :
      Pack.HEPDataResidualProviderFirstMissingReceipt

    providerFirstMissingReceiptIsResidualObservableClass :
      providerFirstMissingReceipt
      ≡
      Pack.firstMissingResidualObservableClass

    nonPromotionBoundary :
      List String

canonicalHEPDataExternalResidualWitnessCandidateDiagnostic :
  HEPDataExternalResidualWitnessCandidateDiagnostic
canonicalHEPDataExternalResidualWitnessCandidateDiagnostic =
  record
    { status =
        localCandidateFoundButProviderReceiptMissing
    ; payloadDiagnostic =
        Payload.canonicalHEPDataExternalResidualWitnessPayloadDiagnostic
    ; candidateFields =
        canonicalHEPDataExternalResidualWitnessCandidateFields
    ; candidateFieldsAreCanonical =
        refl
    ; sourceRecordId =
        "HEPData publication record ins2079374; local normalized artifact derived from phistar_50_76"
    ; sourceTableDoi =
        "10.17182/hepdata.115656.v1/t19"
    ; sourceTableName =
        "phistar mass 50-76"
    ; sourceRecordDescription =
        "CMS Drell-Yan 13 TeV differential cross section in the 50 <= M_ll < 76 GeV mass window, binned in phi*"
    ; localArtifact =
        record
          { path =
              "scripts/data/hepdata_phistar_50_76_artifact.json"
          ; digestAlgorithm =
              "sha256"
          ; digestValue =
              "20085dc6092e59a6afc381cb0bf2f03da2d19f375a22a0f9e701d7c890244139"
          }
    ; sourceNPZ =
        record
          { path =
              "../dashifine/hepdata_npz/phistar_50_76.npz"
          ; digestAlgorithm =
              "sha256"
          ; digestValue =
              "2676cda932eba7e8c0570d05fc896604c82e2961088a1ba89a56e856c0cb39c5"
          }
    ; sourceMetricsCSV =
        record
          { path =
              "../dashifine/hepdata_dashi_native/phistar_50_76_dashi_native_metrics.csv"
          ; digestAlgorithm =
              "sha256"
          ; digestValue =
              "95d004d650d95bc9ff58d3cbc8dcff90efbdf172db88edf57696bbeafeb1ee1c"
          }
    ; sourceCertificationJSON =
        record
          { path =
              "../dashifine/hepdata_lyapunov_test_out_new/overall_certification.json"
          ; digestAlgorithm =
              "sha256"
          ; digestValue =
              "abeb7ed706f8c4c3192da92954d5be0f2fe6e1ec1fdefa7db6b1943f7b364bc3"
          }
    ; leftObservation =
        record
          { binIndex =
              "0"
          ; xValue =
              "0.002"
          ; yValue =
              "188.4"
          ; covarianceDiagonal =
              "15.158"
          }
    ; rightObservation =
        record
          { binIndex =
              "1"
          ; xValue =
              "0.006"
          ; yValue =
              "185.09"
          ; covarianceDiagonal =
              "13.626"
          }
    ; baselineOrInvarianceModel =
        "candidate-only adjacent-bin equality/null local-invariance baseline"
    ; residualDefinition =
        "candidate-only observed y bin0 minus observed y bin1, with diagonal-covariance normalized pull"
    ; candidateResidualDelta =
        "3.3100000000000023"
    ; candidateNormalizedPull =
        "0.6169534835701825"
    ; candidateNonCollapseSummary =
        "bin0 and bin1 have distinct y values under the normalized-artifact candidate residual delta, so this is a local non-collapsing evidence pointer"
    ; providerFirstMissingReceipt =
        Pack.firstMissingResidualObservableClass
    ; providerFirstMissingReceiptIsResidualObservableClass =
        refl
    ; nonPromotionBoundary =
        "This candidate does not construct HEPDataExternalNonCollapseWitnessReceipt"
        ∷ "This candidate does not satisfy residualObservableClassReceipt"
        ∷ "This candidate does not supply an accepted authority route"
        ∷ "This candidate does not promote W3, W4, W5, or W8"
        ∷ "This candidate uses normalized local artifact values; HEPDataEmpiricalAuthorityReceiptCollation records the raw upstream t19 values and the adapter-transform gap"
        ∷ "The named residual definition is candidate-only and still needs provider-grade baseline, covariance, projection, comparison-law, and authority receipts"
        ∷ []
    }
