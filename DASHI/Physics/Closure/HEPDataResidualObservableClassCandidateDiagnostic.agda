module DASHI.Physics.Closure.HEPDataResidualObservableClassCandidateDiagnostic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataExternalResidualWitnessCandidateDiagnostic as Candidate
import DASHI.Physics.Closure.HEPDataResidualObservableClassRequest as Class
import DASHI.Physics.Closure.HEPDataResidualProviderReceiptRequestPack as Pack

------------------------------------------------------------------------
-- HEPData residual observable class candidate diagnostic.
--
-- This module narrows the phistar_50_76 local evidence pointer into a concrete
-- residual observable-class candidate.  It is still not a provider receipt:
-- the class is proposed as a fluctuation profile under an adjacent-bin
-- local-invariance baseline, but no accepted authority route, calibration,
-- projection contract, comparison law, or promotion token is constructed.

data HEPDataResidualObservableClassCandidateStatus : Set where
  phistarClassCandidateFoundButReceiptMissing :
    HEPDataResidualObservableClassCandidateStatus

data HEPDataResidualObservableClassCandidateField : Set where
  classCandidateKind :
    HEPDataResidualObservableClassCandidateField
  classCandidateBaseline :
    HEPDataResidualObservableClassCandidateField
  classCandidateResidualDefinition :
    HEPDataResidualObservableClassCandidateField
  classCandidateCovarianceHandling :
    HEPDataResidualObservableClassCandidateField
  classCandidateSelectionDependency :
    HEPDataResidualObservableClassCandidateField
  classCandidateCalibrationDependency :
    HEPDataResidualObservableClassCandidateField
  classCandidateProjectionTarget :
    HEPDataResidualObservableClassCandidateField
  classCandidateComparisonTarget :
    HEPDataResidualObservableClassCandidateField
  classCandidateNonCollapseJustification :
    HEPDataResidualObservableClassCandidateField
  classCandidateFirstMissingReceipt :
    HEPDataResidualObservableClassCandidateField

canonicalHEPDataResidualObservableClassCandidateFields :
  List HEPDataResidualObservableClassCandidateField
canonicalHEPDataResidualObservableClassCandidateFields =
  classCandidateKind
  ∷ classCandidateBaseline
  ∷ classCandidateResidualDefinition
  ∷ classCandidateCovarianceHandling
  ∷ classCandidateSelectionDependency
  ∷ classCandidateCalibrationDependency
  ∷ classCandidateProjectionTarget
  ∷ classCandidateComparisonTarget
  ∷ classCandidateNonCollapseJustification
  ∷ classCandidateFirstMissingReceipt
  ∷ []

record HEPDataResidualObservableClassCandidateDiagnostic : Setω where
  field
    status :
      HEPDataResidualObservableClassCandidateStatus

    requestDiagnostic :
      Class.HEPDataResidualObservableClassRequestDiagnostic

    witnessCandidateDiagnostic :
      Candidate.HEPDataExternalResidualWitnessCandidateDiagnostic

    candidateFields :
      List HEPDataResidualObservableClassCandidateField

    candidateFieldsAreCanonical :
      candidateFields
      ≡
      canonicalHEPDataResidualObservableClassCandidateFields

    proposedClassSurface :
      Class.HEPDataResidualObservableClassRequestSurface

    proposedKindIsFluctuationProfile :
      Class.HEPDataResidualObservableClassRequestSurface.residualObservableKind
        proposedClassSurface
      ≡
      Class.fluctuationProfile

    proposedBaselineMatchesWitness :
      Class.HEPDataResidualObservableClassRequestSurface.baselineOrInvarianceModel
        proposedClassSurface
      ≡
      Candidate.HEPDataExternalResidualWitnessCandidateDiagnostic.baselineOrInvarianceModel
        witnessCandidateDiagnostic

    proposedResidualDefinitionMatchesWitness :
      Class.HEPDataResidualObservableClassRequestSurface.residualDefinition
        proposedClassSurface
      ≡
      Candidate.HEPDataExternalResidualWitnessCandidateDiagnostic.residualDefinition
        witnessCandidateDiagnostic

    providerFirstMissingReceipt :
      Pack.HEPDataResidualProviderFirstMissingReceipt

    providerFirstMissingReceiptIsResidualObservableClass :
      providerFirstMissingReceipt
      ≡
      Pack.firstMissingResidualObservableClass

    candidateReceiptBoundary :
      List String

canonicalHEPDataResidualObservableClassCandidateDiagnostic :
  HEPDataResidualObservableClassCandidateDiagnostic
canonicalHEPDataResidualObservableClassCandidateDiagnostic =
  record
    { status =
        phistarClassCandidateFoundButReceiptMissing
    ; requestDiagnostic =
        Class.canonicalHEPDataResidualObservableClassRequestDiagnostic
    ; witnessCandidateDiagnostic =
        Candidate.canonicalHEPDataExternalResidualWitnessCandidateDiagnostic
    ; candidateFields =
        canonicalHEPDataResidualObservableClassCandidateFields
    ; candidateFieldsAreCanonical =
        refl
    ; proposedClassSurface =
        record
          { residualObservableKind =
              Class.fluctuationProfile
          ; baselineOrInvarianceModel =
              Candidate.HEPDataExternalResidualWitnessCandidateDiagnostic.baselineOrInvarianceModel
                Candidate.canonicalHEPDataExternalResidualWitnessCandidateDiagnostic
          ; residualDefinition =
              Candidate.HEPDataExternalResidualWitnessCandidateDiagnostic.residualDefinition
                Candidate.canonicalHEPDataExternalResidualWitnessCandidateDiagnostic
          ; uncertaintyOrCovarianceHandling =
              "candidate-only diagonal covariance pull from bins 0 and 1; full covariance authority and conditioning receipt still missing"
          ; selectionReceiptDependency =
              "candidate depends on HEPData publication record ins2079374 / DOI 10.17182/hepdata.115656.v1/t19 / phistar_50_76 bins 0 and 1 plus normalized local artifact; checksum-bound adapter selection receipt still missing"
          ; calibrationDependency =
              "calibration/covariance receipt still missing; no unit or physical calibration promotion"
          ; projectionTarget =
              "theorem-side residual/deviation to DASHI defect profile target still missing as receipt"
          ; comparisonLawTarget =
              "candidate normalized-pull or adjacent-bin residual comparison law; provider-grade comparison receipt still missing"
          ; nonCollapseJustification =
              "normalized-artifact candidate y values differ: 188.4 at x=0.002 versus 185.09 at x=0.006, delta 3.3100000000000023; raw upstream t19 values are recorded in HEPDataEmpiricalAuthorityReceiptCollation"
          }
    ; proposedKindIsFluctuationProfile =
        refl
    ; proposedBaselineMatchesWitness =
        refl
    ; proposedResidualDefinitionMatchesWitness =
        refl
    ; providerFirstMissingReceipt =
        Pack.firstMissingResidualObservableClass
    ; providerFirstMissingReceiptIsResidualObservableClass =
        refl
    ; candidateReceiptBoundary =
        "This module proposes a residual observable class candidate only"
        ∷ "It does not construct residualObservableClassReceipt"
        ∷ "It does not construct exact selected observable, checksum-bound selection, baseline receipt, residual-definition receipt, non-collapse witness receipt, calibration/covariance receipt, projection receipt, comparison-law receipt, or accepted authority route"
        ∷ "It does not promote W3, W4, W5, or W8"
        ∷ []
    }
