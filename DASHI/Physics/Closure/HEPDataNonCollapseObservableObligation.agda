module DASHI.Physics.Closure.HEPDataNonCollapseObservableObligation where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataDefectProjectionDiagnostic as R2
import DASHI.Physics.Closure.HEPDataObservableSchema as HEP
import DASHI.Physics.Closure.HEPDataResidualObservableClassRequest as R1

------------------------------------------------------------------------
-- HEP-R5: non-collapse observable obligation.
--
-- This module is a future receipt target only.  It states the typed shape a
-- HEPData residual/deviation observable must satisfy before it can separate
-- admissible residual/defect profiles from raw, constant, or saturated
-- projections.  It constructs no external witness, no authority token, no
-- comparison receipt, no covariance receipt, and no empirical compatibility.

private
  _≢local_ : {A : Set} → A → A → Set
  x ≢local y = x ≡ y → ⊥

data HEPDataExternalNonCollapseWitnessReceipt : Set where

externalNonCollapseWitnessReceiptImpossibleHere :
  HEPDataExternalNonCollapseWitnessReceipt →
  ⊥
externalNonCollapseWitnessReceiptImpossibleHere ()

data HEPDataNonCollapseObligationStatus : Set where
  blockedAwaitingExternalNonCollapseWitness :
    HEPDataNonCollapseObligationStatus

data HEPDataNonCollapseObservationKind : Set where
  observationPair :
    HEPDataNonCollapseObservationKind
  binPair :
    HEPDataNonCollapseObservationKind

data HEPDataUncertaintyCovarianceAdequacyLabel : Set where
  covarianceAdequacyPendingExternalReceipt :
    HEPDataUncertaintyCovarianceAdequacyLabel
  covarianceAdequateForResidualComparison :
    HEPDataUncertaintyCovarianceAdequacyLabel
  covarianceInadequateRawProjection :
    HEPDataUncertaintyCovarianceAdequacyLabel

data HEPDataNonCollapseRequiredField : Set where
  requiredTwoObservationsOrBins :
    HEPDataNonCollapseRequiredField
  requiredResidualProfileDistinction :
    HEPDataNonCollapseRequiredField
  requiredNotConstantProofTarget :
    HEPDataNonCollapseRequiredField
  requiredDefectDiscriminatorPreservation :
    HEPDataNonCollapseRequiredField
  requiredUncertaintyCovarianceAdequacyLabel :
    HEPDataNonCollapseRequiredField
  requiredComparisonLawCompatibility :
    HEPDataNonCollapseRequiredField
  requiredAuthorityDependency :
    HEPDataNonCollapseRequiredField

canonicalHEPDataNonCollapseRequiredFields :
  List HEPDataNonCollapseRequiredField
canonicalHEPDataNonCollapseRequiredFields =
  requiredTwoObservationsOrBins
  ∷ requiredResidualProfileDistinction
  ∷ requiredNotConstantProofTarget
  ∷ requiredDefectDiscriminatorPreservation
  ∷ requiredUncertaintyCovarianceAdequacyLabel
  ∷ requiredComparisonLawCompatibility
  ∷ requiredAuthorityDependency
  ∷ []

data HEPDataCollapsedProjectionFamily : Set where
  rawProjection :
    HEPDataCollapsedProjectionFamily
  constantProjection :
    HEPDataCollapsedProjectionFamily
  saturatedHistogramProjection :
    HEPDataCollapsedProjectionFamily
  orbitSummaryProjection :
    HEPDataCollapsedProjectionFamily
  forcedStableCountProjection :
    HEPDataCollapsedProjectionFamily

canonicalHEPDataCollapsedProjectionFamilies :
  List HEPDataCollapsedProjectionFamily
canonicalHEPDataCollapsedProjectionFamilies =
  rawProjection
  ∷ constantProjection
  ∷ saturatedHistogramProjection
  ∷ orbitSummaryProjection
  ∷ forcedStableCountProjection
  ∷ []

record ConstantResidualProfileAttempt
  (ObservationOrBin ResidualProfile : Set)
  (residualProfile : ObservationOrBin → ResidualProfile)
  : Set₁ where
  field
    leftObservation :
      ObservationOrBin

    rightObservation :
      ObservationOrBin

    constantProfile :
      ResidualProfile

    leftProjectsToConstant :
      residualProfile leftObservation ≡ constantProfile

    rightProjectsToConstant :
      residualProfile rightObservation ≡ constantProfile

    residualProfilesDistinct :
      residualProfile leftObservation
      ≢local
      residualProfile rightObservation

constantResidualProfileContradiction :
  {ObservationOrBin ResidualProfile : Set}
  {residualProfile : ObservationOrBin → ResidualProfile} →
  ConstantResidualProfileAttempt
    ObservationOrBin
    ResidualProfile
    residualProfile →
  ⊥
constantResidualProfileContradiction attempt =
  ConstantResidualProfileAttempt.residualProfilesDistinct attempt
    (let open ConstantResidualProfileAttempt attempt in
      transLocal
        leftProjectsToConstant
        (symLocal rightProjectsToConstant))
  where
    symLocal : {A : Set} {x y : A} → x ≡ y → y ≡ x
    symLocal refl = refl

    transLocal : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    transLocal refl refl = refl

record HEPDataNonCollapseAuthorityDependency : Set where
  field
    providerReceiptDependency :
      String

    acceptedDatasetAuthorityDependency :
      String

    comparisonLawDependency :
      String

    covarianceReceiptDependency :
      String

record HEPDataNonCollapseWitness
  (observable : HEP.HEPDataObservable)
  : Setω where
  field
    ObservationOrBin :
      Set

    ResidualProfile :
      Set

    DefectDiscriminator :
      Set

    observationKind :
      HEPDataNonCollapseObservationKind

    leftObservation :
      ObservationOrBin

    rightObservation :
      ObservationOrBin

    observationsOrBinsDistinct :
      leftObservation ≢local rightObservation

    residualProfile :
      ObservationOrBin →
      ResidualProfile

    residualProfileDistinction :
      residualProfile leftObservation
      ≢local
      residualProfile rightObservation

    notConstantProofTarget :
      ConstantResidualProfileAttempt
        ObservationOrBin
        ResidualProfile
        residualProfile →
      ⊥

    defectDiscriminator :
      ObservationOrBin →
      DefectDiscriminator

    defectDiscriminatorDistinction :
      defectDiscriminator leftObservation
      ≢local
      defectDiscriminator rightObservation

    defectDiscriminatorPreservation :
      (x y : ObservationOrBin) →
      defectDiscriminator x
      ≢local
      defectDiscriminator y →
      residualProfile x
      ≢local
      residualProfile y

    uncertaintyCovarianceAdequacy :
      HEPDataUncertaintyCovarianceAdequacyLabel

    uncertaintyCovarianceAdequacyJustification :
      String

    comparisonLawLabel :
      String

    comparisonLawMatchesSchemaTarget :
      comparisonLawLabel
      ≡
      HEP.HEPDataObservableSchemaSurface.comparisonLawTarget
        (HEP.HEPDataObservable.schema observable)

    authorityDependency :
      HEPDataNonCollapseAuthorityDependency

record HEPDataNonCollapseWitnessReceiptTarget
  (observable : HEP.HEPDataObservable)
  : Setω where
  field
    externalNonCollapseWitnessReceipt :
      HEPDataExternalNonCollapseWitnessReceipt

    nonCollapseWitness :
      HEPDataNonCollapseWitness observable

nonCollapseWitnessReceiptTargetImpossibleHere :
  {observable : HEP.HEPDataObservable} →
  HEPDataNonCollapseWitnessReceiptTarget observable →
  ⊥
nonCollapseWitnessReceiptTargetImpossibleHere target =
  externalNonCollapseWitnessReceiptImpossibleHere
    (HEPDataNonCollapseWitnessReceiptTarget.externalNonCollapseWitnessReceipt
      target)

record HEPDataNonCollapseObservableObligationDiagnostic : Setω where
  field
    residualObservableClassRequest :
      R1.HEPDataResidualObservableClassRequestDiagnostic

    defectProjectionDiagnostic :
      R2.HEPDataDefectProjectionDiagnostic

    status :
      HEPDataNonCollapseObligationStatus

    requiredFields :
      List HEPDataNonCollapseRequiredField

    requiredFieldsAreCanonical :
      requiredFields
      ≡
      canonicalHEPDataNonCollapseRequiredFields

    collapsedProjectionFamiliesBlocked :
      List HEPDataCollapsedProjectionFamily

    collapsedProjectionFamiliesAreCanonical :
      collapsedProjectionFamiliesBlocked
      ≡
      canonicalHEPDataCollapsedProjectionFamilies

    currentRepoHasExternalWitness :
      Bool

    externalWitnessImpossibleHere :
      HEPDataExternalNonCollapseWitnessReceipt →
      ⊥

    receiptTargetImpossibleHere :
      {observable : HEP.HEPDataObservable} →
      HEPDataNonCollapseWitnessReceiptTarget observable →
      ⊥

    canonicalDiagnostic :
      String

    providerInstructions :
      List String

    missingExternalWitness :
      String

    nonPromotionBoundary :
      List String

    coordinationMapNodeText :
      String

    coordinationMapEdgeText :
      String

canonicalHEPDataNonCollapseObservableObligationDiagnostic :
  HEPDataNonCollapseObservableObligationDiagnostic
canonicalHEPDataNonCollapseObservableObligationDiagnostic =
  record
    { residualObservableClassRequest =
        R1.canonicalHEPDataResidualObservableClassRequestDiagnostic
    ; defectProjectionDiagnostic =
        R2.canonicalHEPDataDefectProjectionDiagnostic
    ; status =
        blockedAwaitingExternalNonCollapseWitness
    ; requiredFields =
        canonicalHEPDataNonCollapseRequiredFields
    ; requiredFieldsAreCanonical =
        refl
    ; collapsedProjectionFamiliesBlocked =
        canonicalHEPDataCollapsedProjectionFamilies
    ; collapsedProjectionFamiliesAreCanonical =
        refl
    ; currentRepoHasExternalWitness =
        false
    ; externalWitnessImpossibleHere =
        externalNonCollapseWitnessReceiptImpossibleHere
    ; receiptTargetImpossibleHere =
        nonCollapseWitnessReceiptTargetImpossibleHere
    ; canonicalDiagnostic =
        "current repo has no external HEPData non-collapse witness; residual observable remains a typed obligation, not an empirical compatibility or promotion receipt"
    ; providerInstructions =
        "Supply two selected observations or bins bound to the HEPData selection receipt"
        ∷ "Show the residual/deviation profiles differ on those observations or bins"
        ∷ "Supply the not-constant proof target excluding raw, constant, saturated, orbit-summary, and forced-stable-count projections"
        ∷ "Show the defect discriminator distinction is preserved by the residual profile"
        ∷ "Label uncertainty/covariance adequacy and bind it to the comparison law target"
        ∷ "Name the accepted provider, covariance, comparison-law, and dataset-authority dependencies"
        ∷ []
    ; missingExternalWitness =
        "Need provider-supplied non-collapse witness: two selected observations/bins, distinct residual profiles, preserved defect discriminator, covariance adequacy label, comparison-law compatibility, and accepted authority dependency"
    ; nonPromotionBoundary =
        "No HEPDataExternalNonCollapseWitnessReceipt is inhabited in this module"
        ∷ "No selected residual observable is promoted from raw, constant, saturated, orbit-summary, or forced-stable-count projections"
        ∷ "No covariance adequacy, comparison law, accepted authority, or empirical compatibility is claimed"
        ∷ "This obligation is a future provider receipt target compatible with HEP-R1 and HEP-R2 diagnostics only"
        ∷ []
    ; coordinationMapNodeText =
        "rectangle \"HEP-R5\\nnon-collapse observable obligation\\ntwo bins/observations + residual profile distinction\\ndefect discriminator preserved\\nno external witness present\" as HEPDATA_HEPR5 #fef3c7"
    ; coordinationMapEdgeText =
        "HEPDATA_HEPR1 --> HEPDATA_HEPR5 : residual/deviation class must supply non-collapse witness\nHEPDATA_HEPR2 --> HEPDATA_HEPR5 : defect projection requires preserved discriminator\nHEPDATA_HEPC --> HEPDATA_HEPR5 : uncertainty/covariance adequacy dependency\nHEPDATA_HEPE --> HEPDATA_HEPR5 : comparison law + accepted authority dependency\nHEPDATA_HEPR5 --> Plateau : blocked until provider non-collapse witness receipt exists\nHEPDATA_HEPR5 --> W3 : no accepted-authority promotion\nHEPDATA_HEPR5 --> W4 : no covariance/calibration promotion\nHEPDATA_HEPR5 --> W5 : no empirical compatibility promotion"
    }

canonicalHEPDataNonCollapseObservableObligationStatus :
  HEPDataNonCollapseObligationStatus
canonicalHEPDataNonCollapseObservableObligationStatus =
  blockedAwaitingExternalNonCollapseWitness
