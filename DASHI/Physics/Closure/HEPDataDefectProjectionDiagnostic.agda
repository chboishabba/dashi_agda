module DASHI.Physics.Closure.HEPDataDefectProjectionDiagnostic where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level; Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Geometry.ProjectionDefect as PD
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic as Authority
import DASHI.Physics.Closure.HEPDataMeasurementSurfaceProjectionRejection as Projection
import DASHI.Physics.Closure.HEPDataObservableSchema as HEP

------------------------------------------------------------------------
-- HEP-R2: HEPData residual/deviation observable -> DASHI defect profile.
--
-- This module is diagnostic-only.  It records the current non-promoting
-- bridge shape for moving from an externally selected HEPData
-- residual/deviation observable into a DASHI defect/residual profile target.
-- It deliberately does not construct a selected residual observable, a
-- projection receipt, a comparison law, an authority token, or an empirical
-- validation.

private
  _≢local_ : {A : Set} → A → A → Set
  x ≢local y = x ≡ y → ⊥

data HEPDataResidualObservableReceipt : Set where

residualObservableReceiptImpossibleHere :
  HEPDataResidualObservableReceipt →
  ⊥
residualObservableReceiptImpossibleHere ()

data DASHIDefectProjectionAuthorityReceipt : Set where

defectProjectionAuthorityReceiptImpossibleHere :
  DASHIDefectProjectionAuthorityReceipt →
  ⊥
defectProjectionAuthorityReceiptImpossibleHere ()

data HEPDataDefectProjectionStatus : Set where
  blockedAwaitingResidualProfileProjectionIngredients :
    HEPDataDefectProjectionStatus

data HEPDataDefectProjectionIngredient : Set where
  residualObservableIngredient :
    HEPDataDefectProjectionIngredient
  dashiDefectCarrierTargetIngredient :
    HEPDataDefectProjectionIngredient
  nonconstantDiscriminatorIngredient :
    HEPDataDefectProjectionIngredient
  severityResidualMappingIngredient :
    HEPDataDefectProjectionIngredient
  covarianceUncertaintyPropagationIngredient :
    HEPDataDefectProjectionIngredient
  comparisonLawIngredient :
    HEPDataDefectProjectionIngredient
  authorityDependencyIngredient :
    HEPDataDefectProjectionIngredient

canonicalHEPDataDefectProjectionIngredients :
  List HEPDataDefectProjectionIngredient
canonicalHEPDataDefectProjectionIngredients =
  residualObservableIngredient
  ∷ dashiDefectCarrierTargetIngredient
  ∷ nonconstantDiscriminatorIngredient
  ∷ severityResidualMappingIngredient
  ∷ covarianceUncertaintyPropagationIngredient
  ∷ comparisonLawIngredient
  ∷ authorityDependencyIngredient
  ∷ []

data HEPDataValueProjectionBlocker : Set where
  rawValueProjectionHasNoDefectProfile :
    HEPDataValueProjectionBlocker
  constantProjectionCollapsesDiscriminator :
    HEPDataValueProjectionBlocker
  saturatedHistogramProjectionCollapsesSeverityProfile :
    HEPDataValueProjectionBlocker
  orbitSummaryProjectionCollapsesResidualProfile :
    HEPDataValueProjectionBlocker
  forcedStableCountProjectionCollapsesDeviationProfile :
    HEPDataValueProjectionBlocker
  defectResidualProfileIsNextAdmissibleTarget :
    HEPDataValueProjectionBlocker

canonicalHEPDataValueProjectionBlockers :
  List HEPDataValueProjectionBlocker
canonicalHEPDataValueProjectionBlockers =
  rawValueProjectionHasNoDefectProfile
  ∷ constantProjectionCollapsesDiscriminator
  ∷ saturatedHistogramProjectionCollapsesSeverityProfile
  ∷ orbitSummaryProjectionCollapsesResidualProfile
  ∷ forcedStableCountProjectionCollapsesDeviationProfile
  ∷ defectResidualProfileIsNextAdmissibleTarget
  ∷ []

record HEPDataDefectProjectionTarget : Setω where
  field
    DefectLevel :
      Set

    ResidualProfile :
      Set

    residualProfileLevel :
      ResidualProfile →
      Residual.ResidualLevel

    residualProfileDefectLevel :
      ResidualProfile →
      DefectLevel

    defectCarrierLevel :
      Level

    defectCarrier :
      PD.Additive defectCarrierLevel

    defectProfileLabel :
      String

record HEPDataResidualProfileProjectionContract
  (observable : HEP.HEPDataObservable)
  : Setω where
  field
    residualObservableReceipt :
      HEPDataResidualObservableReceipt

    theoremSideProjectionReceipt :
      Projection.TheoremSideMeasurementSurfaceProjectionReceipt

    comparisonLawReceipt :
      Authority.HEPDataComparisonLawReceipt observable

    authorityReceipt :
      DASHIDefectProjectionAuthorityReceipt

    target :
      HEPDataDefectProjectionTarget

    ObservableResidual :
      Set

    residualToProfile :
      ObservableResidual →
      HEPDataDefectProjectionTarget.ResidualProfile target

    discriminator :
      ObservableResidual →
      HEPDataDefectProjectionTarget.DefectLevel target

    discriminatorNonconstant :
      (x y : ObservableResidual) →
      discriminator x
      ≢local
      discriminator y →
      HEPDataDefectProjectionTarget.residualProfileDefectLevel target
        (residualToProfile x)
      ≢local
      HEPDataDefectProjectionTarget.residualProfileDefectLevel target
        (residualToProfile y)

    severityResidualMapping :
      ObservableResidual →
      Residual.ResidualLevel

    severityMappingAgreesWithProfile :
      (x : ObservableResidual) →
      severityResidualMapping x
      ≡
      HEPDataDefectProjectionTarget.residualProfileLevel target
        (residualToProfile x)

    covarianceUncertaintyPropagationLaw :
      String

    comparisonLawLabel :
      String

    comparisonLawMatchesSchemaTarget :
      comparisonLawLabel
      ≡
      HEP.HEPDataObservableSchemaSurface.comparisonLawTarget
        (HEP.HEPDataObservable.schema observable)

residualProfileProjectionContractImpossibleHere :
  {observable : HEP.HEPDataObservable} →
  HEPDataResidualProfileProjectionContract observable →
  ⊥
residualProfileProjectionContractImpossibleHere contract =
  residualObservableReceiptImpossibleHere
    (HEPDataResidualProfileProjectionContract.residualObservableReceipt
      contract)

record ConstantRawValueProjectionAttempt : Set₁ where
  field
    RawValue :
      Set

    DefectProfile :
      Set

    rawProjection :
      RawValue →
      DefectProfile

    constantProfile :
      DefectProfile

    rawProjectionIsConstant :
      (x : RawValue) →
      rawProjection x ≡ constantProfile

    leftValue :
      RawValue

    rightValue :
      RawValue

    projectedProfilesDistinct :
      rawProjection leftValue
      ≢local
      rawProjection rightValue

constantRawValueProjectionContradiction :
  ConstantRawValueProjectionAttempt →
  ⊥
constantRawValueProjectionContradiction attempt =
  ConstantRawValueProjectionAttempt.projectedProfilesDistinct attempt
    (let open ConstantRawValueProjectionAttempt attempt in
      transRaw
        (rawProjectionIsConstant leftValue)
        (symRaw (rawProjectionIsConstant rightValue)))
  where
    symRaw : {A : Set} {x y : A} → x ≡ y → y ≡ x
    symRaw refl = refl

    transRaw : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    transRaw refl refl = refl

data HEPDataDefectProjectionBoundaryToken : Set where
  diagnosticOnlyNoResidualProjectionPromotion :
    HEPDataDefectProjectionBoundaryToken

record HEPDataDefectProjectionDiagnostic : Setω where
  field
    measurementProjectionRejection :
      Projection.HEPDataMeasurementSurfaceProjectionRejection

    measurementProjectionStillRejected :
      Projection.HEPDataMeasurementSurfaceProjectionRejection.currentStatus
        measurementProjectionRejection
      ≡
      Projection.rejectedMissingProjectionContract

    status :
      HEPDataDefectProjectionStatus

    requiredIngredients :
      List HEPDataDefectProjectionIngredient

    requiredIngredientsAreCanonical :
      requiredIngredients
      ≡
      canonicalHEPDataDefectProjectionIngredients

    valueProjectionBlockers :
      List HEPDataValueProjectionBlocker

    valueProjectionBlockersAreCanonical :
      valueProjectionBlockers
      ≡
      canonicalHEPDataValueProjectionBlockers

    rawAndConstantProjectionBlocked :
      ConstantRawValueProjectionAttempt →
      ⊥

    residualProfileProjectionContractBlocked :
      {observable : HEP.HEPDataObservable} →
      HEPDataResidualProfileProjectionContract observable →
      ⊥

    defectProjectionIsNextAdmissibleTarget :
      Bool

    diagnosticBoundary :
      HEPDataDefectProjectionBoundaryToken

    nonPromotionBoundary :
      List String

    missingExternalDependency :
      String

    coordinationMapNodeText :
      String

    coordinationMapEdgeText :
      String

canonicalHEPDataDefectProjectionDiagnostic :
  HEPDataDefectProjectionDiagnostic
canonicalHEPDataDefectProjectionDiagnostic =
  record
    { measurementProjectionRejection =
        Projection.canonicalHEPDataMeasurementSurfaceProjectionRejection
    ; measurementProjectionStillRejected =
        refl
    ; status =
        blockedAwaitingResidualProfileProjectionIngredients
    ; requiredIngredients =
        canonicalHEPDataDefectProjectionIngredients
    ; requiredIngredientsAreCanonical =
        refl
    ; valueProjectionBlockers =
        canonicalHEPDataValueProjectionBlockers
    ; valueProjectionBlockersAreCanonical =
        refl
    ; rawAndConstantProjectionBlocked =
        constantRawValueProjectionContradiction
    ; residualProfileProjectionContractBlocked =
        residualProfileProjectionContractImpossibleHere
    ; defectProjectionIsNextAdmissibleTarget =
        true
    ; diagnosticBoundary =
        diagnosticOnlyNoResidualProjectionPromotion
    ; nonPromotionBoundary =
        "Raw HEPData values are not promoted to DASHI defect/residual claims"
        ∷ "Constant projections, saturated histograms, orbit summaries, and forced stable counts collapse the discriminator needed for non-forgetting projection"
        ∷ "The next admissible theorem target is a residual/defect profile with explicit severity mapping and covariance propagation"
        ∷ "No residual observable, comparison law, selected table, calibration, authority receipt, or empirical validation is fabricated here"
        ∷ []
    ; missingExternalDependency =
        "Need an externally selected residual/deviation observable plus accepted authority receipt before constructing the profile projection contract"
    ; coordinationMapNodeText =
        "rectangle \"HEP-R2\\ndefect projection diagnostic\\nresidual/deviation observable -> DASHI defect profile\\nraw/constant projection blocked\\nno theorem promotion\" as HEPDATA_HEPR2 #fef3c7"
    ; coordinationMapEdgeText =
        "HEPDATA_HEPD --> HEPDATA_HEPR2 : projection rejection retargeted to defect/residual profile\nHEPDATA_HEPR2 --> Plateau : selected residual observable + covariance propagation + comparison law + authority still required\nHEPDATA_HEPR2 --> W3 : no empirical adequacy promotion"
    }
