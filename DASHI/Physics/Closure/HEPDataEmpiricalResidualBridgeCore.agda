module DASHI.Physics.Closure.HEPDataEmpiricalResidualBridgeCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataDefectProjectionDiagnostic as R2
import DASHI.Physics.Closure.HEPDataNonCollapseObservableObligation as R5
import DASHI.Physics.Closure.HEPDataResidualComparisonLawRequest as R6
import DASHI.Physics.Closure.HEPDataResidualObservableClassRequest as R1

------------------------------------------------------------------------
-- HEP-R7: empirical residual bridge core.
--
-- This is the missing minimal, generic bridge surface between the residual
-- observable request path and the residual-to-defect comparison path.  It is
-- deliberately non-promoting: it constructs no HEPData selected observable, no
-- HEPData/provider receipt, no calibration or authority receipt, no accepted
-- empirical token, and no W3/W4/W5/W8 promotion.

private
  _≢local_ : {A : Set} → A → A → Set
  x ≢local y = x ≡ y → ⊥

data HEPDataEmpiricalResidualBridgeCoreStatus : Set where
  blockedAwaitingExternalResidualBridgeReceipts :
    HEPDataEmpiricalResidualBridgeCoreStatus

data HEPDataResidualBridgeCoreIngredient : Set where
  residualObservableSurfaceIngredient :
    HEPDataResidualBridgeCoreIngredient
  baselineOrInvarianceSurfaceIngredient :
    HEPDataResidualBridgeCoreIngredient
  nonCollapseWitnessIngredient :
    HEPDataResidualBridgeCoreIngredient
  defectProjectionSurfaceIngredient :
    HEPDataResidualBridgeCoreIngredient
  residualToDefectComparisonLawIngredient :
    HEPDataResidualBridgeCoreIngredient
  soundnessBoundaryIngredient :
    HEPDataResidualBridgeCoreIngredient

canonicalHEPDataResidualBridgeCoreIngredients :
  List HEPDataResidualBridgeCoreIngredient
canonicalHEPDataResidualBridgeCoreIngredients =
  residualObservableSurfaceIngredient
  ∷ baselineOrInvarianceSurfaceIngredient
  ∷ nonCollapseWitnessIngredient
  ∷ defectProjectionSurfaceIngredient
  ∷ residualToDefectComparisonLawIngredient
  ∷ soundnessBoundaryIngredient
  ∷ []

data HEPDataResidualBridgeCoreBoundary : Set where
  noHEPDataSelectedObservableConstructed :
    HEPDataResidualBridgeCoreBoundary
  noHEPDataProviderReceiptConstructed :
    HEPDataResidualBridgeCoreBoundary
  noCalibrationOrAuthorityReceiptConstructed :
    HEPDataResidualBridgeCoreBoundary
  noEmpiricalAdequacyOrPromotionClaim :
    HEPDataResidualBridgeCoreBoundary
  noW3W4W5W8Promotion :
    HEPDataResidualBridgeCoreBoundary

canonicalHEPDataResidualBridgeCoreBoundary :
  List HEPDataResidualBridgeCoreBoundary
canonicalHEPDataResidualBridgeCoreBoundary =
  noHEPDataSelectedObservableConstructed
  ∷ noHEPDataProviderReceiptConstructed
  ∷ noCalibrationOrAuthorityReceiptConstructed
  ∷ noEmpiricalAdequacyOrPromotionClaim
  ∷ noW3W4W5W8Promotion
  ∷ []

record ResidualObservable : Set₁ where
  field
    Observation :
      Set

    ObservedValue :
      Set

    ResidualProfile :
      Set

    observationValue :
      Observation →
      ObservedValue

    residualProfile :
      Observation →
      ResidualProfile

    observableLabel :
      String

record BaselineOrInvariance
  (observable : ResidualObservable)
  : Set₁ where
  open ResidualObservable observable
  field
    BaselineValue :
      Set

    InvarianceWitness :
      Set

    baselineValue :
      Observation →
      BaselineValue

    residualFromBaseline :
      ObservedValue →
      BaselineValue →
      ResidualProfile

    residualAgreesWithBaseline :
      (x : Observation) →
      residualFromBaseline
        (observationValue x)
        (baselineValue x)
      ≡
      residualProfile x

    invarianceWitness :
      Observation →
      InvarianceWitness

    invariancePreservesBaseline :
      (x y : Observation) →
      invarianceWitness x ≡ invarianceWitness y →
      baselineValue x ≡ baselineValue y

    baselineOrInvarianceLabel :
      String

record NonCollapseWitness
  (observable : ResidualObservable)
  : Set₁ where
  open ResidualObservable observable
  field
    DefectDiscriminator :
      Set

    leftObservation :
      Observation

    rightObservation :
      Observation

    observationsDistinct :
      leftObservation ≢local rightObservation

    residualProfilesDistinct :
      residualProfile leftObservation
      ≢local
      residualProfile rightObservation

    defectDiscriminator :
      Observation →
      DefectDiscriminator

    defectDiscriminatorDistinct :
      defectDiscriminator leftObservation
      ≢local
      defectDiscriminator rightObservation

    defectDiscriminatorPreservedByResidual :
      (x y : Observation) →
      defectDiscriminator x
      ≢local
      defectDiscriminator y →
      residualProfile x
      ≢local
      residualProfile y

record DefectProjection
  (observable : ResidualObservable)
  (witness : NonCollapseWitness observable)
  : Set₁ where
  open ResidualObservable observable
  open NonCollapseWitness witness
  field
    DefectProfile :
      Set

    Severity :
      Set

    projectDefect :
      ResidualProfile →
      DefectProfile

    defectSeverity :
      DefectProfile →
      Severity

    projectedDiscriminator :
      DefectProfile →
      DefectDiscriminator

    projectionPreservesWitnessDiscriminator :
      (x : Observation) →
      projectedDiscriminator
        (projectDefect (residualProfile x))
      ≡
      defectDiscriminator x

    projectionPreservesNonCollapse :
      projectedDiscriminator
        (projectDefect (residualProfile leftObservation))
      ≢local
      projectedDiscriminator
        (projectDefect (residualProfile rightObservation))

record ResidualToDefectComparisonLaw
  (observable : ResidualObservable)
  (witness : NonCollapseWitness observable)
  (projection : DefectProjection observable witness)
  : Set₁ where
  open ResidualObservable observable
  open DefectProjection projection
  field
    residualComparison :
      ResidualProfile →
      ResidualProfile →
      Set

    defectComparison :
      DefectProfile →
      DefectProfile →
      Set

    comparisonSound :
      (x y : Observation) →
      residualComparison
        (residualProfile x)
        (residualProfile y) →
      defectComparison
        (projectDefect (residualProfile x))
        (projectDefect (residualProfile y))

    comparisonLawLabel :
      String

record HEPDataEmpiricalResidualBridgeCore : Setω where
  field
    residualObservable :
      ResidualObservable

    baselineOrInvariance :
      BaselineOrInvariance residualObservable

    nonCollapseWitness :
      NonCollapseWitness residualObservable

    defectProjection :
      DefectProjection residualObservable nonCollapseWitness

    residualToDefectComparisonLaw :
      ResidualToDefectComparisonLaw
        residualObservable
        nonCollapseWitness
        defectProjection

    status :
      HEPDataEmpiricalResidualBridgeCoreStatus

    nonPromoting :
      status ≡ blockedAwaitingExternalResidualBridgeReceipts

record HEPDataEmpiricalResidualBridgeCoreDiagnostic : Setω where
  field
    residualObservableClassRequest :
      R1.HEPDataResidualObservableClassRequestDiagnostic

    defectProjectionDiagnostic :
      R2.HEPDataDefectProjectionDiagnostic

    nonCollapseObservableObligation :
      R5.HEPDataNonCollapseObservableObligationDiagnostic

    residualComparisonLawRequest :
      R6.HEPDataResidualComparisonLawRequestDiagnostic

    status :
      HEPDataEmpiricalResidualBridgeCoreStatus

    requiredIngredients :
      List HEPDataResidualBridgeCoreIngredient

    requiredIngredientsAreCanonical :
      requiredIngredients
      ≡
      canonicalHEPDataResidualBridgeCoreIngredients

    hasSelectedHEPDataObservable :
      Bool

    constructsHEPDataReceipt :
      Bool

    constructsEmpiricalPromotion :
      Bool

    nonPromotionBoundary :
      List HEPDataResidualBridgeCoreBoundary

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary
      ≡
      canonicalHEPDataResidualBridgeCoreBoundary

    exactMissingExternalSurfaces :
      List String

    canonicalDiagnostic :
      String

    coordinationMapNodeText :
      String

    coordinationMapEdgeText :
      String

canonicalHEPDataEmpiricalResidualBridgeCoreDiagnostic :
  HEPDataEmpiricalResidualBridgeCoreDiagnostic
canonicalHEPDataEmpiricalResidualBridgeCoreDiagnostic =
  record
    { residualObservableClassRequest =
        R1.canonicalHEPDataResidualObservableClassRequestDiagnostic
    ; defectProjectionDiagnostic =
        R2.canonicalHEPDataDefectProjectionDiagnostic
    ; nonCollapseObservableObligation =
        R5.canonicalHEPDataNonCollapseObservableObligationDiagnostic
    ; residualComparisonLawRequest =
        R6.canonicalHEPDataResidualComparisonLawRequestDiagnostic
    ; status =
        blockedAwaitingExternalResidualBridgeReceipts
    ; requiredIngredients =
        canonicalHEPDataResidualBridgeCoreIngredients
    ; requiredIngredientsAreCanonical =
        refl
    ; hasSelectedHEPDataObservable =
        false
    ; constructsHEPDataReceipt =
        false
    ; constructsEmpiricalPromotion =
        false
    ; nonPromotionBoundary =
        canonicalHEPDataResidualBridgeCoreBoundary
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; exactMissingExternalSurfaces =
        "external selected residual observable receipt remains absent"
        ∷ "baseline or invariance model receipt remains absent"
        ∷ "provider non-collapse witness remains absent"
        ∷ "defect projection receipt remains absent"
        ∷ "residual-aware comparison law receipt remains absent"
        ∷ "accepted authority, calibration, and empirical promotion receipts remain absent"
        ∷ []
    ; canonicalDiagnostic =
        "HEP-R7 records the generic residual observable -> baseline/invariance -> non-collapse witness -> defect projection -> comparison soundness shape only; it is blocked and non-promoting"
    ; coordinationMapNodeText =
        "rectangle \"HEP-R7\\nempirical residual bridge core\\nresidual observable + baseline/invariance\\nnon-collapse witness + defect projection\\ncomparison soundness only\\nnon-promoting\" as HEPDATA_HEPR7 #fef3c7"
    ; coordinationMapEdgeText =
        "HEPDATA_HEPR1 --> HEPDATA_HEPR7 : residual observable surface feeds generic core\nHEPDATA_HEPR5 --> HEPDATA_HEPR7 : non-collapse witness required before projection is meaningful\nHEPDATA_HEPR2 --> HEPDATA_HEPR7 : defect projection surface supplies residual-to-defect target shape\nHEPDATA_HEPR6 --> HEPDATA_HEPR7 : residual-aware comparison law supplies soundness target\nHEPDATA_HEPR7 --> Plateau : blocked; no selected observable, receipt chain, authority, calibration, or empirical promotion\nHEPDATA_HEPR7 --> W3 : no accepted-authority promotion\nHEPDATA_HEPR7 --> W4 : no calibration promotion\nHEPDATA_HEPR7 --> W5 : no empirical compatibility promotion\nHEPDATA_HEPR7 --> W8 : no origin receipt promotion"
    }

canonicalHEPDataEmpiricalResidualBridgeCoreStatus :
  HEPDataEmpiricalResidualBridgeCoreStatus
canonicalHEPDataEmpiricalResidualBridgeCoreStatus =
  blockedAwaitingExternalResidualBridgeReceipts
