module DASHI.Physics.Closure.HEPDataT43DASHINativeComparisonDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataComparisonLawReceiptRequest as R31
import DASHI.Physics.Closure.HEPDataT43DASHINativeProjectionRunDiagnostic as R37

------------------------------------------------------------------------
-- HEP-R38: dirty covariance-aware comparison diagnostic.
--
-- This records a non-promoting chi2 diagnostic computed from the dirty
-- HEP-R37 projection artifact and the checksum-bound t44 covariance matrix.
-- It is useful as a model-gap measure only.  It is not an accepted comparison
-- law because HEP-R37 is not clean-frozen and the comparison was not promoted
-- through HEP-R31.

data HEPDataT43DASHINativeComparisonDiagnosticStatus : Set where
  dirtyDiagnosticComparisonFailsByLargeGap :
    HEPDataT43DASHINativeComparisonDiagnosticStatus

data HEPDataT43DASHINativeComparisonDiagnosticField : Set where
  projectionArtifactDigest :
    HEPDataT43DASHINativeComparisonDiagnosticField
  covarianceSourceT44 :
    HEPDataT43DASHINativeComparisonDiagnosticField
  inverseCovarianceMethod :
    HEPDataT43DASHINativeComparisonDiagnosticField
  chi2Value :
    HEPDataT43DASHINativeComparisonDiagnosticField
  dofValue :
    HEPDataT43DASHINativeComparisonDiagnosticField
  chi2PerDofValue :
    HEPDataT43DASHINativeComparisonDiagnosticField
  residualRange :
    HEPDataT43DASHINativeComparisonDiagnosticField
  firstPullValues :
    HEPDataT43DASHINativeComparisonDiagnosticField

canonicalHEPDataT43DASHINativeComparisonDiagnosticFields :
  List HEPDataT43DASHINativeComparisonDiagnosticField
canonicalHEPDataT43DASHINativeComparisonDiagnosticFields =
  projectionArtifactDigest
  ∷ covarianceSourceT44
  ∷ inverseCovarianceMethod
  ∷ chi2Value
  ∷ dofValue
  ∷ chi2PerDofValue
  ∷ residualRange
  ∷ firstPullValues
  ∷ []

data HEPDataT43DASHINativeComparisonGapInterpretation : Set where
  currentSigmaDASHINormalizationScaleMismatch :
    HEPDataT43DASHINativeComparisonGapInterpretation
  currentFiniteTritProjectionNotAcceptedEmpiricalModel :
    HEPDataT43DASHINativeComparisonGapInterpretation
  refineProjectionBeforeComparisonLawIntake :
    HEPDataT43DASHINativeComparisonGapInterpretation

canonicalHEPDataT43DASHINativeComparisonGapInterpretations :
  List HEPDataT43DASHINativeComparisonGapInterpretation
canonicalHEPDataT43DASHINativeComparisonGapInterpretations =
  currentSigmaDASHINormalizationScaleMismatch
  ∷ currentFiniteTritProjectionNotAcceptedEmpiricalModel
  ∷ refineProjectionBeforeComparisonLawIntake
  ∷ []

data HEPDataT43DASHINativeComparisonDiagnosticBoundary : Set where
  dirtyProjectionArtifactOnly :
    HEPDataT43DASHINativeComparisonDiagnosticBoundary
  noAcceptedChi2Receipt :
    HEPDataT43DASHINativeComparisonDiagnosticBoundary
  noAcceptedComparisonLaw :
    HEPDataT43DASHINativeComparisonDiagnosticBoundary
  noEmpiricalAdequacyClaim :
    HEPDataT43DASHINativeComparisonDiagnosticBoundary
  noW3W4W5W8Promotion :
    HEPDataT43DASHINativeComparisonDiagnosticBoundary

canonicalHEPDataT43DASHINativeComparisonDiagnosticBoundaries :
  List HEPDataT43DASHINativeComparisonDiagnosticBoundary
canonicalHEPDataT43DASHINativeComparisonDiagnosticBoundaries =
  dirtyProjectionArtifactOnly
  ∷ noAcceptedChi2Receipt
  ∷ noAcceptedComparisonLaw
  ∷ noEmpiricalAdequacyClaim
  ∷ noW3W4W5W8Promotion
  ∷ []

data HEPDataAcceptedT43ComparisonLawReceipt : Set where

acceptedT43ComparisonLawReceiptImpossibleHere :
  HEPDataAcceptedT43ComparisonLawReceipt →
  ⊥
acceptedT43ComparisonLawReceiptImpossibleHere ()

record HEPDataT43DASHINativeComparisonDiagnostic : Setω where
  field
    status :
      HEPDataT43DASHINativeComparisonDiagnosticStatus

    projectionRunDiagnostic :
      R37.HEPDataT43DASHINativeProjectionRunDiagnostic

    comparisonLawReceiptRequest :
      R31.HEPDataComparisonLawReceiptRequest

    dirtyDiagnosticComputed :
      Bool

    dirtyDiagnosticComputedIsTrue :
      dirtyDiagnosticComputed ≡ true

    acceptedComparisonLawExistsHere :
      Bool

    acceptedComparisonLawExistsHereIsFalse :
      acceptedComparisonLawExistsHere ≡ false

    nBins :
      Nat

    nBinsIs18 :
      nBins ≡ 18

    chi2String :
      String

    dofString :
      String

    chi2PerDofString :
      String

    covarianceMethodString :
      String

    residualRangeString :
      String

    firstThreePullsString :
      String

    diagnosticFields :
      List HEPDataT43DASHINativeComparisonDiagnosticField

    diagnosticFieldsAreCanonical :
      diagnosticFields
      ≡
      canonicalHEPDataT43DASHINativeComparisonDiagnosticFields

    gapInterpretations :
      List HEPDataT43DASHINativeComparisonGapInterpretation

    gapInterpretationsAreCanonical :
      gapInterpretations
      ≡
      canonicalHEPDataT43DASHINativeComparisonGapInterpretations

    boundaries :
      List HEPDataT43DASHINativeComparisonDiagnosticBoundary

    boundariesAreCanonical :
      boundaries
      ≡
      canonicalHEPDataT43DASHINativeComparisonDiagnosticBoundaries

    futureAcceptedComparisonLawBlocked :
      HEPDataAcceptedT43ComparisonLawReceipt →
      ⊥

canonicalHEPDataT43DASHINativeComparisonDiagnostic :
  HEPDataT43DASHINativeComparisonDiagnostic
canonicalHEPDataT43DASHINativeComparisonDiagnostic =
  record
    { status =
        dirtyDiagnosticComparisonFailsByLargeGap
    ; projectionRunDiagnostic =
        R37.canonicalHEPDataT43DASHINativeProjectionRunDiagnostic
    ; comparisonLawReceiptRequest =
        R31.canonicalHEPDataComparisonLawReceiptRequest
    ; dirtyDiagnosticComputed =
        true
    ; dirtyDiagnosticComputedIsTrue =
        refl
    ; acceptedComparisonLawExistsHere =
        false
    ; acceptedComparisonLawExistsHereIsFalse =
        refl
    ; nBins =
        18
    ; nBinsIs18 =
        refl
    ; chi2String =
        "6402144.431093033"
    ; dofString =
        "18"
    ; chi2PerDofString =
        "355674.6906162796"
    ; covarianceMethodString =
        "inverse of t44 Total uncertainty covariance matrix"
    ; residualRangeString =
        "0.877355159718522 to 0.9086506463845561"
    ; firstThreePullsString =
        "1587.2338127262133, 1722.710595531962, 1704.2250745901044"
    ; diagnosticFields =
        canonicalHEPDataT43DASHINativeComparisonDiagnosticFields
    ; diagnosticFieldsAreCanonical =
        refl
    ; gapInterpretations =
        canonicalHEPDataT43DASHINativeComparisonGapInterpretations
    ; gapInterpretationsAreCanonical =
        refl
    ; boundaries =
        canonicalHEPDataT43DASHINativeComparisonDiagnosticBoundaries
    ; boundariesAreCanonical =
        refl
    ; futureAcceptedComparisonLawBlocked =
        acceptedT43ComparisonLawReceiptImpossibleHere
    }

canonicalHEPDataT43DASHINativeComparisonDiagnosticStatus :
  HEPDataT43DASHINativeComparisonDiagnosticStatus
canonicalHEPDataT43DASHINativeComparisonDiagnosticStatus =
  HEPDataT43DASHINativeComparisonDiagnostic.status
    canonicalHEPDataT43DASHINativeComparisonDiagnostic
