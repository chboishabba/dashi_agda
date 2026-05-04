module DASHI.Physics.Closure.HEPDataT43ProjectionRunnerContract where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataDASHIProjectionRunnerDiscovery as R25
import DASHI.Physics.Closure.HEPDataPredictionFreezeProjectionRunRequest as R22

------------------------------------------------------------------------
-- HEP-R29: executable digest-bound DASHI t43 projection runner contract.
--
-- This module is a request/receipt skeleton only.  Current discovery says no
-- accepted exact t43 projection runner is present here.  The skeleton names
-- what such a runner must read and emit, but it does not freeze a prediction,
-- calculate an accepted projection digest, construct a projection receipt,
-- construct a comparison law, or promote W3/W4/W5/W8. HEP-R32 may supply a
-- fail-closed script implementation attempt without satisfying this receipt.

data HEPDataT43ProjectionRunnerContractStatus : Set where
  contractSkeletonOnlyNoExecutableRunnerHere :
    HEPDataT43ProjectionRunnerContractStatus

data HEPDataT43ProjectionRunnerInput : Set where
  inputT43CSV :
    HEPDataT43ProjectionRunnerInput
  inputPredictionFixedAt :
    HEPDataT43ProjectionRunnerInput
  inputFrozenPredictionArtifact :
    HEPDataT43ProjectionRunnerInput
  inputNonCollapsePreRegistration :
    HEPDataT43ProjectionRunnerInput

canonicalHEPDataT43ProjectionRunnerInputs :
  List HEPDataT43ProjectionRunnerInput
canonicalHEPDataT43ProjectionRunnerInputs =
  inputT43CSV
  ∷ inputPredictionFixedAt
  ∷ inputFrozenPredictionArtifact
  ∷ inputNonCollapsePreRegistration
  ∷ []

data HEPDataT43ProjectionRunnerOutputField : Set where
  outputInputDigest :
    HEPDataT43ProjectionRunnerOutputField
  outputBinBindings :
    HEPDataT43ProjectionRunnerOutputField
  outputRDashi :
    HEPDataT43ProjectionRunnerOutputField
  outputRData :
    HEPDataT43ProjectionRunnerOutputField
  outputProjectionDigest :
    HEPDataT43ProjectionRunnerOutputField

canonicalHEPDataT43ProjectionRunnerOutputFields :
  List HEPDataT43ProjectionRunnerOutputField
canonicalHEPDataT43ProjectionRunnerOutputFields =
  outputInputDigest
  ∷ outputBinBindings
  ∷ outputRDashi
  ∷ outputRData
  ∷ outputProjectionDigest
  ∷ []

data HEPDataT43ProjectionRunnerBoundary : Set where
  noAcceptedExactRunnerImplementationHere :
    HEPDataT43ProjectionRunnerBoundary
  noPredictionFixedAtReceiptHere :
    HEPDataT43ProjectionRunnerBoundary
  noConcreteInputDigestHere :
    HEPDataT43ProjectionRunnerBoundary
  noConcreteProjectionDigestHere :
    HEPDataT43ProjectionRunnerBoundary
  noProjectionReceiptHere :
    HEPDataT43ProjectionRunnerBoundary
  noComparisonLawHere :
    HEPDataT43ProjectionRunnerBoundary
  noPromotionHere :
    HEPDataT43ProjectionRunnerBoundary

canonicalHEPDataT43ProjectionRunnerBoundaries :
  List HEPDataT43ProjectionRunnerBoundary
canonicalHEPDataT43ProjectionRunnerBoundaries =
  noAcceptedExactRunnerImplementationHere
  ∷ noPredictionFixedAtReceiptHere
  ∷ noConcreteInputDigestHere
  ∷ noConcreteProjectionDigestHere
  ∷ noProjectionReceiptHere
  ∷ noComparisonLawHere
  ∷ noPromotionHere
  ∷ []

data HEPDataT43ProjectionRunnerReceipt : Set where

t43ProjectionRunnerReceiptImpossibleHere :
  HEPDataT43ProjectionRunnerReceipt →
  ⊥
t43ProjectionRunnerReceiptImpossibleHere ()

record HEPDataT43ProjectionRunnerContract : Setω where
  field
    status :
      HEPDataT43ProjectionRunnerContractStatus

    runnerDiscovery :
      R25.HEPDataDASHIProjectionRunnerDiscoveryDiagnostic

    predictionRunRequest :
      R22.HEPDataPredictionFreezeProjectionRunRequestSurface

    discoverySaysNoExactRunner :
      R25.HEPDataDASHIProjectionRunnerDiscoveryDiagnostic.exactRunnerExistsHere
        runnerDiscovery
      ≡
      false

    predictionRequestStillBlocked :
      R22.HEPDataPredictionFreezeProjectionRunRequestSurface.currentStatus
        predictionRunRequest
      ≡
      R22.blockedAwaitingInternalPredictionFreezeAndProjectionRun

    acceptedExactRunnerExistsHere :
      Bool

    acceptedExactRunnerExistsHereIsFalse :
      acceptedExactRunnerExistsHere ≡ false

    requiredInputs :
      List HEPDataT43ProjectionRunnerInput

    requiredInputsAreCanonical :
      requiredInputs ≡ canonicalHEPDataT43ProjectionRunnerInputs

    outputFileName :
      String

    outputFileNameIsT43ProjectionJSON :
      outputFileName ≡ "t43_projection.json"

    requiredOutputFields :
      List HEPDataT43ProjectionRunnerOutputField

    requiredOutputFieldsAreCanonical :
      requiredOutputFields
      ≡
      canonicalHEPDataT43ProjectionRunnerOutputFields

    requiredInputFieldNames :
      List String

    requiredOutputFieldNames :
      List String

    runnerContractText :
      List String

    nonPromotionBoundary :
      List HEPDataT43ProjectionRunnerBoundary

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary
      ≡
      canonicalHEPDataT43ProjectionRunnerBoundaries

    futureReceiptBlocked :
      HEPDataT43ProjectionRunnerReceipt →
      ⊥

canonicalHEPDataT43ProjectionRunnerContract :
  HEPDataT43ProjectionRunnerContract
canonicalHEPDataT43ProjectionRunnerContract =
  record
    { status =
        contractSkeletonOnlyNoExecutableRunnerHere
    ; runnerDiscovery =
        R25.canonicalHEPDataDASHIProjectionRunnerDiscoveryDiagnostic
    ; predictionRunRequest =
        R22.canonicalHEPDataPredictionFreezeProjectionRunRequestSurface
    ; discoverySaysNoExactRunner =
        refl
    ; predictionRequestStillBlocked =
        refl
    ; acceptedExactRunnerExistsHere =
        false
    ; acceptedExactRunnerExistsHereIsFalse =
        refl
    ; requiredInputs =
        canonicalHEPDataT43ProjectionRunnerInputs
    ; requiredInputsAreCanonical =
        refl
    ; outputFileName =
        "t43_projection.json"
    ; outputFileNameIsT43ProjectionJSON =
        refl
    ; requiredOutputFields =
        canonicalHEPDataT43ProjectionRunnerOutputFields
    ; requiredOutputFieldsAreCanonical =
        refl
    ; requiredInputFieldNames =
        "t43CSV : checksum-bound HEPData t43 ratio CSV"
        ∷ "predictionFixedAt : accepted commit/hash identity for the frozen DASHI prediction"
        ∷ "predictionArtifact : digest-bound frozen prediction artifact consumed by the runner"
        ∷ "nonCollapsePreRegistration : criterion fixed before reading projection output"
        ∷ []
    ; requiredOutputFieldNames =
        "inputDigest : digest covering the t43 CSV, predictionFixedAt, prediction artifact, and runner configuration"
        ∷ "binBindings : exact t43 bin identifiers/ranges bound to each output row"
        ∷ "R_dashi : DASHI-projected ratio value per bound t43 bin"
        ∷ "R_data : HEPData t43 ratio value per bound t43 bin"
        ∷ "projectionDigest : digest of t43_projection.json and runner code identity"
        ∷ []
    ; runnerContractText =
        "The future executable runner must read the checksum-bound HEPData t43 CSV"
        ∷ "The future executable runner must consume an accepted predictionFixedAt identity before projection"
        ∷ "The future executable runner must emit t43_projection.json with inputDigest, binBindings, R_dashi, R_data, and projectionDigest"
        ∷ "This module supplies no concrete digest, no projected ratio values, and no accepted exact projection-runner receipt"
        ∷ []
    ; nonPromotionBoundary =
        canonicalHEPDataT43ProjectionRunnerBoundaries
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; futureReceiptBlocked =
        t43ProjectionRunnerReceiptImpossibleHere
    }

canonicalHEPDataT43ProjectionRunnerOutputFile :
  String
canonicalHEPDataT43ProjectionRunnerOutputFile =
  HEPDataT43ProjectionRunnerContract.outputFileName
    canonicalHEPDataT43ProjectionRunnerContract
