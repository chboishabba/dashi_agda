module DASHI.Physics.Closure.HEPDataMassWindowGeneralPredictionRunDiagnostic where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataMassWindowGeneralPredictionLawDiagnostic as R43

------------------------------------------------------------------------
-- HEP-R44: dirty run of the fresh mass-window-general predictor.
--
-- HEP-R43 created a non-promoting mass-window-general law request after the
-- HEP-R42 t45/t46 holdout failure.  HEP-R44 runs the fresh Python predictor:
--
--   DASHI.Physics.Prediction.sigma_dashi_mass_general
--
-- against both checksum-bound ratio/covariance pairs:
--
--   t43/t44 = 50-76 / 76-106
--   t45/t46 = 106-170 / 76-106
--
-- The result is diagnostic failure on both surfaces.  The t43 overprediction
-- is catastrophic, while the t45 surface is closer than the previous holdout
-- failure but still far above the acceptance threshold.  This is a model-gap
-- signal only; it constructs no accepted comparison law.

data HEPDataMassWindowGeneralPredictionRunStatus : Set where
  massWindowGeneralDirtyRunFailsBothTargets :
    HEPDataMassWindowGeneralPredictionRunStatus

data HEPDataMassWindowGeneralPredictionRunField : Set where
  freshMassGeneralPredictor :
    HEPDataMassWindowGeneralPredictionRunField
  t43DirtyRunFailed :
    HEPDataMassWindowGeneralPredictionRunField
  t45DirtyRunFailed :
    HEPDataMassWindowGeneralPredictionRunField
  t43OverpredictionIsCatastrophic :
    HEPDataMassWindowGeneralPredictionRunField
  t45StillAboveAcceptanceThreshold :
    HEPDataMassWindowGeneralPredictionRunField
  noComparisonLawConstructed :
    HEPDataMassWindowGeneralPredictionRunField

canonicalHEPDataMassWindowGeneralPredictionRunFields :
  List HEPDataMassWindowGeneralPredictionRunField
canonicalHEPDataMassWindowGeneralPredictionRunFields =
  freshMassGeneralPredictor
  ∷ t43DirtyRunFailed
  ∷ t45DirtyRunFailed
  ∷ t43OverpredictionIsCatastrophic
  ∷ t45StillAboveAcceptanceThreshold
  ∷ noComparisonLawConstructed
  ∷ []

data HEPDataMassWindowGeneralPredictionRunBoundary : Set where
  dirtySyntheticFreezeOnly :
    HEPDataMassWindowGeneralPredictionRunBoundary
  noAcceptedProjectionReceiptHere :
    HEPDataMassWindowGeneralPredictionRunBoundary
  noAcceptedComparisonLawHere :
    HEPDataMassWindowGeneralPredictionRunBoundary
  noEmpiricalAdequacyHere :
    HEPDataMassWindowGeneralPredictionRunBoundary
  noW3W4W5W8PromotionHere :
    HEPDataMassWindowGeneralPredictionRunBoundary

canonicalHEPDataMassWindowGeneralPredictionRunBoundaries :
  List HEPDataMassWindowGeneralPredictionRunBoundary
canonicalHEPDataMassWindowGeneralPredictionRunBoundaries =
  dirtySyntheticFreezeOnly
  ∷ noAcceptedProjectionReceiptHere
  ∷ noAcceptedComparisonLawHere
  ∷ noEmpiricalAdequacyHere
  ∷ noW3W4W5W8PromotionHere
  ∷ []

data HEPDataMassWindowGeneralAcceptedRunReceipt : Set where

hepR44AcceptedRunReceiptImpossibleHere :
  HEPDataMassWindowGeneralAcceptedRunReceipt →
  ⊥
hepR44AcceptedRunReceiptImpossibleHere ()

record HEPDataMassWindowGeneralPredictionRunDiagnostic : Setω where
  field
    status :
      HEPDataMassWindowGeneralPredictionRunStatus

    upstreamLawDiagnostic :
      R43.HEPDataMassWindowGeneralPredictionLawDiagnostic

    predictionAPI :
      String

    predictionAPIIsCanonical :
      predictionAPI
      ≡
      "DASHI.Physics.Prediction.sigma_dashi_mass_general"

    t43DirtyArtifactPath :
      String

    t43DirtyArtifactPathIsCanonical :
      t43DirtyArtifactPath
      ≡
      "/tmp/t43_projection_hep_r43_mass_general_dirty.json"

    t43DirtyArtifactSHA256 :
      String

    t43DirtyArtifactSHA256IsCanonical :
      t43DirtyArtifactSHA256
      ≡
      "235e289e79d9aca474fbb16ddf8dd11359ff4c9e807d07d032e4e9e15dedb359"

    t43ProjectionDigest :
      String

    t43ProjectionDigestIsCanonical :
      t43ProjectionDigest
      ≡
      "ba9b9f821d1a17ab3c3d9f175081f260665efc5ebc795bedcb2a5479700c678d"

    t43Chi2PerDofString :
      String

    t43Chi2PerDofStringIsCanonical :
      t43Chi2PerDofString
      ≡
      "1770377.845008375"

    t43ResidualRangeString :
      String

    t43ResidualRangeStringIsCanonical :
      t43ResidualRangeString
      ≡
      "1.8459953092439472 to 2.5122180535409937"

    t45DirtyArtifactPath :
      String

    t45DirtyArtifactPathIsCanonical :
      t45DirtyArtifactPath
      ≡
      "/tmp/t45_projection_hep_r43_mass_general_dirty.json"

    t45DirtyArtifactSHA256 :
      String

    t45DirtyArtifactSHA256IsCanonical :
      t45DirtyArtifactSHA256
      ≡
      "301c64668a47404b0bc8d75ce79542795f974633ce3fb02df4e851b8be503171"

    t45ProjectionDigest :
      String

    t45ProjectionDigestIsCanonical :
      t45ProjectionDigest
      ≡
      "8adc2d9d5cc764123be371b3d428169356579802b77be46847ea5bfeb6bc5927"

    t45Chi2PerDofString :
      String

    t45Chi2PerDofStringIsCanonical :
      t45Chi2PerDofString
      ≡
      "122.01665676644487"

    t45ResidualRangeString :
      String

    t45ResidualRangeStringIsCanonical :
      t45ResidualRangeString
      ≡
      "0.005827674966932275 to 0.009752982373518255"

    acceptedComparisonLawExistsHere :
      Bool

    acceptedComparisonLawExistsHereIsFalse :
      acceptedComparisonLawExistsHere ≡ false

    runFields :
      List HEPDataMassWindowGeneralPredictionRunField

    runFieldsAreCanonical :
      runFields
      ≡
      canonicalHEPDataMassWindowGeneralPredictionRunFields

    boundaries :
      List HEPDataMassWindowGeneralPredictionRunBoundary

    boundariesAreCanonical :
      boundaries
      ≡
      canonicalHEPDataMassWindowGeneralPredictionRunBoundaries

    futureAcceptedRunReceiptBlocked :
      HEPDataMassWindowGeneralAcceptedRunReceipt →
      ⊥

canonicalHEPDataMassWindowGeneralPredictionRunDiagnostic :
  HEPDataMassWindowGeneralPredictionRunDiagnostic
canonicalHEPDataMassWindowGeneralPredictionRunDiagnostic =
  record
    { status =
        massWindowGeneralDirtyRunFailsBothTargets
    ; upstreamLawDiagnostic =
        R43.canonicalHEPDataMassWindowGeneralPredictionLawDiagnostic
    ; predictionAPI =
        "DASHI.Physics.Prediction.sigma_dashi_mass_general"
    ; predictionAPIIsCanonical =
        refl
    ; t43DirtyArtifactPath =
        "/tmp/t43_projection_hep_r43_mass_general_dirty.json"
    ; t43DirtyArtifactPathIsCanonical =
        refl
    ; t43DirtyArtifactSHA256 =
        "235e289e79d9aca474fbb16ddf8dd11359ff4c9e807d07d032e4e9e15dedb359"
    ; t43DirtyArtifactSHA256IsCanonical =
        refl
    ; t43ProjectionDigest =
        "ba9b9f821d1a17ab3c3d9f175081f260665efc5ebc795bedcb2a5479700c678d"
    ; t43ProjectionDigestIsCanonical =
        refl
    ; t43Chi2PerDofString =
        "1770377.845008375"
    ; t43Chi2PerDofStringIsCanonical =
        refl
    ; t43ResidualRangeString =
        "1.8459953092439472 to 2.5122180535409937"
    ; t43ResidualRangeStringIsCanonical =
        refl
    ; t45DirtyArtifactPath =
        "/tmp/t45_projection_hep_r43_mass_general_dirty.json"
    ; t45DirtyArtifactPathIsCanonical =
        refl
    ; t45DirtyArtifactSHA256 =
        "301c64668a47404b0bc8d75ce79542795f974633ce3fb02df4e851b8be503171"
    ; t45DirtyArtifactSHA256IsCanonical =
        refl
    ; t45ProjectionDigest =
        "8adc2d9d5cc764123be371b3d428169356579802b77be46847ea5bfeb6bc5927"
    ; t45ProjectionDigestIsCanonical =
        refl
    ; t45Chi2PerDofString =
        "122.01665676644487"
    ; t45Chi2PerDofStringIsCanonical =
        refl
    ; t45ResidualRangeString =
        "0.005827674966932275 to 0.009752982373518255"
    ; t45ResidualRangeStringIsCanonical =
        refl
    ; acceptedComparisonLawExistsHere =
        false
    ; acceptedComparisonLawExistsHereIsFalse =
        refl
    ; runFields =
        canonicalHEPDataMassWindowGeneralPredictionRunFields
    ; runFieldsAreCanonical =
        refl
    ; boundaries =
        canonicalHEPDataMassWindowGeneralPredictionRunBoundaries
    ; boundariesAreCanonical =
        refl
    ; futureAcceptedRunReceiptBlocked =
        hepR44AcceptedRunReceiptImpossibleHere
    }

canonicalHEPDataMassWindowGeneralPredictionRunStatus :
  HEPDataMassWindowGeneralPredictionRunStatus
canonicalHEPDataMassWindowGeneralPredictionRunStatus =
  HEPDataMassWindowGeneralPredictionRunDiagnostic.status
    canonicalHEPDataMassWindowGeneralPredictionRunDiagnostic
