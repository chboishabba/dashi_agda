module DASHI.Physics.Closure.ZhengKolkowitz2023PublicDataReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (_+_; _*_; _≤ᵇ_)

------------------------------------------------------------------------
-- ZHENG / KOLKOWITZ 2023 PUBLIC-DATA CLOCK-NETWORK RECEIPT
--
-- Source authority:
--   Zheng et al., Nature Communications 14, 4886 (2023),
--   DOI 10.1038/s41467-023-40629-8.
--   The article states that the process data for the study are deposited at
--   Zenodo DOI 10.5281/zenodo.8184043 and that control/analysis/simulation
--   code is available from the corresponding author upon request.
--
-- Zenodo authority is limited to artifact identity, file names, sizes and the
-- repository-published MD5 values below. DASHI owns the scaled-integer
-- comparison arithmetic and the decision to use this experiment as an
-- independent rehearsal of the generic ingestion architecture.
--
-- This experiment is NOT substituted for missing Bothwell/Ye 2022 arrays,
-- covariance or code merely because both are optical-clock redshift tests.
------------------------------------------------------------------------

articleDOI : String
articleDOI = "10.1038/s41467-023-40629-8"

zenodoDOI : String
zenodoDOI = "10.5281/zenodo.8184043"

zenodoVersion : String
zenodoVersion = "v1; published 2023-07-25"

record PublicProcessDataFile : Set where
  field
    fileName : String
    sourceMD5 : String
    sourceSize : String

open PublicProcessDataFile public

fig1 : PublicProcessDataFile
fig1 = record
  { fileName = "Fig1.csv"
  ; sourceMD5 = "a829e2044f0ef2dd450435d7b790e8c7"
  ; sourceSize = "25.6 kB"
  }

fig2 : PublicProcessDataFile
fig2 = record
  { fileName = "Fig2.csv"
  ; sourceMD5 = "8edb5d957e81a07b07e9d350afe43e3a"
  ; sourceSize = "2.9 kB"
  }

fig3 : PublicProcessDataFile
fig3 = record
  { fileName = "Fig3.csv"
  ; sourceMD5 = "257eab6f29cf3480c536cac73ed3998a"
  ; sourceSize = "958 Bytes"
  }

fig4 : PublicProcessDataFile
fig4 = record
  { fileName = "Fig4.csv"
  ; sourceMD5 = "53987b91b94d75d844f865ac0a778e75"
  ; sourceSize = "369 Bytes"
  }

canonicalPublicProcessDataFiles : List PublicProcessDataFile
canonicalPublicProcessDataFiles = fig1 ∷ fig2 ∷ fig3 ∷ fig4 ∷ []

fiveEnsembleClockNetwork : Bool
fiveEnsembleClockNetwork = true

totalVerticalSpanMillimetres : Nat
totalVerticalSpanMillimetres = 10

ensembleSpacingTenthsMillimetres : Nat
ensembleSpacingTenthsMillimetres = 25

-- Common signed-magnitude scale: tenths of 1e-19 / cm.
publishedMeasuredGradientTenthsE19PerCm : Nat
publishedMeasuredGradientTenthsE19PerCm = 124

publishedStatUncertaintyTenthsE19PerCm : Nat
publishedStatUncertaintyTenthsE19PerCm = 7

publishedSystematicUncertaintyTenthsE19PerCm : Nat
publishedSystematicUncertaintyTenthsE19PerCm = 25

publishedExpectedGradientTenthsE19PerCm : Nat
publishedExpectedGradientTenthsE19PerCm = 109

publishedAbsoluteResidualTenthsE19PerCm : Nat
publishedAbsoluteResidualTenthsE19PerCm = 15

canonicalMeasuredExpectedResidual :
  publishedMeasuredGradientTenthsE19PerCm ≡
  publishedExpectedGradientTenthsE19PerCm + publishedAbsoluteResidualTenthsE19PerCm
canonicalMeasuredExpectedResidual = refl

-- DASHI reconstruction only: residual^2 <= stat^2 + sys^2 on the published
-- rounded numbers. This is a compact consistency check, not a reanalysis of
-- the experiment and not a claim about an unpublished covariance model.
residualSquared : Nat
residualSquared = publishedAbsoluteResidualTenthsE19PerCm * publishedAbsoluteResidualTenthsE19PerCm

quotedQuadratureBudgetSquared : Nat
quotedQuadratureBudgetSquared =
  publishedStatUncertaintyTenthsE19PerCm * publishedStatUncertaintyTenthsE19PerCm
  + publishedSystematicUncertaintyTenthsE19PerCm * publishedSystematicUncertaintyTenthsE19PerCm

publishedRoundedConsistencyCheck : Bool
publishedRoundedConsistencyCheck = residualSquared ≤ᵇ quotedQuadratureBudgetSquared

canonicalPublishedRoundedConsistencyCheck : publishedRoundedConsistencyCheck ≡ true
canonicalPublishedRoundedConsistencyCheck = refl

record ZhengKolkowitz2023PublicDataReceipt : Set where
  field
    sourceArticleDOI : String
    publicDataDOI : String
    publicFiles : List PublicProcessDataFile

    fiveEnsembleClockNetwork : Bool
    fiveEnsembleClockNetworkIsTrue : fiveEnsembleClockNetwork ≡ true

    publicProcessDataManifestIngested : Bool
    publicProcessDataManifestIngestedIsTrue :
      publicProcessDataManifestIngested ≡ true

    sourcePublishedConsistencyReconstructed : Bool
    sourcePublishedConsistencyReconstructedIsTrue :
      sourcePublishedConsistencyReconstructed ≡ true

    datasetBytesMaterialisedInRepo : Bool
    datasetBytesMaterialisedInRepoIsFalse :
      datasetBytesMaterialisedInRepo ≡ false

    numericalReplayCompleted : Bool
    numericalReplayCompletedIsFalse : numericalReplayCompleted ≡ false

    analysisCodePubliclyAvailable : Bool
    analysisCodePubliclyAvailableIsFalse :
      analysisCodePubliclyAvailable ≡ false

    analysisCodeAvailableOnRequest : Bool
    analysisCodeAvailableOnRequestIsTrue :
      analysisCodeAvailableOnRequest ≡ true

    doesNotFillBothwellYeRawRows : Bool
    doesNotFillBothwellYeRawRowsIsTrue : doesNotFillBothwellYeRawRows ≡ true

    reading : List String

open ZhengKolkowitz2023PublicDataReceipt public

canonicalZhengKolkowitz2023PublicDataReceipt : ZhengKolkowitz2023PublicDataReceipt
canonicalZhengKolkowitz2023PublicDataReceipt = record
  { sourceArticleDOI = articleDOI
  ; publicDataDOI = zenodoDOI
  ; publicFiles = canonicalPublicProcessDataFiles
  ; fiveEnsembleClockNetwork = true
  ; fiveEnsembleClockNetworkIsTrue = refl
  ; publicProcessDataManifestIngested = true
  ; publicProcessDataManifestIngestedIsTrue = refl
  ; sourcePublishedConsistencyReconstructed = publishedRoundedConsistencyCheck
  ; sourcePublishedConsistencyReconstructedIsTrue = canonicalPublishedRoundedConsistencyCheck
  ; datasetBytesMaterialisedInRepo = false
  ; datasetBytesMaterialisedInRepoIsFalse = refl
  ; numericalReplayCompleted = false
  ; numericalReplayCompletedIsFalse = refl
  ; analysisCodePubliclyAvailable = false
  ; analysisCodePubliclyAvailableIsFalse = refl
  ; analysisCodeAvailableOnRequest = true
  ; analysisCodeAvailableOnRequestIsTrue = refl
  ; doesNotFillBothwellYeRawRows = true
  ; doesNotFillBothwellYeRawRowsIsTrue = refl
  ; reading =
      "Zheng et al. report a blinded five-ensemble 87Sr clock-network redshift test spanning 1 cm, with a measured gradient -12.4 +/- 0.7(stat) +/- 2.5(sys) x 1e-19/cm and expected -10.9 x 1e-19/cm."
      ∷ "Zenodo DOI 10.5281/zenodo.8184043 publicly exposes process-data files for Figures 1-4 with source-published MD5 identities."
      ∷ "DASHI's squared-residual check on the rounded published values is repository reconstruction; it is not attributed to the authors as their statistical method."
      ∷ "The public-data manifest is useful as an independent ingestion/replay rehearsal, but it cannot substitute for the still-missing Bothwell/Ye 2022 raw arrays, covariance treatment or analysis code."
      ∷ []
  }
