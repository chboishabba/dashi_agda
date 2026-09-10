module DASHI.Astronomy.LocalGroupFirstLightBenchmarkReceiptExact where

open import DASHI.Core.Prelude
open import DASHI.Astronomy.LocalGroupObservationFrameProvenanceExact
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Exact-payment surface for converting an attributed benchmark claim into an
-- independently reproduced DASHI result.  This module does not assert that
-- any receipt has yet been paid.
------------------------------------------------------------------------

benchAnd : Bool → Bool → Bool
benchAnd true b = b
benchAnd false _ = false

record BenchmarkReproductionReceipt (claim : BenchmarkClaim) : Set where
  constructor benchmarkReproductionReceipt
  field
    sourceRowsAcquired : Bool
    transformationVersionPinned : Bool
    unitsPinned : Bool
    frameConventionPinned : Bool
    uncertaintyConventionPinned : Bool
    executableProducerAcquired : Bool
    outputComparedAgainstSource : Bool
    independentRunCompleted : Bool
    exactArtifactHashRecorded : Bool
    resultSummary : String

open BenchmarkReproductionReceipt public

receiptComplete :
  {claim : BenchmarkClaim} →
  BenchmarkReproductionReceipt claim →
  Bool
receiptComplete r =
  benchAnd (sourceRowsAcquired r)
  (benchAnd (transformationVersionPinned r)
  (benchAnd (unitsPinned r)
  (benchAnd (frameConventionPinned r)
  (benchAnd (uncertaintyConventionPinned r)
  (benchAnd (executableProducerAcquired r)
  (benchAnd (outputComparedAgainstSource r)
  (benchAnd (independentRunCompleted r)
            (exactArtifactHashRecorded r))))))))

record FirstLightBenchmarkFrontier : Set where
  constructor firstLightBenchmarkFrontier
  field
    lmc : ClaimStatus
    sagittarius : ClaimStatus
    sgrA : ClaimStatus
    mcConnachie : ClaimStatus
    kkh86 : ClaimStatus
    sourceFormalisationIntegrated : Bool
    sourceMetadataChecked : Bool
    agdaKernelReceiptPresent : Bool
    independentScienceReproductionPresent : Bool

open FirstLightBenchmarkFrontier public

currentBenchmarkFrontier : FirstLightBenchmarkFrontier
currentBenchmarkFrontier =
  firstLightBenchmarkFrontier
    attributedPosterClaim
    attributedPosterClaim
    attributedPosterClaim
    attributedPosterClaim
    unresolvedResidual
    true
    true
    false
    false

attributedClaimConstructsIndependentReceipt : Bool
attributedClaimConstructsIndependentReceipt = false

attributedClaimConstructsIndependentReceiptIsFalse :
  attributedClaimConstructsIndependentReceipt ≡ false
attributedClaimConstructsIndependentReceiptIsFalse = refl

record BenchmarkAcquisitionDemand : Set where
  constructor benchmarkAcquisitionDemand
  field
    demandBenchmark : BenchmarkKind
    requiredArtifact : String
    paymentPurpose : String

benchmarkAcquisitionDemands : List BenchmarkAcquisitionDemand
benchmarkAcquisitionDemands =
  benchmarkAcquisitionDemand lmcSixComponent
    "exact six-component LMC source rows plus Virtual Observatory transformation/kernel code and uncertainty normalization"
    "test the attributed <=0.03 sigma claim component by component"
  ∷ benchmarkAcquisitionDemand sagittariusPhaseSpace
    "exact Vasiliev Sagittarius comparison rows plus Virtual Observatory row-selection and frame-transformation producer"
    "test the attributed last-printed-digit agreement without conflating candidate membership with measured truth"
  ∷ benchmarkAcquisitionDemand sgrAProperMotion
    "exact assembled-frame constants, solar-motion assumptions, Sgr A* comparison coordinates, and sigma calculation"
    "test the attributed 0.85 sigma external-frame agreement"
  ∷ benchmarkAcquisitionDemand mcConnachieDerivedDistances
    "exact McConnachie input table version, the three derived-column formulas, all selected rows, and the first-light recomputation producer"
    "recompute RMS residuals and isolate KKH 86 rather than accepting the aggregate summary"
  ∷ []
