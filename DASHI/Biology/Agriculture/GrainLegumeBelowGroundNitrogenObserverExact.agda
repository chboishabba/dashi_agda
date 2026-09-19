module DASHI.Biology.Agriculture.GrainLegumeBelowGroundNitrogenObserverExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution

------------------------------------------------------------------------
-- GRAIN-LEGUME BELOW-GROUND N OBSERVER CALIBRATION
--
-- This owner is deliberately about the measurement object.
--
-- McNeill & Unkovich 2024:
--   * glasshouse faba bean, field pea and lupin;
--   * 15N leaf/stem feeding;
--   * recovered coarse roots accounted for only 33-55% of estimated plant
--     below-ground N at physiological maturity;
--   * substantial below-ground N occurred in unrecovered/fine-root and soil
--     fractions.
--
-- Liu et al. 2024:
--   * Saskatchewan grain-legume/wheat field system;
--   * partitions above- and total below-ground residual contributions to
--     following-wheat N nutrition;
--   * below-ground residuals were the primary residue-N source (70-91%);
--     above-ground residue supplied 1-11%.
--
-- These sources motivate/validate a BG-residue observer axis.  Their numerical
-- fractions are not projected into Queensland, and they do not convert an
-- assumption-based BG input denominator in another experiment into a direct
-- measurement.
------------------------------------------------------------------------

mcNeillUnkovich2024DOI : String
mcNeillUnkovich2024DOI = "10.1007/s11104-024-06515-y"

liuEtAl2024DOI : String
liuEtAl2024DOI = "10.1016/j.fcr.2024.109412"

mcNeillUnkovich2024 : Attribution.AttributedSource
mcNeillUnkovich2024 = Attribution.mkDOISource
  "Ann M. McNeill; Murray J. Unkovich"
  "Estimates of N accumulated below-ground by grain legumes derived using leaf or stem 15N-feeding: in search of a practical method for potential use at remote field locations"
  "Plant and Soil 500:721-741"
  "2024" mcNeillUnkovich2024DOI
  "https://doi.org/10.1007/s11104-024-06515-y"
  Attribution.academicArticleSource
  "Glasshouse observer-calibration study for total below-ground N in faba bean, field pea and lupin. Recovered coarse-root N was 33-55% of estimated plant below-ground N at physiological maturity; fine-root/soil fractions therefore remain part of the below-ground measurement object. Retained as a method/observer donor, not a Queensland transfer-efficiency source."
  Attribution.publicAttribution

liuEtAl2024 : Attribution.AttributedSource
liuEtAl2024 = Attribution.mkDOISource
  "Liting Liu; J. Diane Knight; Reynald L. Lemke; Richard E. Farrell"
  "Quantifying the contribution of above- and below-ground residues of chickpea, faba bean, lentil, field pea and wheat to the nitrogen nutrition of a subsequent wheat crop"
  "Field Crops Research 313:109412"
  "2024" liuEtAl2024DOI
  "https://doi.org/10.1016/j.fcr.2024.109412"
  Attribution.academicArticleSource
  "Saskatchewan field residue-partition study. Across tested crops, total below-ground residuals including roots and soil were the primary residue-derived N source to subsequent wheat (70-91%), while above-ground residue supplied 1-11%. Retained as an external route-strength/comparator receipt, not a Queensland same-object percentage."
  Attribution.publicAttribution

data BelowGroundObserverEvidenceRole : Set where
  totalBelowGroundMeasurementCalibration : BelowGroundObserverEvidenceRole
  followingCropRouteContributionComparator : BelowGroundObserverEvidenceRole

record BelowGroundObserverReceipt : Set where
  field
    source : Attribution.AttributedSource
    role : BelowGroundObserverEvidenceRole
    observationReading : String
    boundedReading : String

open BelowGroundObserverReceipt public

mcNeillObserverReceipt : BelowGroundObserverReceipt
mcNeillObserverReceipt = record
  { source = mcNeillUnkovich2024
  ; role = totalBelowGroundMeasurementCalibration
  ; observationReading =
      "Coarse recovered roots represented 33-55% of estimated plant below-ground N at physiological maturity; below-ground N measurement therefore includes material not captured by standard coarse-root recovery."
  ; boundedReading =
      "Glasshouse grain-legume method evidence; it does not measure the BG residue-N denominator in the 2026 UQ Gatton field experiment."
  }

liuRouteComparatorReceipt : BelowGroundObserverReceipt
liuRouteComparatorReceipt = record
  { source = liuEtAl2024
  ; role = followingCropRouteContributionComparator
  ; observationReading =
      "In the Saskatchewan field system, total below-ground residuals were the primary residue-derived N source to subsequent wheat (70-91%), while above-ground residue supplied 1-11%."
  ; boundedReading =
      "Crop species, Canadian prairie environment, residue definitions and experimental design remain indexed; numerical route fractions do not transfer to Queensland."
  }

record BelowGroundObserverBoundary : Set where
  field
    belowGroundNitrogenObserverCalibrationOwned : Bool
    externalFollowingCropRouteComparatorOwned : Bool

    coarseRootRecoveryEqualsTotalBelowGroundNitrogen : Bool
    fineRootAndSoilFractionsMayBeErased : Bool
    canadianResidueFractionsTransferToQueensland : Bool
    observerCalibrationMakesGRDCBgDenominatorDirectMeasurement : Bool
    routeComparatorCreatesAcaciaSameObjectEvidence : Bool
    observerCalibrationCreatesDeploymentAuthority : Bool

open BelowGroundObserverBoundary public

canonicalBelowGroundObserverBoundary : BelowGroundObserverBoundary
canonicalBelowGroundObserverBoundary = record
  { belowGroundNitrogenObserverCalibrationOwned = true
  ; externalFollowingCropRouteComparatorOwned = true
  ; coarseRootRecoveryEqualsTotalBelowGroundNitrogen = false
  ; fineRootAndSoilFractionsMayBeErased = false
  ; canadianResidueFractionsTransferToQueensland = false
  ; observerCalibrationMakesGRDCBgDenominatorDirectMeasurement = false
  ; routeComparatorCreatesAcaciaSameObjectEvidence = false
  ; observerCalibrationCreatesDeploymentAuthority = false
  }

attributionRule : String
attributionRule =
  "McNeill & Unkovich 2024 (DOI 10.1007/s11104-024-06515-y) owns its glasshouse 15N observer-method results and below-ground N partition observations. Liu et al. 2024 (DOI 10.1016/j.fcr.2024.109412) owns its Saskatchewan field residue-partition and following-wheat N-nutrition results. DASHI owns only the typed observer/route roles and no-promotion boundary. These papers do not transfer Canadian percentages to Queensland, convert the GRDC BG-input assumption into direct measurement, create Acacia/Senegalia same-object evidence or deployment authority."
