module DASHI.Biology.Agriculture.QueenslandChickpeaWheatFertilizerEquivalentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.CoverCropNitrogenCarryoverCounterfactualExact as Counterfactual

------------------------------------------------------------------------
-- QUEENSLAND CHICKPEA -> WHEAT MULTI-RATE FERTILIZER-N EQUIVALENT
--
-- SOURCE
--
-- Dalal et al. 1998, Warra, southern Queensland, DOI 10.1071/EA98027.
--
-- An adjacent annual wheat experiment applied urea at:
--
--   0, 25, 50, 75, 100 (1988 only), 125 (1989 only), 150 kg N/ha.
--
-- Linear or quadratic regressions of wheat grain-N yield against fertilizer-N
-- rate were used to estimate the amount of fertilizer N required to match the
-- grain-N yield of unfertilized wheat following chickpea.
--
-- Mean fertilizer-N equivalent for the usable seasons 1989, 1990, 1992, 1993
-- and 1996 was 49.2 +/- 6.4 kg N/ha.  1988 was unusually high (114.6 kg N/ha)
-- after frost-damaged chickpea / unusual preceding conditions.  1994 and 1995
-- were not estimable because poor in-crop rainfall led to poor fertilizer-N
-- uptake.
--
-- DASHI therefore treats "response curve exists" and "response curve is
-- informative enough to estimate an equivalent this season" as distinct.
------------------------------------------------------------------------

dalalEtAl1998DOI : String
dalalEtAl1998DOI = "10.1071/EA98027"

dalalEtAl1998 : Attribution.AttributedSource
dalalEtAl1998 = Attribution.mkDOISource
  "Ram C. Dalal; W. M. Strong; E. J. Weston; J. E. Cooper; G. B. Wildermuth; K. J. Lehane; A. J. King; C. J. Holmes"
  "Sustaining productivity of a Vertisol at Warra, Queensland, with fertilisers, no-tillage, or legumes. 5. Wheat yields, nitrogen benefits and water-use efficiency of chickpea-wheat rotation"
  "Australian Journal of Experimental Agriculture 38(5):489-501"
  "1998" dalalEtAl1998DOI "https://doi.org/10.1071/EA98027"
  Attribution.academicArticleSource
  "Warra chickpea-wheat rotation study with an adjacent multi-rate wheat fertilizer-N response experiment. Linear/quadratic grain-N-yield response curves were used to estimate fertilizer-N equivalents for unfertilized wheat following chickpea. Retained as a Queensland explicit counterfactual/response-curve receipt; seasonal water limitation and response estimability remain indexed."
  Attribution.publicAttribution

data FertilizerEquivalentEstimate : Set where
  estimatedTenthsKgHa : Nat → FertilizerEquivalentEstimate
  notEstimated : FertilizerEquivalentEstimate

record AnnualFertilizerEquivalent : Set where
  field
    cropYear : Nat
    estimate : FertilizerEquivalentEstimate
    reading : String

open AnnualFertilizerEquivalent public

equivalent1988 : AnnualFertilizerEquivalent
equivalent1988 = record
  { cropYear = 1988
  ; estimate = estimatedTenthsKgHa 1146
  ; reading =
      "114.6 kg N/ha; source discusses frost injury to preceding chickpea, low chickpea grain/N removal and unusually large initial nitrate supply."
  }

equivalent1989 : AnnualFertilizerEquivalent
equivalent1989 = record
  { cropYear = 1989
  ; estimate = estimatedTenthsKgHa 501
  ; reading = "50.1 kg N/ha."
  }

equivalent1990 : AnnualFertilizerEquivalent
equivalent1990 = record
  { cropYear = 1990
  ; estimate = estimatedTenthsKgHa 579
  ; reading = "57.9 kg N/ha."
  }

equivalent1992 : AnnualFertilizerEquivalent
equivalent1992 = record
  { cropYear = 1992
  ; estimate = estimatedTenthsKgHa 505
  ; reading = "50.5 kg N/ha."
  }

equivalent1993 : AnnualFertilizerEquivalent
equivalent1993 = record
  { cropYear = 1993
  ; estimate = estimatedTenthsKgHa 473
  ; reading = "47.3 kg N/ha."
  }

equivalent1994 : AnnualFertilizerEquivalent
equivalent1994 = record
  { cropYear = 1994
  ; estimate = notEstimated
  ; reading =
      "Not estimated: poor fertilizer-N uptake under low in-crop rainfall made the response experiment non-informative for an equivalent."
  }

equivalent1995 : AnnualFertilizerEquivalent
equivalent1995 = record
  { cropYear = 1995
  ; estimate = notEstimated
  ; reading =
      "Not estimated: poor fertilizer-N uptake under low in-crop rainfall made the response experiment non-informative for an equivalent."
  }

equivalent1996 : AnnualFertilizerEquivalent
equivalent1996 = record
  { cropYear = 1996
  ; estimate = estimatedTenthsKgHa 400
  ; reading = "40.0 kg N/ha."
  }

record ChickpeaFertilizerEquivalentReceipt : Set where
  field
    source : Attribution.AttributedSource
    mineralNRatesReading : String
    responseModelReading : String
    meanUsableSeasonFertilizerEquivalentTenthsKgHa : Nat
    meanUsableSeasonFertilizerEquivalentSETenthsKgHa : Nat
    annualEstimates : List AnnualFertilizerEquivalent
    boundedReading : String

open ChickpeaFertilizerEquivalentReceipt public

warraChickpeaFertilizerEquivalentReceipt : ChickpeaFertilizerEquivalentReceipt
warraChickpeaFertilizerEquivalentReceipt = record
  { source = dalalEtAl1998
  ; mineralNRatesReading =
      "Fresh urea-N response experiment used 0, 25, 50, 75 and 150 kg N/ha annually, plus 100 kg N/ha in 1988 and 125 kg N/ha in 1989."
  ; responseModelReading =
      "Linear or quadratic regressions of wheat grain-N yield against fertilizer-N rate; equivalent rate selected to match grain-N yield of unfertilized wheat following chickpea."
  ; meanUsableSeasonFertilizerEquivalentTenthsKgHa = 492
  ; meanUsableSeasonFertilizerEquivalentSETenthsKgHa = 64
  ; annualEstimates =
      equivalent1988 ∷
      equivalent1989 ∷
      equivalent1990 ∷
      equivalent1992 ∷
      equivalent1993 ∷
      equivalent1994 ∷
      equivalent1995 ∷
      equivalent1996 ∷ []
  ; boundedReading =
      "The ~49.2 kg N/ha mean is explicitly for usable seasons 1989, 1990, 1992, 1993 and 1996. 1988 is contextually anomalous; 1994-95 are non-estimable. Fertilizer equivalence remains crop, season, water, response metric and source-system indexed."
  }

queenslandChickpeaCounterfactualShape :
  Counterfactual.FertilizerReplacementEvidenceShape
queenslandChickpeaCounterfactualShape =
  Counterfactual.fertilizer-replacement-evidence-shape
    true true true true true true true true

record ChickpeaEquivalentBoundary : Set where
  field
    explicitMultiRateFertilizerResponseCurveOwned : Bool
    regressionBasedFertilizerEquivalentOwned : Bool
    fertilizerEquivalentRequiresInformativeSeasonalResponse : Bool

    singleRateComparatorRequired : Bool
    nonEstimableDryYearsAssignedReplacementValue : Bool
    oneMeanEquivalentAppliesToEverySeason : Bool
    grainNEquivalentEqualsWholeCropNEquivalent : Bool
    waterContextMayBeDropped : Bool
    chickpeaFertilizerEquivalentTransfersToAcaciaAvoidedMineralN : Bool
    chickpeaResponseCurveCreatesDeploymentAuthority : Bool

open ChickpeaEquivalentBoundary public

canonicalChickpeaEquivalentBoundary : ChickpeaEquivalentBoundary
canonicalChickpeaEquivalentBoundary = record
  { explicitMultiRateFertilizerResponseCurveOwned = true
  ; regressionBasedFertilizerEquivalentOwned = true
  ; fertilizerEquivalentRequiresInformativeSeasonalResponse = true
  ; singleRateComparatorRequired = false
  ; nonEstimableDryYearsAssignedReplacementValue = false
  ; oneMeanEquivalentAppliesToEverySeason = false
  ; grainNEquivalentEqualsWholeCropNEquivalent = false
  ; waterContextMayBeDropped = false
  ; chickpeaFertilizerEquivalentTransfersToAcaciaAvoidedMineralN = false
  ; chickpeaResponseCurveCreatesDeploymentAuthority = false
  }

attributionRule : String
attributionRule =
  "Dalal et al. 1998 (DOI 10.1071/EA98027) owns the Warra chickpea-wheat observations, adjacent fertilizer-N rate experiment, linear/quadratic grain-N response curves, annual fertilizer-equivalent estimates, non-estimable dry seasons and source interpretation. DASHI owns only the typed response-curve/equivalent/estimability reconstruction and no-promotion boundary. The Queensland chickpea result does not create an Acacia/Senegalia fertilizer-replacement value, whole-crop-N equivalence, season-invariant replacement value or deployment authority."
