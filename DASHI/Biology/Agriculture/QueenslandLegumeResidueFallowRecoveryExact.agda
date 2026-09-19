module DASHI.Biology.Agriculture.QueenslandLegumeResidueFallowRecoveryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.ConstructiveNitrogenTransportKernelExact as Transport

------------------------------------------------------------------------
-- QUEENSLAND LEGUME RESIDUE ROUTE x FALLOW x FOLLOWING-CROP RECOVERY
--
-- SOURCE / ATTRIBUTION
--
-- Thi Thanh Hai Nguyen, Michael Bell, Chelsea Janke & Alwyn Williams,
-- GRDC Grains Research Update, Goondiwindi, 3 March 2026:
--
--   "Residue-derived nitrogen recovery from above and below ground legume
--    residues under contrasting fallow durations"
--
-- The UQ Gatton field experiments used 15N-enriched tracing and explicitly
-- separated above-ground (AG), below-ground (BG), combined AG&BG, and bare
-- fallow treatments across:
--
--   * a short ~2 month lablab/millet -> barley fallow;
--   * a long ~9 month mungbean -> sorghum fallow.
--
-- The paper therefore pays a same-experiment route x time x crop-recovery join.
--
-- IMPORTANT MEASUREMENT FIREWALL
--
-- Isotope-derived residue N uptake (Ndfr) is directly estimated from the
-- tracer design.  Recovery efficiency for BG treatments additionally requires
-- a denominator for total BG residue-N input.  The paper states that complete
-- BG residue-N quantification was not possible and assumes BG residue N equals
-- half of corresponding AG residue N for that calculation.
--
-- DASHI keeps those two evidentiary objects separate.
------------------------------------------------------------------------

grdcPublicationDate : String
grdcPublicationDate = "2026-03-03"

grdcSourceURL : String
grdcSourceURL =
  "https://grdc.com.au/resources-and-publications/grdc-update-papers/tab-content/grdc-update-papers/2026/03/residue-derived-nitrogen-recovery-from-above-and-below-ground-legume-residues-under-contrasting-fallow-durations"

nguyenEtAl2026 : Attribution.AttributedSource
nguyenEtAl2026 = Attribution.mkNoDOISource
  "Thi Thanh Hai Nguyen; Michael Bell; Chelsea Janke; Alwyn Williams"
  "Residue-derived nitrogen recovery from above and below ground legume residues under contrasting fallow durations"
  "GRDC Grains Research Update, Goondiwindi"
  "2026" grdcSourceURL
  Attribution.institutionalSource
  "University of Queensland Gatton field experiments using 15N-enriched tracing to separate above-ground, below-ground and combined residue contributions to following-cereal N uptake after approximately two- and nine-month fallows. Retained as a Queensland route x fallow x recovery source, not an Acacia/Senegalia result and not a fertilizer-replacement experiment."
  Attribution.publicAttribution

data FallowRecoverySystem : Set where
  lablabMilletToBarleyShortFallow : FallowRecoverySystem
  mungbeanToSorghumLongFallow : FallowRecoverySystem

record FallowRecoveryReceipt : Set where
  field
    source : Attribution.AttributedSource
    system : FallowRecoverySystem
    candidateRoute : Transport.NitrogenTransportRoute

    fallowMonths : Nat
    followingCropFertiliserNkgHa : Nat

    agNdfrLowerKgHa : Nat
    agNdfrUpperKgHa : Nat
    agBgNdfrLowerKgHa : Nat
    agBgNdfrUpperKgHa : Nat

    totalCropNUptakeLowerKgHa : Nat
    totalCropNUptakeUpperKgHa : Nat

    measuredReading : String
    recoveryEfficiencyReading : String
    boundedReading : String

open FallowRecoveryReceipt public

shortFallowBarleyReceipt : FallowRecoveryReceipt
shortFallowBarleyReceipt = record
  { source = nguyenEtAl2026
  ; system = lablabMilletToBarleyShortFallow
  ; candidateRoute = Transport.residueMineralisationRoute
  ; fallowMonths = 2
  ; followingCropFertiliserNkgHa = 50
  ; agNdfrLowerKgHa = 11
  ; agNdfrUpperKgHa = 14
  ; agBgNdfrLowerKgHa = 20
  ; agBgNdfrUpperKgHa = 25
  ; totalCropNUptakeLowerKgHa = 0
  ; totalCropNUptakeUpperKgHa = 0
  ; measuredReading =
      "After the approximately two-month fallow, barley residue-derived N uptake was about 11-14 kg N/ha for AG-only and about 20-25 kg N/ha for AG&BG; AG&BG exceeded AG significantly. Soil mineral N was observed at 0, 30 and 60 days and was generally lower under BG-inclusive treatments. Barley received a uniform 50 kg N/ha urea application."
  ; recoveryEfficiencyReading =
      "AG-only recovery efficiencies were below 20% for both species; the millet BG treatment exceeded 50%. Complete BG residue-N input was not directly quantified, so recovery-efficiency denominators assumed BG residue N equal to half the corresponding measured AG residue-N input."
  ; boundedReading =
      "Ndfr and recovery efficiency are distinct receipts. Uniform fertilizer N means this experiment does not directly identify avoided mineral fertilizer. Short-fallow results remain species, weather, residue-placement and field-context indexed."
  }

longFallowSorghumReceipt : FallowRecoveryReceipt
longFallowSorghumReceipt = record
  { source = nguyenEtAl2026
  ; system = mungbeanToSorghumLongFallow
  ; candidateRoute = Transport.residueMineralisationRoute
  ; fallowMonths = 9
  ; followingCropFertiliserNkgHa = 0
  ; agNdfrLowerKgHa = 9
  ; agNdfrUpperKgHa = 10
  ; agBgNdfrLowerKgHa = 14
  ; agBgNdfrUpperKgHa = 16
  ; totalCropNUptakeLowerKgHa = 180
  ; totalCropNUptakeUpperKgHa = 200
  ; measuredReading =
      "After the approximately nine-month fallow, sorghum total biomass and total N uptake did not differ significantly among residue-component treatments; total N uptake averaged about 180-200 kg N/ha. Isotope-derived total-biomass Ndfr was about 9-10 kg N/ha in AG and 14-16 kg N/ha in AG&BG, with AG&BG significantly greater than AG. Sorghum received no fertilizer N."
  ; recoveryEfficiencyReading =
      "The paper emphasizes persistence/detectability of residue-derived N after extensive decomposition and redistribution; it does not turn the no-fertilizer sorghum treatment into a mineral-N response curve."
  ; boundedReading =
      "Several intense rainfall events occurred during the long fallow, including two above 130 mm and a short flooding event. Source, rainfall, fallow, crop and residue placement remain indexed; no universal transfer efficiency is inferred."
  }

record FallowRecoveryBoundary : Set where
  field
    sameExperimentRouteFallowRecoveryJoinOwned : Bool
    shortFallowSoilMineralNTimeSeriesOwned : Bool
    isotopeDerivedNdfrDirectlyObserved : Bool

    bgRecoveryEfficiencyDenominatorDirectlyMeasured : Bool
    recoveryEfficiencyEqualsIsotopeDerivedNdfr : Bool
    shortFallowRecoveryEqualsAvoidedMineralFertiliser : Bool
    zeroFertiliserLongFallowCreatesMineralNResponseCurve : Bool
    absenceOfBiomassDifferenceImpliesNoResidueTransferDifference : Bool
    bgResidueEqualsLivingSymbioticTransfer : Bool
    fallowDurationMayBeErased : Bool
    rainfallAndSeasonMayBeErased : Bool
    queenslandCroppingResidueRecoveryCreatesAcaciaSameObjectEvidence : Bool
    sourceCreatesDeploymentAuthority : Bool

open FallowRecoveryBoundary public

canonicalFallowRecoveryBoundary : FallowRecoveryBoundary
canonicalFallowRecoveryBoundary = record
  { sameExperimentRouteFallowRecoveryJoinOwned = true
  ; shortFallowSoilMineralNTimeSeriesOwned = true
  ; isotopeDerivedNdfrDirectlyObserved = true
  ; bgRecoveryEfficiencyDenominatorDirectlyMeasured = false
  ; recoveryEfficiencyEqualsIsotopeDerivedNdfr = false
  ; shortFallowRecoveryEqualsAvoidedMineralFertiliser = false
  ; zeroFertiliserLongFallowCreatesMineralNResponseCurve = false
  ; absenceOfBiomassDifferenceImpliesNoResidueTransferDifference = false
  ; bgResidueEqualsLivingSymbioticTransfer = false
  ; fallowDurationMayBeErased = false
  ; rainfallAndSeasonMayBeErased = false
  ; queenslandCroppingResidueRecoveryCreatesAcaciaSameObjectEvidence = false
  ; sourceCreatesDeploymentAuthority = false
  }

attributionRule : String
attributionRule =
  "Nguyen, Bell, Janke & Williams 2026 owns the UQ Gatton field design, AG/BG/AG&BG residue treatments, approximately two- and nine-month fallows, soil-mineral-N observations, isotope-derived residue-N uptake results, crop-N/biomass observations and the stated BG-input assumption used for recovery-efficiency calculations. DASHI owns only the typed route/time/recovery reconstruction and no-promotion boundary. The source does not own DASHI's convolution, continuous-to-discrete, tail or Cauchy mathematics; the assumption-dependent BG recovery denominator is not relabelled as direct measurement; and the experiment does not create Acacia/Senegalia same-object evidence, living symbiotic transfer, an explicit mineral-N response curve, fertilizer-replacement value or deployment authority."
