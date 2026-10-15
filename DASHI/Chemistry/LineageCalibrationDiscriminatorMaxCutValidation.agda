module DASHI.Chemistry.LineageCalibrationDiscriminatorMaxCutValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Chemistry.GoldReactionReplaySuiteExact as Gold
import DASHI.Biology.LeadCalciumEndToEndReplayExact as PbCa
import DASHI.Biology.KitzerowBH4FluxCausalModelsExact as BH4
import DASHI.Chemistry.LineageBidiDiscriminatorSynthesisExact as Disc
import DASHI.Biology.CarbonSiliconReachableChemistryBenchmarkExact as Carbon
import DASHI.Chemistry.LineageCalibrationAttributionEnvelopeExact as Attribution
import DASHI.Chemistry.LineageSourceManifestationGuardExact as Manifestation
import DASHI.Chemistry.LineageAttributionAcquisitionFrontierExact as Acquisition

goldSuiteHasFiveHeterogeneousReplays :
  Gold.replayCountAtLeastFive Gold.canonicalGoldReactionReplaySuite ≡ true
goldSuiteHasFiveHeterogeneousReplays = refl

pbCaReplayRetainsFineAtomicDifference :
  PbCa.atomicIdentityCollapsed PbCa.canonicalLeadCalciumEndToEndReplay ≡ false
pbCaReplayRetainsFineAtomicDifference = refl

bh4FluxDoesNotPretendMeasuredNumbers :
  BH4.numericBranchFluxCalibrated BH4.canonicalBH4FluxModel ≡ false
  × BH4.competingArchitecturesExplicit BH4.canonicalBH4FluxModel ≡ true
bh4FluxDoesNotPretendMeasuredNumbers = refl , refl

discriminatorSynthesisDoesNotCreateTruth :
  Disc.generatedCandidateCreatesTruth Disc.canonicalLineageBidiSynthesisBoundary ≡ false
  × Disc.competingModelsDriveCandidateGeneration Disc.canonicalLineageBidiSynthesisBoundary ≡ true
discriminatorSynthesisDoesNotCreateTruth = refl , refl

carbonBenchmarkDoesNotPromoteInevitability :
  Carbon.carbonWinsImpliesLifeInevitable Carbon.canonicalCarbonSiliconReachableChemistryBenchmark ≡ false
carbonBenchmarkDoesNotPromoteInevitability = refl

attributionEnvelopeRetainsSourceRoleWithoutPromotion :
  Attribution.everyReplayCarriesAttributedSource Attribution.canonicalLineageCalibrationAttributionBoundary ≡ true
  × Attribution.citationCreatesNumericPayment Attribution.canonicalLineageCalibrationAttributionBoundary ≡ false
  × Attribution.dashiSynthesisAttributedToExternalSource Attribution.canonicalLineageCalibrationAttributionBoundary ≡ false
attributionEnvelopeRetainsSourceRoleWithoutPromotion = refl , (refl , refl)

manifestationGuardBlocksNearbySourcePromotion :
  Manifestation.nearbyCitationPaysCoordinate Manifestation.canonicalLineageManifestationBoundary ≡ false
  × Manifestation.sameObjectAndLocatorRequiredForNumericPayment Manifestation.canonicalLineageManifestationBoundary ≡ true
manifestationGuardBlocksNearbySourcePromotion = refl , refl

acquisitionFrontierIsNotTruthRanking :
  Acquisition.frontierRankIsTruthRank Acquisition.canonicalLineageAttributionAcquisitionFrontier ≡ false
  × Acquisition.unpaidCoordinateRetainsAttribution Acquisition.canonicalLineageAttributionAcquisitionFrontier ≡ true
acquisitionFrontierIsNotTruthRanking = refl , refl
