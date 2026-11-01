module DASHI.Physics.Catalysis.HighEntropyMBeneMechanismHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- HIGH-ENTROPY MBENE CO2RR MECHANISM HYPERFABRIC
--
-- Source scope: Bharadwaj H and Ranganathan, npj Computational Materials
-- (2026), DOI 10.1038/s41524-026-02287-4.
--
-- This owner encodes the reported COMPUTATIONAL mechanism for why the best
-- screened high-entropy MBenes improve the CO2 -> CO free-energy pathway.
-- It deliberately does not collapse the mechanism to a single activity score.
------------------------------------------------------------------------

record CatalysisBase : Set₁ where
  constructor catalysis-base
  field
    Composition SurfaceSite ReactionEnvironment ElectrodePotential : Set
    sourceReference : String

open CatalysisBase public

record CatalyticFibre (base : CatalysisBase) : Set₁ where
  constructor catalytic-fibre
  field
    LocalMetalIdentity LocalNeighbourhood ElectronicState : Set
    ChargeRedistribution AdsorbateState ReactionStep : Set
    FreeEnergyProfile LinearScalingResidual HydrogenCompetition : Set
    mechanismReference : String

open CatalyticFibre public

record CatalyticHypervoxel : Set₁ where
  constructor catalytic-hypervoxel
  field
    base : CatalysisBase
    fibre : CatalyticFibre base

open CatalyticHypervoxel public

CatalyticHyperfabric : Set₁
CatalyticHyperfabric = CatalyticHypervoxel

------------------------------------------------------------------------
-- The chemistry is local and relational.
--
-- Bulk/equiatomic composition is therefore only a coarse chart.  The local
-- Cr-centred site, its Hf/Zr neighbourhood, charge redistribution, adsorbate,
-- and reaction step remain fibre coordinates.
------------------------------------------------------------------------

record CompositionProjectionBoundary : Set where
  constructor composition-projection-boundary
  field
    globalCompositionDeterminesLocalMechanism : Bool
    globalCompositionDeterminesLocalMechanismIsFalse :
      globalCompositionDeterminesLocalMechanism ≡ false

    localNeighbourhoodIsIndependentCoordinate : Bool
    localNeighbourhoodIsIndependentCoordinateIsTrue :
      localNeighbourhoodIsIndependentCoordinate ≡ true

    chargeRedistributionIsIndependentCoordinate : Bool
    chargeRedistributionIsIndependentCoordinateIsTrue :
      chargeRedistributionIsIndependentCoordinate ≡ true

canonicalCompositionProjectionBoundary : CompositionProjectionBoundary
canonicalCompositionProjectionBoundary =
  composition-projection-boundary false refl true refl true refl

------------------------------------------------------------------------
-- Producer-level causal receipt.
--
-- This is stronger than recording that a candidate has a good limiting
-- potential: it records WHY the paper reports that the local chemistry is
-- better.  Each stage is kept explicit so a downstream consumer can require
-- the mechanism rather than merely a leaderboard scalar.
------------------------------------------------------------------------

record BetterChemistryProducer : Set where
  constructor better-chemistry-producer
  field
    highEntropyChemicalDiversityPresent : Bool
    highEntropyChemicalDiversityPresentIsTrue :
      highEntropyChemicalDiversityPresent ≡ true

    hfZrElectronDonationToCrCentre : Bool
    hfZrElectronDonationToCrCentreIsTrue :
      hfZrElectronDonationToCrCentre ≡ true

    coohStarPreferentiallyStabilized : Bool
    coohStarPreferentiallyStabilizedIsTrue :
      coohStarPreferentiallyStabilized ≡ true

    coohStarIsReportedRateDeterminingIntermediate : Bool
    coohStarIsReportedRateDeterminingIntermediateIsTrue :
      coohStarIsReportedRateDeterminingIntermediate ≡ true

    monometallicLinearScalingConstraintDecoupled : Bool
    monometallicLinearScalingConstraintDecoupledIsTrue :
      monometallicLinearScalingConstraintDecoupled ≡ true

    pathwayFreeEnergyBottleneckLowered : Bool
    pathwayFreeEnergyBottleneckLoweredIsTrue :
      pathwayFreeEnergyBottleneckLowered ≡ true

    mechanismIsLocalNotCompositionScalar : Bool
    mechanismIsLocalNotCompositionScalarIsTrue :
      mechanismIsLocalNotCompositionScalar ≡ true

canonicalBetterChemistryProducer : BetterChemistryProducer
canonicalBetterChemistryProducer =
  better-chemistry-producer
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Explicit causal ordering.
--
-- The arrows here are source-bounded mechanism stages, not universal laws of
-- all high-entropy catalysts.
------------------------------------------------------------------------

record MechanismChain : Set where
  constructor mechanism-chain
  field
    stage1LocalChemicalDiversity : String
    stage2HfZrChargeDonation : String
    stage3CrCentredElectronicState : String
    stage4COOHStarStabilization : String
    stage5LinearScalingDecoupling : String
    stage6LowerFreeEnergyBottleneck : String
    stage7ImprovedLimitingPotential : String

canonicalMechanismChain : MechanismChain
canonicalMechanismChain = mechanism-chain
  "high-entropy local chemical diversity"
  "Hf/Zr-mediated electron donation"
  "Cr-centred active-site electronic state"
  "stabilization of rate-determining COOH*"
  "decoupling of monometallic linear scaling relationships"
  "lower CO2-to-CO free-energy bottleneck"
  "improved CHE limiting potential"

------------------------------------------------------------------------
-- Three reported computational winners.
------------------------------------------------------------------------

record PredictedWinnerSet : Set where
  constructor predicted-winner-set
  field
    winner1 winner2 winner3 : String
    allThreeReportedULZeroVsRHE : Bool
    allThreeReportedULZeroVsRHEIsTrue :
      allThreeReportedULZeroVsRHE ≡ true

canonicalPredictedWinnerSet : PredictedWinnerSet
canonicalPredictedWinnerSet = predicted-winner-set
  "CrNbZrMoTiB5"
  "MoZrHfNbCrB5"
  "MoZrHfTaCrB5"
  true refl

------------------------------------------------------------------------
-- Evidence and thermodynamic-language firewalls.
--
-- U_L = 0.00 V vs RHE is the reported CHE limiting-potential result for the
-- computed pathway.  It must not be reinterpreted as zero electricity, a
-- self-powered reactor, or experimental validation.
------------------------------------------------------------------------

record ComputationalEvidenceBoundary : Set where
  constructor computational-evidence-boundary
  field
    resultIsComputationalPrediction : Bool
    resultIsComputationalPredictionIsTrue :
      resultIsComputationalPrediction ≡ true

    experimentallyValidatedCatalystPerformance : Bool
    experimentallyValidatedCatalystPerformanceIsFalse :
      experimentallyValidatedCatalystPerformance ≡ false

    zeroCHELimitingPotentialMeansZeroElectricalSystem : Bool
    zeroCHELimitingPotentialMeansZeroElectricalSystemIsFalse :
      zeroCHELimitingPotentialMeansZeroElectricalSystem ≡ false

    zeroCHELimitingPotentialMeansNoAdditionalCHEDrivingPotential : Bool
    zeroCHELimitingPotentialMeansNoAdditionalCHEDrivingPotentialIsTrue :
      zeroCHELimitingPotentialMeansNoAdditionalCHEDrivingPotential ≡ true

canonicalComputationalEvidenceBoundary : ComputationalEvidenceBoundary
canonicalComputationalEvidenceBoundary =
  computational-evidence-boundary true refl false refl false refl true refl

------------------------------------------------------------------------
-- Screening provenance is kept separate from mechanism provenance.
------------------------------------------------------------------------

record ScreeningReceipt : Set where
  constructor screening-receipt
  field
    equiatomicQuinaryCandidatesScreened : String
    viableCandidatesAfterFunnel : String
    surfaceEnvironmentsAcceleratedByMACE : String
    screeningUsesDFTRelaxation : Bool
    screeningUsesDFTRelaxationIsTrue : screeningUsesDFTRelaxation ≡ true
    screeningUsesFormationEnergyFilter : Bool
    screeningUsesFormationEnergyFilterIsTrue :
      screeningUsesFormationEnergyFilter ≡ true
    screeningUsesPDOSActiveSiteIdentification : Bool
    screeningUsesPDOSActiveSiteIdentificationIsTrue :
      screeningUsesPDOSActiveSiteIdentification ≡ true
    screeningUsesCHEFreeEnergyProfiling : Bool
    screeningUsesCHEFreeEnergyProfilingIsTrue :
      screeningUsesCHEFreeEnergyProfiling ≡ true

canonicalScreeningReceipt : ScreeningReceipt
canonicalScreeningReceipt = screening-receipt
  "56"
  "18"
  "1375"
  true refl
  true refl
  true refl
  true refl

------------------------------------------------------------------------
-- Consumer firewall: a good score does not reconstruct the producer.
------------------------------------------------------------------------

record ScoreMechanismBoundary : Set where
  constructor score-mechanism-boundary
  field
    goodLimitingPotentialDeterminesChargeTransferMechanism : Bool
    goodLimitingPotentialDeterminesChargeTransferMechanismIsFalse :
      goodLimitingPotentialDeterminesChargeTransferMechanism ≡ false

    goodLimitingPotentialDeterminesUniqueActiveSite : Bool
    goodLimitingPotentialDeterminesUniqueActiveSiteIsFalse :
      goodLimitingPotentialDeterminesUniqueActiveSite ≡ false

    mechanismReceiptRequiredForWhyBetterClaim : Bool
    mechanismReceiptRequiredForWhyBetterClaimIsTrue :
      mechanismReceiptRequiredForWhyBetterClaim ≡ true

canonicalScoreMechanismBoundary : ScoreMechanismBoundary
canonicalScoreMechanismBoundary =
  score-mechanism-boundary false refl false refl true refl
