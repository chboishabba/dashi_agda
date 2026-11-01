module DASHI.Empirical.DarkDimensionDAOPaperTableReconstructionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- PAPER-TABLE RECONSTRUCTION FOR arXiv:2602.23895
--
-- Table I of Garny–Niedermann–Sloth publishes the best-fit point for the
-- extended DRMD + SH0ES-calibrated-supernova analysis for all ordinary
-- cosmological coordinates and the principal DRMD coordinates except the
-- sampled z_stop input.  The paper instead publishes best-fit log10(z_dec)
-- and gives Eq. (13):
--
--   (1 + z_stop) / (1 + z_dec) ≃ ln[(G/H)_ini]
--
-- with (G/H)_ini fixed to 10^7.
--
-- This owner therefore records a source-bound, runnable reconstruction packet.
-- It is deliberately NOT an identity claim about the authors' original MCMC
-- manifest or chain state: z_stop is reconstructed through an approximation.
------------------------------------------------------------------------

paperArXiv : String
paperArXiv = "2602.23895"

record PaperTableBestFit : Set where
  constructor paperTableBestFit
  field
    omegaB : String
    omegaCDM : String
    h0KmPerSecPerMpc : String
    lnTenTenAs : String
    scalarTiltNs : String
    tauReio : String
    deltaNeffDRMD : String
    log10ZDec : String
    interactingDMFraction : String
    baryonDragHorizonMpcOverH : String
    darkDragHorizonMpcOverH : String
    daoAmplitude : String

open PaperTableBestFit public

extendedAnalysisBestFit : PaperTableBestFit
extendedAnalysisBestFit =
  paperTableBestFit
    "0.02318"
    "0.1382"
    "72.50"
    "3.051"
    "0.9798"
    "0.0581"
    "0.87"
    "3.350"
    "0.039"
    "100.0"
    "58.6"
    "0.036"

fixedInitialInteractionStrength : String
fixedInitialInteractionStrength = "1e7"

fixedMassiveNeutrinoCount : String
fixedMassiveNeutrinoCount = "1"

fixedMassiveNeutrinoMassEV : String
fixedMassiveNeutrinoMassEV = "0.06"

fixedMassiveNeutrinoTemperatureRatio : String
fixedMassiveNeutrinoTemperatureRatio = "0.716"

fixedAlphaS : String
fixedAlphaS = "0"

fixedBetaS : String
fixedBetaS = "0"

zStopReconstructionFormula : String
zStopReconstructionFormula =
  "z_stop = (1 + 10^log10(z_dec)) * ln((G/H)_ini) - 1"

record PaperTableReconstructionStatus : Set where
  constructor paperTableReconstructionStatus
  field
    tableBestFitPublished : Bool
    fixedInteractionStrengthPublished : Bool
    zStopDirectlyPublished : Bool
    zStopReconstructedFromEquation13 : Bool
    equation13ApproximationRetained : Bool
    originalMCMCManifestRecovered : Bool
    reconstructionManifestRunnable : Bool
    reconstructionExecutedByDASHI : Bool

open PaperTableReconstructionStatus public

canonicalPaperTableReconstructionStatus : PaperTableReconstructionStatus
canonicalPaperTableReconstructionStatus =
  paperTableReconstructionStatus
    true
    true
    false
    true
    true
    false
    true
    false

------------------------------------------------------------------------
-- WrongType / custody firewalls.
------------------------------------------------------------------------

data PaperBestFitEqualsOriginalMCMCManifest : Set where

data ApproximateZStopEqualsExactSampledCoordinate : Set where

paperBestFitDoesNotEqualOriginalMCMCManifest :
  PaperBestFitEqualsOriginalMCMCManifest → ⊥
paperBestFitDoesNotEqualOriginalMCMCManifest ()

approximateZStopDoesNotBecomeExactSampledCoordinate :
  ApproximateZStopEqualsExactSampledCoordinate → ⊥
approximateZStopDoesNotBecomeExactSampledCoordinate ()

reconstructionCanRunWithoutClaimingOriginalCustody :
  reconstructionManifestRunnable canonicalPaperTableReconstructionStatus ≡ true
reconstructionCanRunWithoutClaimingOriginalCustody = refl

originalManifestStillNotRecovered :
  originalMCMCManifestRecovered canonicalPaperTableReconstructionStatus ≡ false
originalManifestStillNotRecovered = refl

reconstructionStillNotExecuted :
  reconstructionExecutedByDASHI canonicalPaperTableReconstructionStatus ≡ false
reconstructionStillNotExecuted = refl
