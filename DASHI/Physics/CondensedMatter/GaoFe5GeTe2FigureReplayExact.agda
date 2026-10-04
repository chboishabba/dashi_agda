module DASHI.Physics.CondensedMatter.GaoFe5GeTe2FigureReplayExact where

------------------------------------------------------------------------
-- SOURCE-EXACT FIGURE REPLAY FOR Fe5GeTe2
--
-- Primary source:
-- Q. Gao et al., Science Advances 12(32), eaeg5930 (2026),
-- DOI 10.1126/sciadv.aeg5930.
--
-- This owner records only statements explicit in the public article/figure
-- captions.  It deliberately does not reconstruct pixel-level ARPES arrays.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Physics.CondensedMatter.GaoFe5GeTe2FlatBandChargeOrderSourceReplayExact as Source

jiangEtAl2019MagicAngleChargeOrder : Attribution.AttributedSource
jiangEtAl2019MagicAngleChargeOrder =
  Attribution.mkDOISource
    "Yuhang Jiang, Xing Lai, Kenji Watanabe, Takashi Taniguchi, Kristjan Haule, Jie Mao, Eva Y. Andrei"
    "Charge order and broken rotational symmetry in magic-angle twisted bilayer graphene"
    "Nature 573, 91-95"
    "2019"
    "10.1038/s41586-019-1460-4"
    "https://doi.org/10.1038/s41586-019-1460-4"
    Attribution.academicArticleSource
    "prior flat-band/twistronics charge-order context cited by Gao et al.; this citation does not identify the graphene and Fe5GeTe2 ordering mechanisms"
    Attribution.publicAttribution

record Fe5GeTe2FigureReplay : Set where
  constructor fe5gete2-figure-replay
  field
    source : Attribution.AttributedSourceAtlas

    orderedPhaseLabel : String

    originalBrillouinZoneShown : Bool
    reconstructedSqrt3BrillouinZoneShown : Bool

    originalBandMomentumLabel : String
    replicaBandMomentumLabel : String
    replicaBandsAttributedToSqrt3Reconstruction : Bool

    lowTemperatureK : Nat
    highTemperatureK : Nat

    heliumLampPhotonEnergyTimesTenEv : Nat
    laserPhotonEnergyEv : Nat

    spectralWeightIntegrationLowerMeV : Nat
    spectralWeightIntegrationUpperMeV : Nat
    logarithmicTemperatureFitsShown : Bool

    staticLindhardResponseSimulated : Bool
    preferredNestingVectorsShown : Bool
    flatBandNestingScenarioSimulated : Bool

    pixelLevelARPESArrayReconstructed : Bool
    supplementaryRawIntensityTableImported : Bool

open Fe5GeTe2FigureReplay public

figureReplaySourceAtlas : Attribution.AttributedSourceAtlas
figureReplaySourceAtlas =
  Attribution.mkSourceAtlas
    "Fe5GeTe2 figure-caption replay and magic-angle charge-order context"
    "DASHI.Physics.CondensedMatter.GaoFe5GeTe2FigureReplayExact"
    (Source.gaoEtAl2026 ∷ jiangEtAl2019MagicAngleChargeOrder ∷ [])
    "records explicit published figure/caption coordinates and one cited magic-angle charge-order precedent; does not import raw spectra or identify mechanisms"

canonicalFe5GeTe2FigureReplay : Fe5GeTe2FigureReplay
canonicalFe5GeTe2FigureReplay =
  fe5gete2-figure-replay
    figureReplaySourceAtlas
    "UUU phase"
    true
    true
    "Gamma-bar"
    "K-bar"
    true
    8
    180
    212
    6
    50
    0
    true
    true
    true
    true
    false
    false

record FigureReplayBoundary : Set where
  constructor figure-replay-boundary
  field
    gammaToKReplicaStatementSourcePaid : Bool
    reconstructedBZStatementSourcePaid : Bool
    temperatureSeriesBoundsSourcePaid : Bool
    spectralIntegrationWindowSourcePaid : Bool
    lindhardScenarioSourcePaid : Bool
    jiangMagicAngleChargeOrderOnlyPriorContext : Bool
    sameOrderingMechanismClaimed : Bool
    rawARPESPixelsInvented : Bool

canonicalFigureReplayBoundary : FigureReplayBoundary
canonicalFigureReplayBoundary =
  figure-replay-boundary
    true true true true true true
    false false
