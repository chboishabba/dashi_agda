{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsDirectSourceOSLiteralClayResidualExact where

------------------------------------------------------------------------
-- DIRECT-SOURCE / OS / LITERAL CLAY: POST-MAX-CUT RESIDUAL LEDGER
--
-- This is intentionally NOT a scheduler and NOT a proof-by-status module.
-- It records the exact theorem-bearing source boundaries observed by the
-- source-first capstone after the current max-cut.
--
-- Compiler-owned:
--   * literal affine activity -> exact physical KP datum;
--   * KP condition / cluster expansion / support filtering;
--   * R467 finite upper -> transfer-gap core;
--   * selected Wilson expectation-limit algebra;
--   * continuum covariance -> R281 spectral correlation;
--   * compact-simple classification/package lookup;
--   * B + C -> Round77 Gaussian/Maxwell contradiction;
--   * final literal Clay record assembly.
--
-- Physical/source instantiations still required:
--   H1  literal published CMP116 selected localization + physical rate;
--   H2  actual continuum/OS same-object bridge and exact selected Wilson
--       presentation;
--   H3  exact R281 spectrum = spectrum of that SAME H2 OS reconstruction;
--   H5  one quantitative compact-simple parametric continuation producing the
--       exact finite/H1/H2/H3 package for arbitrary G;
--   C   minimal same-family curvature/OPE/stress source cut required by the
--       full literal endpoint;
--   H6  Gaussian Ward/same-H semantic bridge on that SAME H2/H3 system.
--
-- The finite UV source underneath H5 is already max-cut to A1 + A2; historical
-- BC1/BC2 and stronger R338/R444 decompressions are not reintroduced here.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralSelectedRound467Exact as H1
import DASHI.Physics.YangMills.YangMillsDirectSourceOSRationalContinuumH2Exact as H2Continuum
import DASHI.Physics.YangMills.YangMillsDirectSourceOSSelectedWilsonH2Exact as H2Wilson
import DASHI.Physics.YangMills.YangMillsDirectSourceOSReconstructedSpectrumH3Exact as H3
import DASHI.Physics.YangMills.YangMillsDirectSourceOSCompactSimpleH5Exact as H5
import DASHI.Physics.YangMills.YangMillsDirectSourceOSSameSystemH6Exact as H6
import DASHI.Physics.YangMills.YangMillsClayGoal1CSourceCutRound475Exact as C475
import DASHI.Physics.YangMills.YangMillsClayGoal1A1SourceCutRound473Exact as A1
import DASHI.Physics.YangMills.BalabanA2BetaMarkSourceCoordinateRound250Exact as A2
import DASHI.Physics.YangMills.YangMillsDirectSourceOSLiteralClayMaxCutExact as Capstone

h1LiteralPublishedCMP116ApplicationLevel : ProofLevel
h1LiteralPublishedCMP116ApplicationLevel =
  H1.literalRound467PublishedLiteralSelectedLocalizationLevel

h2ContinuumOSSameObjectLevel : ProofLevel
h2ContinuumOSSameObjectLevel =
  H2Continuum.directRationalContinuumPhysicalInstantiationLevel

h2ExactSelectedWilsonPresentationLevel : ProofLevel
h2ExactSelectedWilsonPresentationLevel =
  H2Wilson.directSelectedWilsonH2SameCarrierPresentationLevel

h3SameOSReconstructedSpectrumLevel : ProofLevel
h3SameOSReconstructedSpectrumLevel =
  H3.directH3SameOSPhysicalInstantiationLevel

h5CompactSimpleParametricContinuationLevel : ProofLevel
h5CompactSimpleParametricContinuationLevel =
  H5.directH5PhysicalParametricContinuationLevel

cExactSameFamilyLocalQFTSourceLevel : ProofLevel
cExactSameFamilyLocalQFTSourceLevel =
  C475.literalRound475CSourceInstantiationLevel

h6SameSystemGaussianWardGapLevel : ProofLevel
h6SameSystemGaussianWardGapLevel =
  H6.directH6SameSystemPhysicalInstantiationLevel

finiteA1CurrentStepSourceLevel : ProofLevel
finiteA1CurrentStepSourceLevel =
  A1.literalRound473A1SourceInstantiationLevel

finiteA2HistoryShellSameObjectLevel : ProofLevel
finiteA2HistoryShellSameObjectLevel =
  A2.literalCMP116BetaMarkIsGeneratedHistoryShellLevel

literalClayCompilerLevel : ProofLevel
literalClayCompilerLevel =
  Capstone.directSourceOSLiteralClayCompilerLevel

literalClayPhysicalInstantiationLevel : ProofLevel
literalClayPhysicalInstantiationLevel =
  Capstone.directSourceOSLiteralClayPhysicalInstantiationLevel
