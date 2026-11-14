module DASHI.Unified.AdelicSpectralPaperTOEExact where

------------------------------------------------------------------------
-- SEPTEMBER 2026 NON-ARCHIMEDEAN SPECTRAL PAPER -> DASHI TOE
--
-- Original source: Research Group for Spectral Geometry and Theoretical
-- Computing, "Non-Archimedean Spectral Dynamics, Discrete Character Trace
-- Formulas, and Provable Ultrametric Representation Invariance"
-- (September 2026).
-- https://github.com/sneed-and-feed/adelic-spectral-zeta/blob/main/papers/nonarchimedean_spectral_dynamics.md
--
-- Source Lean lemmas are owned by the upstream authors. The existing DASHI
-- finite spatial weld, repaired mixing/stopping results, counterexamples,
-- and compiler closure are repository-owned; see the existing source audit,
-- capstone, and provenance of PR #703. This module only attaches THOSE
-- already-owned proof/status results to the canonical TOE graph.
--
-- Status equalities below verify the actual finite obligation compiler.
-- They are NOT additional proofs of the source's analytic, ML, holographic,
-- arbitrary-DAG, or Monster assertions, and are not independent verification
-- that the upstream Lean kernel accepted a theorem.
--
-- Mathematical interpretation:
-- * Finite spectra lie ON the listed circles, not equal whole circles.
-- * log(r_n) = 2 log(2)/N for N=2^n: size exponent 1, not 1/2.
-- * Character/spatial transport is a same-object proof obligation.
-- * RoPE phase, AF, entropy, and DAG routing require separate consumers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)

-- Keep all theorem producers in their existing modules.
import DASHI.EverythingNonArchimedeanSpectralBidi as NonArch
import DASHI.Analysis.NonArchimedeanSpectralBidiObligationExact as Bidi
import DASHI.Analysis.NonArchimedeanSpectralOriginalGoalCapstoneExact as Capstone
import DASHI.Analysis.AdelicSpectralClaimStrengthAuditExact as SourceAudit

sourcePaperAuthor : String
sourcePaperAuthor = "Research Group for Spectral Geometry and Theoretical Computing"

sourcePaperDate : String
sourcePaperDate = "September 2026"

sourcePaperPath : String
sourcePaperPath =
  "sneed-and-feed/adelic-spectral-zeta/papers/nonarchimedean_spectral_dynamics.md"

priorDASHIIntegration : String
priorDASHIIntegration = "chboishabba/dashi_agda PR #703 and the current-master source audit"

-- Positive finite-source and DASHI compiler results. These types refer to
-- the ORIGINAL obligations; no second spectral model is created here.

toeFiniteSpatialCircleClosed :
  Bidi.compileMissing Bidi.spatialSpectralCircle ≡ []
toeFiniteSpatialCircleClosed = Bidi.finiteSpatialCoreClosed

toeFiniteTwistedPowerClosed :
  Bidi.compileMissing Bidi.spatialTwistedPower ≡ []
toeFiniteTwistedPowerClosed = refl

toeLiteralSpectrumTowerClosed :
  Bidi.compileMissing Bidi.literalOneStepSpectrumUnion ≡ []
toeLiteralSpectrumTowerClosed = Bidi.spectrumTowerRepoClosed

toePrefactoredFiniteMixingClosed :
  Bidi.compileMissing Bidi.prefactoredL2PowerMixing ≡ []
toePrefactoredFiniteMixingClosed = Bidi.prefactoredMixingClosed

toeConstructiveFiniteStoppingTailClosed :
  Bidi.compileMissing Bidi.setDependentStoppingSurvivalBound ≡ []
toeConstructiveFiniteStoppingTailClosed =
  Bidi.constructiveSetDependentStoppingTailClosed

-- Keep the source's stronger prose assertions outside the closed cut.
-- These are exactly the existing compiler's negative/open receipts.

toeDirectedSizeSigmaHalfRejected :
  Bidi.compileMissing Bidi.directedRadiusSigmaHalf
    ≡ Bidi.rejectedDirectedRadiusSizeExponentHalf ∷ []
toeDirectedSizeSigmaHalfRejected = refl

toeArbitraryDAGCoverNeedsConstruction :
  Bidi.compileMissing Bidi.arbitraryDagCover
    ≡ Bidi.needGraphToDecompositionProducer ∷ []
toeArbitraryDAGCoverNeedsConstruction = refl

toeDepthSparsityNeedsQuantitativeBound :
  Bidi.compileMissing Bidi.depthDecaySparsity
    ≡ Bidi.needDepthDecayProducer ∷ []
toeDepthSparsityNeedsQuantitativeBound = refl

toeBoundaryEntropyNeedsSameObjectWeld :
  Bidi.compileMissing Bidi.contractedBoundaryEntropy
    ≡ Bidi.needBoundaryEntropySameObjectWeld ∷ []
toeBoundaryEntropyNeedsSameObjectWeld = refl

toeRoPEOptimalityNeedsModelConsumer :
  Bidi.compileMissing Bidi.ropeOptimality
    ≡ Bidi.needModelLevelRoPEConsumerTheorem ∷ []
toeRoPEOptimalityNeedsModelConsumer = refl

toeMultiPrimeSparsityNonPromotion :
  SourceAudit.MultiPrimeBoundary.proseSparsityClaimMayBePromoted
    SourceAudit.canonicalMultiPrimeBoundary ≡ false
toeMultiPrimeSparsityNonPromotion =
  SourceAudit.multiPrimePromotionIsFailClosed

toeHolographySameObjectNonPromotion :
  SourceAudit.HolographicSameObjectBoundary.entropyIsWeldedToContractedBoundaryState
    SourceAudit.canonicalHolographicSameObjectBoundary ≡ false
toeHolographySameObjectNonPromotion =
  SourceAudit.holographicSameObjectIsFailClosed

toeNoAutomaticSpectralToRoPETransfer :
  SourceAudit.CrossFibreBridgeBoundary.spectralToRoPEBridgeIsAutomatic
    SourceAudit.canonicalCrossFibreBridgeBoundary ≡ false
toeNoAutomaticSpectralToRoPETransfer =
  SourceAudit.crossFibreAutomaticTransportIsRejected

toeOriginalAdvertisedChainHasNoLiveProducer :
  Capstone.PostClosureBoundary.advertisedChainHasLiveProducer
    Capstone.canonicalPostClosureBoundary ≡ false
toeOriginalAdvertisedChainHasNoLiveProducer =
  Capstone.originalAdvertisedChainHasNoLiveProducer
