module DASHI.Physics.Foundations.TSVFOriginalR445AllWordActualPushforwardExact where

-- S10 / HIL07 finite original-source donor.
-- Specialize the EXISTING original side-four 1024-bond Wilson-Gibbs
-- R445->R320 expectation pushforward to every finite observable word.
-- No independently selected coarse Gibbs measure; no invented J.
--
-- Important: the target expectation below is the ACTUAL pushed
-- classical Wilson measure. It is NOT the independently reconstructed
-- Osterwalder-Schrader reflection inner product. Noncommutative
-- observer/OS Gram identification remains an independent leaf.
--
-- Ref: YMClaySUNR445BlockedPushforwardR320CovarianceExact
-- and the original selected Wilson/blocked gauge source.

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 1ℝ; _*ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNR445BlockedPushforwardR320CovarianceExact as R445
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  FineLinks : Set
  FineLinks = R445.FineLinks theory traceData exponential
    betaFine oneLink bilateral divide

  CoarseLinks : Set
  CoarseLinks = R445.CoarseLinks theory traceData exponential
    betaFine oneLink bilateral divide

  originalBlock : FineLinks → CoarseLinks
  originalBlock = R445.originalNativeBlock theory traceData exponential
    betaFine oneLink bilateral divide

  -- Words consist of genuine functions on the original coarse link
  -- carrier, not a new detached SourceDirection syntax.
  CoarseObservable : Set
  CoarseObservable = CoarseLinks → ℝ

  coarseWord : List CoarseObservable → CoarseObservable
  coarseWord [] configuration = 1ℝ
  coarseWord (observable ∷ rest) configuration =
    observable configuration *ℝ coarseWord rest configuration

  originalFineWord : List CoarseObservable → FineLinks → ℝ
  originalFineWord word fine = coarseWord word (originalBlock fine)

  -- This is the actual original fine Gibbs normalized expectation,
  -- not a new measure. The exact original blocked expectation is
  -- definitionally the fine expectation of this pulled-back word.
  originalFiniteWilsonWordMoment : List CoarseObservable → ℝ
  originalFiniteWilsonWordMoment word =
    R445.originalBlockedFineExpectation theory traceData exponential
      betaFine oneLink bilateral divide (coarseWord word)

  -- Makes the precise native original Gibbs source explicit. The
  -- equality is definitional because R445.originalBlockedFineExpectation
  -- already means this physical normalized expectation, not a surrogate.
  originalWordMomentIsActualFineGibbs :
    (word : List CoarseObservable) →
    originalFiniteWilsonWordMoment word
    ≡
    Physical.normalizedExpectation
      (R445.originalFineGibbsMeasure theory traceData exponential
        betaFine oneLink bilateral divide)
      (originalFineWord word)
  originalWordMomentIsActualFineGibbs word = refl

  -- Explicit pointwise R445 word evaluation: the fine source reads
  -- the same ordered coarse observables after the native block map.
  originalWordIsLiteralNativeBlockRead :
    (word : List CoarseObservable) (fine : FineLinks) →
    originalFineWord word fine
    ≡ coarseWord word (originalBlock fine)
  originalWordIsLiteralNativeBlockRead word fine = refl

  actualR445PushedWordMoment : List CoarseObservable → ℝ
  actualR445PushedWordMoment word =
    R445.actualPushedCoarseExpectation theory traceData exponential
      betaFine oneLink bilateral divide (coarseWord word)

  -- REAL source theorem for ALL finite word lengths, including empty,
  -- singleton, all pairs and arbitrary higher moments. The original
  -- physical Gibbs source and its R445 blocked measure are identical.
  actualOriginalR445AllWordMoments :
    (word : List CoarseObservable) →
    originalFiniteWilsonWordMoment word
      ≡ actualR445PushedWordMoment word
  actualOriginalR445AllWordMoments word =
    R445.originalBlockedFineExpectationIsPushforward
      theory traceData exponential betaFine
      oneLink bilateral divide (coarseWord word)

  -- Any real pairing-word operation (concatenation, reversal, star
  -- when sourced separately) is covered at once. This does NOT
  -- silently identify the OS reflection word.
  actualOriginalR445AllPairingWordMoments :
    (pairWord : List CoarseObservable →
                List CoarseObservable → List CoarseObservable) →
    (left right : List CoarseObservable) →
    originalFiniteWilsonWordMoment (pairWord left right)
      ≡ actualR445PushedWordMoment (pairWord left right)
  actualOriginalR445AllPairingWordMoments pairWord left right =
    actualOriginalR445AllWordMoments (pairWord left right)

-- Outstanding: full changing-cutoff renormalized CMP119/122 source,
-- original TSVF observer functional, genuine OS reflection positivity,
-- positive Hilbert/GNS, Stone, physical limits, 5D measured-metric weld.
