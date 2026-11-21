module DASHI.Physics.YangMills.YMClayOriginalR445NativeF19WeightedPhysicalSourceBIDIExact where

------------------------------------------------------------------------
-- P0 ACTUAL original Wilson-GIBBS native R445 -> F19 effective source.
-- Steelman BIDI weld: not a new YM measure, density, block or clock.
--
-- Reverse physical endpoint: original E1 cutoff-3 native block,
-- original finite real SU(N) Gibbs normalized expectation of every
-- 64-coarse-link Wilson observable.
-- Forward existing producers:
--   1. YMClayNative1024WeightedWilsonReindexExact: original actual
--      Wilson Gibbs on all 1024 positive side-four links, 896
--      spectator links fully present IN THE BOLTZMANN WEIGHT;
--   2. YMClayOriginalF19R445Native64HolonomySquareExact: ORIGINAL
--      nativeSUNBlockLinks = F19 physical 64-block pair products,
--      conditional on its candidate finite 64-index normalization;
--   3. YMClayOriginalWilsonCanonicalBlockedMarkF19Exact: physical
--      same-Z numerator/partition normalized effective F19 density
--      for EVERY coarse observable, not a bare n=1 Wilson weight.
--
-- The two BIDI arrows meet at the very SAME original weighted
-- integral; source congruence retains its full interacting density.
--
-- This finite theorem is a SOURCE-WRITTEN Agda candidate; an existing
-- upstream 64-index refl normalization and count transports remain
-- kernel UNVERIFIED. No assumption of E1 continuum, CMP116 physical
-- marked Wilson decay, complex-star RP or H_OS spectrum.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)
import Data.Vec.Base as Vec

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral

import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Native
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayNative1024WeightedWilsonReindexExact as Original
import DASHI.Physics.YangMills.YMClayOriginalWilsonCanonicalBlockedMarkF19Exact as F19
import DASHI.Physics.YangMills.YMClayOriginalF19R445Native64HolonomySquareExact as NativeWeld

module _
  {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
  (exponential : Exp.StrictPositiveRealExponential)
  (beta : ℝ)
  (source : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
  (bilateral : Bilateral.OneLinkSUNBilateralHaar theory source)
  (ordered : Ordered.OneLinkOrderedHaarAlgebra source)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  -- SOURCE native R445 Wilson mark, on the ACTUAL original full
  -- 1024-link canonical configuration, before any effective averaging.
  originalNativeR445MarkedNumerator :
    (Vec.Vec Link 64 → ℝ) → ℝ
  originalNativeR445MarkedNumerator observable =
    Haar.productIntegral source
      (λ canonical →
        Original.originalWilsonVectorWeight
          theory traceData exponential beta canonical
        *ℝ observable
          (NativeWeld.originalNativeCoarse64
            theory traceData exponential beta source bilateral ordered
            canonical))

  -- The canonical F19 mark is on the SAME canonical 1024-link vector,
  -- with the SAME original Gibbs weight; the only difference is the
  -- source-normalized blocked observable on that very same vector.
  originalNativeR445NumeratorIsOriginalF19 :
    ∀ observable →
    originalNativeR445MarkedNumerator observable
      ≡ F19.Mark.canonicalOriginalMarkedNumerator
          theory traceData exponential beta source
          (F19.sortedSourceCoarseObservable
            theory traceData exponential beta source bilateral ordered
            observable)
  originalNativeR445NumeratorIsOriginalF19 observable =
    Original.productIntegralCongruent source
      (λ canonical →
        Original.originalWilsonVectorWeight
          theory traceData exponential beta canonical
        *ℝ observable
          (NativeWeld.originalNativeCoarse64
            theory traceData exponential beta source bilateral ordered
            canonical))
      (λ canonical →
        Original.originalWilsonVectorWeight
          theory traceData exponential beta canonical
        *ℝ F19.canonicalSourceCoarseObservable
          theory traceData exponential beta source bilateral ordered
          observable canonical)
      (λ canonical →
        cong
          (λ mark →
            Original.originalWilsonVectorWeight
              theory traceData exponential beta canonical *ℝ mark)
          (NativeWeld.originalF19CoarseWilsonObservableEqualsNativeR445
            theory traceData exponential beta source bilateral ordered
            observable canonical))

  originalNativeR445BlockedNormalized :
    (divide : ℝ → ℝ → ℝ) → (Vec.Vec Link 64 → ℝ) → ℝ
  originalNativeR445BlockedNormalized divide observable =
    divide
      (originalNativeR445MarkedNumerator observable)
      (Haar.productIntegral source
        (Original.originalWilsonVectorWeight
          theory traceData exponential beta))

  -- FINITE SAME-SOURCE BIDI target:
  --     [original R445 native SU(N) block]_*(original Wilson Gibbs)
  --        = same original actual F19 weighted effective density.
  -- No bare-coarse Gibbs / no normalized score trick / no dropped
  -- original 896 spectator variables.
  originalNativeR445NormalizedEqualsPhysicalF19Effective :
    (divide : ℝ → ℝ → ℝ) → ∀ observable →
    originalNativeR445BlockedNormalized divide observable
    ≡ F19.originalEffectiveBlockedNormalized
       theory traceData exponential beta source bilateral ordered
       divide observable
  originalNativeR445NormalizedEqualsPhysicalF19Effective
      divide observable =
    trans
      (cong
        (λ numerator →
          divide numerator
            (Haar.productIntegral source
              (Original.originalWilsonVectorWeight
                theory traceData exponential beta)))
        (originalNativeR445NumeratorIsOriginalF19 observable))
      (F19.originalCanonicalBlockedNormalizedEqualsPhysicalEffective
        theory traceData exponential beta source bilateral ordered
        divide observable)

  -- This is an ORIGINAL fixed side4-to-side2 Wilson source identity;
  -- the separate actual changing-cutoff E1 k-indexed physical family
  -- and its uniform continuum convergence remain proof-bearing data.
