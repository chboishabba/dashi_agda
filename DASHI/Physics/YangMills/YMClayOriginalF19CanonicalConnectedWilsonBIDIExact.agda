module DASHI.Physics.YangMills.YMClayOriginalF19CanonicalConnectedWilsonBIDIExact where

------------------------------------------------------------------------
-- P0 actual original Wilson finite SOURCE BIDI:
--
-- 1024 canonical original SU(N) Wilson positive bonds
--   == original F19 64 ordered pairs + 896 interacting spectators
--   == original physical 64-link effective density, normalized by
--      the SAME original full Wilson Gibbs partition
--   => EXACT equality of ALL canonical/effective connected two-mark
--      covariances by the already original source THREE-test identity.
--
-- THIS IS NOT a new locality assumption, auxiliary bare coarse Gibbs,
-- independent J, or independent "correlation". Uses the previously
-- source-written ALL-COARSE-OBSERVABLE F19 normalized equality on master:
-- YMClayOriginalWilsonCanonicalBlockedMarkF19Exact
--   .originalCanonicalBlockedNormalizedEqualsPhysicalEffective.
-- The literal F19->original native R445 bond field identification is
-- separate; current #1444 owners supply original bond parity, native
-- Fin origin, link-pair products, and full 896-spectator decoder.
-- Physical all-k Wilson W1/W3 estimates, E1, OS and H remain OPEN.
-- Source-written; Agda kernel acceptance NOT RUN.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong₂)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; _*ℝ_; _-ℝ_)
import Data.Vec.Base as Vec

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClayOriginalWilsonCanonicalBlockedMarkF19Exact as Original

module _
  {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
  (exponential : Exp.StrictPositiveRealExponential)
  (betaFine : ℝ)
  (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
  (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
  (linear : Ordered.OneLinkOrderedHaarAlgebra oneLink)
  (divide : ℝ → ℝ → ℝ)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  OriginalCoarseTest : Set
  OriginalCoarseTest = Vec.Vec Link 64 → ℝ

  canonicalOriginalWilsonExpectation : OriginalCoarseTest → ℝ
  canonicalOriginalWilsonExpectation =
    Original.originalCanonicalBlockedNormalized
      theory traceData exponential betaFine oneLink bilateral linear
      divide

  originalF19EffectiveWilsonExpectation : OriginalCoarseTest → ℝ
  originalF19EffectiveWilsonExpectation =
    Original.originalEffectiveBlockedNormalized
      theory traceData exponential betaFine oneLink bilateral linear
      divide

  productWord : OriginalCoarseTest → OriginalCoarseTest → OriginalCoarseTest
  productWord left right links = left links *ℝ right links

  canonicalOriginalWilsonConnected :
    OriginalCoarseTest → OriginalCoarseTest → ℝ
  canonicalOriginalWilsonConnected left right =
    canonicalOriginalWilsonExpectation (productWord left right) -ℝ
    (canonicalOriginalWilsonExpectation left *ℝ
     canonicalOriginalWilsonExpectation right)

  originalF19EffectiveWilsonConnected :
    OriginalCoarseTest → OriginalCoarseTest → ℝ
  originalF19EffectiveWilsonConnected left right =
    originalF19EffectiveWilsonExpectation (productWord left right) -ℝ
    (originalF19EffectiveWilsonExpectation left *ℝ
     originalF19EffectiveWilsonExpectation right)

  -- Each of the THREE source moments is already handled by ORIGINAL
  -- master F19 all-coarse normalized equality on the actual density.
  originalF19CanonicalMomentEqualsPhysical :
    ∀ word →
    canonicalOriginalWilsonExpectation word ≡
    originalF19EffectiveWilsonExpectation word
  originalF19CanonicalMomentEqualsPhysical =
    Original.originalCanonicalBlockedNormalizedEqualsPhysicalEffective
      theory traceData exponential betaFine oneLink bilateral linear
      divide

  -- The SAME finite canonical source gives the SAME connected covariance,
  -- not only a same partition or one single marked observable.
  originalCanonicalF19ConnectedCovarianceSamePhysical :
    ∀ left right →
    canonicalOriginalWilsonConnected left right ≡
    originalF19EffectiveWilsonConnected left right
  originalCanonicalF19ConnectedCovarianceSamePhysical left right =
    cong₂ _-ℝ_
      (originalF19CanonicalMomentEqualsPhysical
        (productWord left right))
      (cong₂ _*ℝ_
        (originalF19CanonicalMomentEqualsPhysical left)
        (originalF19CanonicalMomentEqualsPhysical right))

  -- Plugging a later *selected actual original native R445* identity
  -- into the already complete finite F19 covariance does NOT change
  -- the source proof. No equality of original effective and BARE
  -- coarse Wilson laws is inferred; the latter is an RG-error theorem.
