module DASHI.Physics.YangMills.YMClayOriginalF19R445PhysicalBlockedObservableSquareExact where

------------------------------------------------------------------------
-- P0 follow-on to the TRUE 1024-bond DECODER commuting square:
-- actual original F19 physical blocked cylinder and every Wilson
-- coarse observable evaluate identically when its input is read
-- through the existing original R445 FULL 128+896 field encoding.
--
-- This is no longer merely label or arbitrary-value equality: it
-- uses the ORIGINAL full interacting F19 owner
-- YMClayOriginalWilsonCanonicalBlockedMarkF19Exact
--   .coarseFromSortedOriginal
--   .canonicalSourceCoarseObservable
-- and the ACTUAL original adjacent-sort permutation, without a
-- replacement block map, field, measure or normalization.
--
-- F19's source coarseFromSortedOriginal is the original 64 ordered
-- two-link SU(N) pair multiplication, via the existing 896-spectator
-- finite decoder. Original R445 *native* block pointwise link identity
-- is already separately produced by
-- YMClayNativeSideFourTwoLinkPairSameObjectExact
--   .originalSUNBlockIsLiteralTwoLinkProduct.
-- Identifying the two sorted coarse vector enumerations is a
-- distinct native 64-bond lookup/codec proof, NOT claimed here.
-- No physical E1/W1/W3 analytic uniform estimates or OS/H claim.
--
-- SOURCE-WRITTEN; PINNED Agda 2.9 KERNEL NOT RUN.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
import Data.Vec.Base as Vec

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClayOriginalWilsonCanonicalBlockedMarkF19Exact as F19
import DASHI.Physics.YangMills.YMClayR445CanonicalBondPermutationCodecExact as R445
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Native
import DASHI.Physics.YangMills.YMClayOriginalF19R445ActualSortedVectorBIDIExact as Weld

module _
  {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
  (exponential : Exp.StrictPositiveRealExponential)
  (beta : ℝ)
  (source : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
  (bilateral : Bilateral.OneLinkSUNBilateralHaar theory source)
  (linear : Ordered.OneLinkOrderedHaarAlgebra source)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  -- ORIGINAL full-source F19 64 ordered coarse SU(N) pair holonomies:
  -- changing ONLY the full 1024-link coordinate presentation from
  -- actual F19 adjacent-sort to original R445 pair/residual encoder
  -- changes NONE of the 64 physical F19 coarse link values.
  originalF19BlockedLinksOnR445Coordinates :
    (original : Vec.Vec Link Native.Count) →
    F19.coarseFromSortedOriginal
      theory traceData exponential beta source bilateral linear
      (Haar.permuteLinks (F19.actualProgram
        theory traceData exponential beta source bilateral linear)
        original)
    ≡
    F19.coarseFromSortedOriginal
      theory traceData exponential beta source bilateral linear
      (R445.originalR445CanonicalToPairResidual original)
  originalF19BlockedLinksOnR445Coordinates original =
    cong
      (F19.coarseFromSortedOriginal
        theory traceData exponential beta source bilateral linear)
      (Weld.originalPhysicalF19ActualSortIsOriginalR445Codec
        theory original)

  -- EVERY original F19 source-owned gauge/Wilson coarse observable.
  -- No new Haar expectation or R445-independent bare coarse action:
  -- both expressions are evaluated on identical source 64-link values.
  originalF19BlockedWilsonObservableSquare :
    (observable : Vec.Vec Link 64 → ℝ)
    (original : Vec.Vec Link Native.Count) →
    F19.canonicalSourceCoarseObservable
      theory traceData exponential beta source bilateral linear
      observable original
    ≡
    observable
      (F19.coarseFromSortedOriginal
        theory traceData exponential beta source bilateral linear
        (R445.originalR445CanonicalToPairResidual original))
  originalF19BlockedWilsonObservableSquare observable original =
    cong observable (originalF19BlockedLinksOnR445Coordinates original)

-- Actual R445.nativeSUNBlockLinks vs these 64 pair results should be
-- connected USING existing literal 2-link product at all 64 bond
-- labels; source-closed conditional finite F19 normalization already
-- exists in original YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.
