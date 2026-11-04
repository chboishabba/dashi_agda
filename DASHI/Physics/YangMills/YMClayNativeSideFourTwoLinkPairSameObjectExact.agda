module DASHI.Physics.YangMills.YMClayNativeSideFourTwoLinkPairSameObjectExact where

------------------------------------------------------------------------
-- R445: ACTUAL ORIGINAL SIDE-FOUR 2-LINK GEOMETRY AND SUN PRODUCT.
--
-- Native 4D torus fine side 4 (1024 positive bonds), coarse side 2
-- (64 positive bonds), original M=2, L=2 block path. Prove for
-- EVERY original coarse bond (including periodic endpoints) that the
-- ACTUAL already-selected group-valued native blocked holonomy is
-- exactly the multiplication of two ORIGINAL distinct-labeled fine
-- bond lookups at the original zero-offset block origin and next
-- original positiveStep.
--
-- This is not a second block map. No externally supplied "agrees"
-- witness. The original positiveHolonomy source uses group identity
-- at length zero; the only proof is its EXISTING identityRight law.
-- It specializes to the very SAME original SUN matrix link field
-- and SUNBlock.nativeSUNBlockLinks used by the selected R445
-- physical fine Gibbs measure and its blocked cylinder functional.
--
-- SOURCE-WRITTEN, Agda kernel PENDING. This closes the pointwise
-- selected 2-link multiplication identification, but NOT the
-- 1024-label finite coordinate PERMUTATION proving all 128 pair
-- links are disjoint from one another, the 896-spectator product Haar
-- reordering, continuous Haar, Gibbs density disintegration, RG,
-- continuum clustering, OS or Clay.
--
-- Wilson; Bałaban; exact original DASHI group/block/geometry owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClayNativeBlockedPositiveHolonomyGaugeExact as Block
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as SUNNative
import DASHI.Physics.YangMills.YMClaySUNNativeBlockedPositiveHolonomyExact as SUNBlock
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact as Push
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

module _ {Value : Set} (group : Bond.ExactLinkGroup Value) where

  OriginalFineBond : Set
  OriginalFineBond = Torus.PositiveBond 4

  OriginalCoarseBond : Set
  OriginalCoarseBond = Torus.PositiveBond 2

  OriginalFineLinks : Set
  OriginalFineLinks = Bond.PeriodicBondField 3 Value

  originalFirstFineBond :
    OriginalCoarseBond → OriginalFineBond
  originalFirstFineBond (Torus.pair site axis) =
    Torus.pair (Block.fineBlockOrigin {m = 1} {l = 1} group site) axis

  originalSecondFineBond :
    OriginalCoarseBond → OriginalFineBond
  originalSecondFineBond (Torus.pair site axis) =
    Torus.pair
      (Bond.positiveStep
        (Block.fineBlockOrigin {m = 1} {l = 1} group site) axis)
      axis

  literalOriginalTwoFineLinkProduct :
    OriginalFineLinks → OriginalCoarseBond → Value
  literalOriginalTwoFineLinkProduct fine bond =
    Bond.multiply group
      (fine (originalFirstFineBond bond))
      (fine (originalSecondFineBond bond))

  -- One proof for ALL original 64 native coarse positive bonds.
  -- No need to assume a second block map or an equality of measures.
  originalNativeBlockedLinkIsLiteralTwoFineProduct :
    (fine : OriginalFineLinks) (bond : OriginalCoarseBond) →
    Block.nativeBlockedPositiveLinks {m = 1} {l = 1}
      group fine bond
    ≡ literalOriginalTwoFineLinkProduct fine bond
  originalNativeBlockedLinkIsLiteralTwoFineProduct fine
      (Torus.pair site axis) =
    cong
      (Bond.multiply group
        (fine (originalFirstFineBond (Torus.pair site axis))))
      (Bond.identityRight group
        (fine (originalSecondFineBond (Torus.pair site axis))))

-- Actual original SU(N) matrix-valued selected R445 physical link source.
module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  selectedOriginalGroup : Bond.ExactLinkGroup Link
  selectedOriginalGroup = SUNNative.sunExactSignedLinkGroup theory

  originalSUNSideFourLinks : Set
  originalSUNSideFourLinks = Variable.SUNPeriodicLinks theory 3

  originalSUNSideTwoLinks : Set
  originalSUNSideTwoLinks = Variable.SUNPeriodicLinks theory 1

  originalSUNBlockIsLiteralTwoLinkProduct :
    (fine : originalSUNSideFourLinks)
    (bond : Torus.PositiveBond 2) →
    SUNBlock.nativeSUNBlockLinks {m = 1} {l = 1}
      theory fine bond
    ≡
    literalOriginalTwoFineLinkProduct selectedOriginalGroup fine bond
  originalSUNBlockIsLiteralTwoLinkProduct fine bond =
    originalNativeBlockedLinkIsLiteralTwoFineProduct
      selectedOriginalGroup fine bond


-- Most stringent same-object identity: select the ACTUAL original weighted
-- side-four Gibbs / native blocked-cylinder pushforward owner, then prove
-- that its literal chosen block map is exactly the same 2 fine-bond product.
-- No new Gibbs measure, scalar division, or gauge-field configuration.
module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  actualSelectedWeightedGibbsBlockIsNativePair :
    (fine : Variable.SUNPeriodicLinks theory 3)
    (bond : Torus.PositiveBond 2) →
    Push.actualBlockedLinkMap
      theory traceData exponential betaFine oneLink bilateral divide
      fine bond
    ≡
    literalOriginalTwoFineLinkProduct
      (SUNNative.sunExactSignedLinkGroup theory) fine bond
  actualSelectedWeightedGibbsBlockIsNativePair fine bond =
    originalSUNBlockIsLiteralTwoLinkProduct theory fine bond
