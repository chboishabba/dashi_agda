module DASHI.Physics.YangMills.YMClayOriginalF19R445Native64HolonomySquareExact where

------------------------------------------------------------------------
-- YM P0 original F19 -> NATIVE R445 actual 64-SU(N)-bond holonomy square.
--
-- Do not introduce a second block, field, measure or clock.
-- Existing SOURCE OWNERS:
--   YMClayOriginalF19R445PhysicalBlockedObservableSquareExact
--       : F19 constructed adjacent-sort -> F19 original 64 pair block
--         equals complete R445 128+896 coordinates -> F19 64 block.
--   YMClayR445OriginalNativeParityPairWeldExact
--       : actual original nativeSUNBlockLinks at EACH original coarse
--         bond equals original signed SU(N) multiplication at the
--         phase-zero and phase-one original fine bond lookups.
--   YMClayOriginalF19R445Full1024LabelsP0Exact
--       : the selected 128 and spectator 896 F19/R445 labels match
--         in ORIGINAL source order.
--
-- New bridge: original F19 pair-list coarse output and original R445
-- native coarse output use EXACT SAME 64 original positive bond labels,
-- then transitivity proves the diagram with ACTUAL native blocking.
--
-- In particular the pair-order calculation uses NONCOMMUTATIVE
-- SUN multiplication. The full original 896 spectators remain in
-- the input to the 64-block map, although none is projected into a
-- single blocked two-link holonomy.
--
-- Important: the 64-value pairing lemma below is a CLOSED reduction
-- candidate, not Agda-kernel verified; its proof asks the kernel
-- to normalize original 1024 F19 labels / R445 source cartesian pair
-- order. Do not call this a proved source theorem without acceptance.
--
-- This finite source equality does NOT supply original Wilson W1/W3
-- physical large-field/cutoff estimates, continuum E1 or same-H gap.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Vec.Base as Vec

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNNativeBlockedPositiveHolonomyExact as SUNBlock
import DASHI.Physics.YangMills.YMClayR445OriginalNativeParityPairWeldExact as NativeParity
import DASHI.Physics.YangMills.YMClayR445OriginalAxialBondParityInjectiveExact as Parity
import DASHI.Physics.YangMills.YMClayR445CanonicalBondPermutationCodecExact as R445
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Native
import DASHI.Physics.YangMills.YMClayNativeSideFourPairSpectatorSortProgramExact as F19Order
import DASHI.Physics.YangMills.YMClayOriginalF19R445Full1024LabelsP0Exact as SameLabels
import DASHI.Physics.YangMills.YMClayOriginalF19R445PhysicalBlockedObservableSquareExact as F19Block
import DASHI.Physics.YangMills.YMClayOriginalWilsonCanonicalBlockedMarkF19Exact as Physical
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

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

  -- Exact ORIGINAL native field, decoded from the same canonical
  -- original 1024 positive-bond vector as F19's physical source.
  originalNativeCoarse64 :
    Vec.Vec Link (Codec.originalPositiveBondCount 4) →
    Vec.Vec Link (Codec.originalPositiveBondCount 2)
  originalNativeCoarse64 original =
    Codec.encodeOriginalBonds 2
      (SUNBlock.nativeSUNBlockLinks {m = 1} {l = 1}
        theory (Codec.decodeOriginalBonds 4 original))

  -- Source-selected ordered physical R445 native two-link products,
  -- evaluated on the ORIGINAL positive coarse bond enumeration.
  originalExplicitParityCoarse64 :
    Vec.Vec Link (Codec.originalPositiveBondCount 4) →
    Vec.Vec Link (Codec.originalPositiveBondCount 2)
  originalExplicitParityCoarse64 original =
    let fine = Codec.decodeOriginalBonds 4 original in
    Codec.encodeOriginalBonds 2
      (λ bond →
        SUN.sunMultiply theory
          (fine (Parity.originalR445SelectedFineBond bond Torus.zeroᵢ))
          (fine (Parity.originalR445SelectedFineBond bond
            (Torus.sucᵢ Torus.zeroᵢ))))

  -- This part is already paid: source ORIGINAL native 64 block
  -- is exactly the selected ordered parity-pair multiplication.
  originalNative64IsExplicitParity64 :
    ∀ original →
    originalNativeCoarse64 original
      ≡ originalExplicitParityCoarse64 original
  originalNative64IsExplicitParity64 original =
    let fine = Codec.decodeOriginalBonds 4 original in
    Codec.originalBondsEncodePointwise 2
      (SUNBlock.nativeSUNBlockLinks {m = 1} {l = 1}
        theory fine)
      (λ bond →
        SUN.sunMultiply theory
          (fine (Parity.originalR445SelectedFineBond bond Torus.zeroᵢ))
          (fine (Parity.originalR445SelectedFineBond bond
            (Torus.sucᵢ Torus.zeroᵢ))))
      (λ (Torus.pair site axis) →
        NativeParity.originalR445NativeBlockAgreesExplicitParity
          theory fine site axis)

  originalF19SortedCoarse64 :
    Vec.Vec Link Native.Count → Vec.Vec Link 64
  originalF19SortedCoarse64 original =
    Physical.coarseFromSortedOriginal
      theory traceData exponential beta source bilateral linear
      (R445.originalR445CanonicalToPairResidual original)

  -- This is the single source-specific, finite 64-INDEX ordering
  -- computation still requiring KERNEL reduction. F19's selected
  -- 128 original labels are literally cartesian(CoarseBond,phase),
  -- and the suffix is the identical 896 original physical spectators.
  --
  -- We transport the already established full-1024 F19 target
  -- equality, then ask source definitions to normalize the 64
  -- original adjacent pair-products to the same parity products.
  originalF19Sorted64AreNativeParity64 :
    ∀ (original : Vec.Vec Link Native.Count) →
    originalF19SortedCoarse64 original
    ≡
    originalExplicitParityCoarse64 original
  originalF19Sorted64AreNativeParity64 original
    rewrite SameLabels.originalF19Complete1024LabelOrderMatchesR445
      theory = refl

  -- The TWO distinct routes from the SAME ORIGINAL canonical Wilson
  -- configuration now end at the same original 64 coarse SU(N) values:
  --
  --    canonical U --F19 adjacent swaps--> 128+896 --F19 block--> 64
  --       |                                              |
  --       | original fine decoder                         | =
  --       v                                              v
  --    original native R445 field ------------native block--> 64
  --
  -- Both 64-link outputs are original bond-ordered source vectors.
  originalF19AndNativeR445Actual64CommutingSquare :
    ∀ (original : Vec.Vec Link Native.Count) →
    F19Block.originalF19BlockedLinksOnR445Coordinates
      theory traceData exponential beta source bilateral linear
      original
    ≡
    originalF19SortedCoarse64 original
  originalF19AndNativeR445Actual64CommutingSquare original =
    F19Block.originalF19BlockedLinksOnR445Coordinates
      theory traceData exponential beta source bilateral linear
      original

  originalPhysicalF19Blocked64EqualsNativeR445 :
    ∀ (original : Vec.Vec Link Native.Count) →
    originalF19SortedCoarse64 original
    ≡ originalNativeCoarse64 original
  originalPhysicalF19Blocked64EqualsNativeR445 original =
    trans
      (originalF19Sorted64AreNativeParity64 original)
      (sym (originalNative64IsExplicitParity64 original))

-- The prior original F19 normalized real Wilson Gibbs theorem supplies
-- the physical finite observable equality ONCE these actual source
-- 64-link index equalities type-check; it does NOT instantiate the
-- all-cutoff analytic Wilson W1/W3 and E1 continuum hypotheses.
