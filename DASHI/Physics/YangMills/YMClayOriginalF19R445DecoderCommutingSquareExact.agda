module DASHI.Physics.YangMills.YMClayOriginalF19R445DecoderCommutingSquareExact where

------------------------------------------------------------------------
-- P0 genuine finite square: ORIGINAL canonical full 1024-link field
--     P_F19 (original source-owned adjacent-swap)
--  C ----------------------------------------------> S
--  |                                                  |
--  | decodeOriginalBonds 4                            | decodeField
--  |                                                  | originalR445PairResidualFinite
--  v                                                  v
--  Original fine bond -> Value ---------------------> Original fine bond -> Value
--                       IDENTITY
--
-- Stronger than a two-arrow numeric equality:
--   decode_R445(P_F19 U)(bond) = decodeCanonical(U)(bond)
-- for EACH of the original 1024 fine bonds and arbitrary Value.
--
-- This square reuses original master F19 adjacent sort theorem,
-- original R445 128-selected/896-residual codec, and #1536 full
-- 1024 ordered-label proof candidate. The inverse square is equally
-- exact: R445-to-canonical followed by F19 sort is the identity on
-- every sorted original link vector.
--
-- IMPORTANT: this is a FIELD-COORDINATE isomorphism, not itself the
-- 64-pair SU(N) multiplication map, Wilson Haar Gibbs conditional
-- expectation, E1 continuum measure, RP or reconstructed H_OS.
-- Uncompiled Agda source candidate; no kernel PASS claimed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Data.Vec.Base as Vec

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Single
import DASHI.Physics.YangMills.YMClayNative1024ClosedReindexHaarConsequencesExact as F19
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Sort
import DASHI.Physics.YangMills.YMClayR445CanonicalBondPermutationCodecExact as R445
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayOriginalF19R445ActualSortedVectorBIDIExact as Weld

module _
  {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  where

  -- Upper and side maps, all using ORIGINAL master source owners.
  originalF19Sort :
    ∀ {Value : Set} →
    Vec.Vec Value Single.Count → Vec.Vec Value Single.Count
  originalF19Sort = Sort.permuteLinks (F19.actualPairProgram theory)

  originalR445SortedDecode :
    ∀ {Value : Set} →
    Vec.Vec Value
      (Codec.listLength R445.originalR445PairResidualBondEnumeration)
    → R445.FineBond → Value
  originalR445SortedDecode = Codec.decodeField R445.originalR445PairResidualFinite

  -- The actual COMMUTING SQUARE, pointwise over ALL original bonds.
  -- No function extensionality; 896 spectators are not projected away.
  originalFull1024DecoderSquare :
    ∀ {Value : Set} (original : Vec.Vec Value Single.Count)
      (bond : R445.FineBond) →
    originalR445SortedDecode (originalF19Sort original) bond
      ≡ Codec.decodeOriginalBonds 4 original bond
  originalFull1024DecoderSquare original bond =
    trans
      (cong
        (λ sorted → originalR445SortedDecode sorted bond)
        (Weld.originalPhysicalF19ActualSortIsOriginalR445Codec
          theory original))
      (Codec.decodeEncodeAt R445.originalR445PairResidualFinite
        (Codec.decodeOriginalBonds 4 original) bond)

  -- Reverse route at the level of the full original source vector:
  -- first F19 sort, then original R445 reconstruction, recovers U.
  originalF19SortThenR445Unsort :
    ∀ {Value : Set} (original : Vec.Vec Value Single.Count) →
    R445.originalR445PairResidualToCanonical
      (originalF19Sort original) ≡ original
  originalF19SortThenR445Unsort original =
    trans
      (cong R445.originalR445PairResidualToCanonical
        (Weld.originalPhysicalF19ActualSortIsOriginalR445Codec
          theory original))
      (R445.originalR445CanonicalReorderRoundTrip original)

  -- And the other inverse route for EVERY sorted source value vector.
  originalR445UnsortThenF19Sort :
    ∀ {Value : Set}
      (sorted : Vec.Vec Value
        (Codec.listLength R445.originalR445PairResidualBondEnumeration)) →
    originalF19Sort
      (R445.originalR445PairResidualToCanonical sorted)
      ≡ sorted
  originalR445UnsortThenF19Sort sorted =
    trans
      (Weld.originalPhysicalF19ActualSortIsOriginalR445Codec
        theory (R445.originalR445PairResidualToCanonical sorted))
      (R445.originalR445PairResidualReorderRoundTrip sorted)

-- See actual original native SU(N) 64 coarse holonomy producer
-- YMClayNativeSideFourTwoLinkPairSameObjectExact
--   .originalSUNBlockIsLiteralTwoLinkProduct,
-- and actual original full Gibbs F19 numerator/partition producer
-- YMClayOriginalWilsonCanonicalBlockedMarkF19Exact
--   .originalCanonicalBlockedNormalizedEqualsPhysicalEffective.
-- Those are DIFFERENT downstream physical squares, not consequences
-- of the lossless field-coordinate change alone.
