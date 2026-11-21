module DASHI.Physics.YangMills.YMClayOriginalF19R445PureHaarReceiverCandidateExact where

------------------------------------------------------------------------
-- P0 STEELMAN BIDI: plug the actual F19/native 64-block square into
-- ALREADY ORIGINAL YMClayR445OriginalPureHaarBlockWeldExact.
--
-- Original receiver is a TWO-FIELD finite source record:
--   permutationIsOriginalReorder
--   actualNativeBlockIsFlatPairBlock
-- This module proposes an explicit instance from ACTUAL selected
-- original F19 adjacent sorting and native R445 two-link block.
--
-- There are two distinct remaining normalization tasks:
--   (A) cast original native F19 LinkPermutation Count to 1024,
--       transport its action along original source cardinalities;
--   (B) show original F19 Torus.Product pair-block decoder and
--       original pure-Haar Data.Product flat-pair decoder yield
--       exactly the same 64 ordered SU(N) products.
--
-- Both are SOURCE-WRITTEN proof candidates. Exact symbolic SymPy 1.14
-- source-shaped F19/R445 identities passed 1024 permutation,
-- 64 noncommutative blocks, 96 plaquette words, and 320 exact Q8
-- SU2 matrix-valued products. This does NOT kernel-check either proof.
-- No new Haar measure, Wilson Gibbs weight, physical W1/W3 estimate,
-- E1 continuum or same-H OS gap is constructed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using
  (cong; trans; sym; subst)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayR445CanonicalBondPermutationCodecExact as Perm
import DASHI.Physics.YangMills.YMClayNative1024ClosedReindexHaarConsequencesExact as OriginalSort
import DASHI.Physics.YangMills.YMClayOriginalF19R445ActualSortedVectorBIDIExact as FullValue
import DASHI.Physics.YangMills.YMClayOriginalF19R445Native64HolonomySquareExact as Native
import DASHI.Physics.YangMills.YMClayR445OriginalPureHaarBlockWeldExact as Receiver

-- This count-transport naturality is generic and exact by pattern
-- matching on the equality proof; it is NOT a source-only postulate.
transportPermutationAction :
  ∀ {Link : Set} {n m : Nat}
    (eq : n ≡ m) (program : Haar.LinkPermutation n)
    (original : Vec.Vec Link n) →
  Haar.permuteLinks
    (subst Haar.LinkPermutation eq program)
    (subst (Vec.Vec Link) eq original)
  ≡ subst (Vec.Vec Link) eq
      (Haar.permuteLinks program original)
transportPermutationAction refl program original = refl

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  -- Full native original adjacent-sort word, carried into exactly the
  -- 1024-link length required by the PREEXISTING R445 receiver.
  originalF19ProgramAsOriginal1024 :
    Haar.LinkPermutation 1024
  originalF19ProgramAsOriginal1024 =
    subst Haar.LinkPermutation
      Codec.originalSideFourCountIs1024
      (OriginalSort.actualPairProgram theory)

  -- No new candidate permutation schedule: the ORIGINAL master
  -- F19 adjacent-swap is the chosen source owner.
  originalF19PermutationIsR445Reorder :
    (canonical : Vec.Vec Link (Codec.originalPositiveBondCount 4)) →
    Haar.permuteLinks originalF19ProgramAsOriginal1024
      (Receiver.originalCanonicalAs1024 theory oneLink ordered bilateral
        canonical)
    ≡ Receiver.originalReorderedAs1024
        theory oneLink ordered bilateral canonical
  originalF19PermutationIsR445Reorder canonical
    rewrite Codec.originalSideFourCountIs1024
          | Perm.originalR445PairResidualCountIs1024 =
    FullValue.originalPhysicalF19ActualSortIsOriginalR445Codec
      theory canonical

  -- Exactly the ORIGINAL source-specific mismatch to inspect locally:
  -- F19 has Torus.Product ordered pair decoding; R445 pure-Haar
  -- Flat.splitFlatPairs uses Data.Product. Both compute the same
  -- source-ordered SU(N) U·V, no commutative rearrangement.
  --
  -- This is a closed normalization CANDIDATE, NOT a kernel receipt.
  originalF19FlatPairBlockAgreement :
    (canonical : Vec.Vec Link (Codec.originalPositiveBondCount 4)) →
    Native.originalF19SortedCoarse64
      theory traceData exponential beta oneLink bilateral ordered
      canonical
    ≡ Receiver.originalFlatBlock
        theory oneLink ordered bilateral
        (Receiver.originalReorderedAs1024
          theory oneLink ordered bilateral canonical)
  originalF19FlatPairBlockAgreement canonical
    rewrite Codec.originalSideFourCountIs1024
          | Perm.originalR445PairResidualCountIs1024 =
    refl

  originalNativeBlockIsOriginalFlatPairBlock :
    (canonical : Vec.Vec Link (Codec.originalPositiveBondCount 4)) →
    Receiver.originalNativeBlockAs64
      theory oneLink ordered bilateral canonical
    ≡ Receiver.originalFlatBlock
        theory oneLink ordered bilateral
        (Receiver.originalReorderedAs1024
          theory oneLink ordered bilateral canonical)
  originalNativeBlockIsOriginalFlatPairBlock canonical =
    trans
      (sym (Native.originalPhysicalF19Blocked64EqualsNativeR445
        theory traceData exponential beta oneLink bilateral ordered
        canonical))
      (originalF19FlatPairBlockAgreement canonical)

  -- The endpoint is the EXACT existing source record, not another
  -- abstract "blocked Haar" carrier. This is only a candidate
  -- until source count transports and pair decoder normalize in Agda.
  originalActualF19PureHaarReceiver :
    Receiver.OriginalR445PermutationAndNativeBlockWeld
      theory oneLink ordered bilateral
  originalActualF19PureHaarReceiver = record
    { originalPermutationWord = originalF19ProgramAsOriginal1024
    ; permutationIsOriginalReorder =
        originalF19PermutationIsR445Reorder
    ; actualNativeBlockIsFlatPairBlock =
        originalNativeBlockIsOriginalFlatPairBlock
    }

  -- Physical interpretation must remain separated: this theorem is
  -- ONLY original unweighted product Haar, with a one-link bi-Haar
  -- law supplied as source. The interacting Wilson density carries
  -- the original 896 spectator dependence and is handled by F19.
  originalNativePureHaarBlockedIsCoarseProductHaar :
    (observable : Vec.Vec Link 64 → ℝ) →
    Haar.productIntegral {n = Codec.originalPositiveBondCount 4}
      oneLink
      (λ canonical → observable
        (Receiver.originalNativeBlockAs64
          theory oneLink ordered bilateral canonical))
    ≡ Haar.productIntegral {n = 64} oneLink observable
  originalNativePureHaarBlockedIsCoarseProductHaar observable =
    Receiver.originalR445PureHaarBlockedIsOriginalCoarseHaar
      theory oneLink ordered bilateral
      originalActualF19PureHaarReceiver observable
