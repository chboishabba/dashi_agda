module DASHI.Physics.YangMills.YMClayR445OriginalPureHaarBlockWeldExact where

------------------------------------------------------------------------
-- P0.D: EXACT LAST ORIGINAL-SOURCE PURE-HAAR BLOCKING WELD.
--
-- P0.B now constructs a disjoint/complete original 1024-bond list
-- and canonical field-vector reorder; P0.C connects the original
-- native Balaban block to its two original fine positive bonds;
-- YMClayR445FlatPairedHaarIntegrationExact proves 1024 -> 64 Haar.
--
-- Two FINITE source-equality certificates are still required:
--  (1) the original canonical->reordered bond-vector map is realized
--      by a concrete word in original Haar.LinkPermutation,
--  (2) the ORIGINAL native block agrees with flat pair products
--      in the same canonical 64-bond output order.
-- They are fields of the record, not unproved global postulates.
--
-- Under exactly those two welds, the ORIGINAL pure-Haar measure
-- pushes forward to original side-two product Haar. This is NOT
-- a theorem about interacting Wilson Gibbs weights, RG contraction,
-- the continuum, OS spectral support, or any Clay endpoint.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base as Vec using (Vec; [])
open import Data.Product as Pair using (proj₁)
open import Relation.Binary.PropositionalEquality using
  (cong; trans; sym; subst)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNNativeBlockedPositiveHolonomyExact as SUNBlock
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayR445CanonicalBondPermutationCodecExact as Perm
import DASHI.Physics.YangMills.YMClayR445FlatPairedHaarIntegrationExact as Flat
import DASHI.Physics.YangMills.YMClaySUNFinitePairedHaarBlockPushforwardExact as Paired

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  OriginalFineCount : Nat
  OriginalFineCount = Codec.originalPositiveBondCount 4

  originalCoarseCountIs64 :
    Codec.originalPositiveBondCount 2 ≡ 64
  originalCoarseCountIs64 =
    trans (Codec.originalPositiveBondCountFormula 2) refl

  originalCanonicalAs1024 :
    Vec Link OriginalFineCount → Vec Link 1024
  originalCanonicalAs1024 canonical =
    subst (Vec Link) Codec.originalSideFourCountIs1024
      canonical

  originalReorderedAs1024 :
    Vec Link OriginalFineCount → Vec Link 1024
  originalReorderedAs1024 canonical =
    subst (Vec Link)
      Perm.originalR445PairResidualCountIs1024
      (Perm.originalR445CanonicalToPairResidual canonical)

  originalFlatBlock : Vec Link 1024 → Vec Link 64
  originalFlatBlock flat =
    Paired.blockPairs theory oneLink ordered bilateral
      (proj₁
        (Flat.splitFlatPairs theory oneLink ordered bilateral
          {n = 64} {m = 896} flat))

  originalNativeBlockAs64 :
    Vec Link OriginalFineCount → Vec Link 64
  originalNativeBlockAs64 canonical =
    subst (Vec Link) originalCoarseCountIs64
      (Codec.encodeOriginalBonds 2
        (SUNBlock.nativeSUNBlockLinks {m = 1} {l = 1}
          theory
          (Codec.decodeOriginalBonds 4 canonical)))

  record OriginalR445PermutationAndNativeBlockWeld : Set where
    field
      originalPermutationWord : Haar.LinkPermutation 1024

      permutationIsOriginalReorder :
        (canonical : Vec Link OriginalFineCount) →
        Haar.permuteLinks originalPermutationWord
          (originalCanonicalAs1024 canonical)
        ≡ originalReorderedAs1024 canonical

      actualNativeBlockIsFlatPairBlock :
        (canonical : Vec Link OriginalFineCount) →
        originalNativeBlockAs64 canonical
        ≡ originalFlatBlock (originalReorderedAs1024 canonical)

  open OriginalR445PermutationAndNativeBlockWeld

  -- No implicit extensionality of Haar functionals: established
  -- by induction on the ORIGINAL one-link integrator.
  productHaarCongruent :
    ∀ {n} (left right : Vec Link n → ℝ) →
    (∀ links → left links ≡ right links) →
    Haar.productIntegral oneLink left
      ≡ Haar.productIntegral oneLink right
  productHaarCongruent {zero} left right same = same []
  productHaarCongruent {suc n} left right same =
    Haar.integrateCongruent oneLink
      (λ U → Haar.productIntegral oneLink
        (λ tail → left (U Vec.∷ tail)))
      (λ U → Haar.productIntegral oneLink
        (λ tail → right (U Vec.∷ tail)))
      (λ U → productHaarCongruent
        (λ tail → left (U Vec.∷ tail))
        (λ tail → right (U Vec.∷ tail))
        (λ tail → same (U Vec.∷ tail)))

  -- Transport along an ACTUALLY PROVED finite-index cardinality;
  -- not an assumption that distinct finite configuration spaces
  -- are judgmentally equal.
  productHaarTransportLength :
    ∀ {m n} (countEq : m ≡ n)
      (test : Vec Link n → ℝ) →
    Haar.productIntegral {n = m} oneLink
      (λ links → test (subst (Vec Link) countEq links))
    ≡ Haar.productIntegral {n = n} oneLink test
  productHaarTransportLength refl test = refl

  -- The literal original side-four pure-Haar blocked expectation
  -- (the *selected original nativeSU(N) block*, not a mock map)
  -- is the original side-two product Haar integral, relative only
  -- to the outstanding finite index-permutation/native vector weld.
  originalR445PureHaarBlockedIsOriginalCoarseHaar :
    (weld : OriginalR445PermutationAndNativeBlockWeld)
    (observable : Vec Link 64 → ℝ) →
    Haar.productIntegral {n = OriginalFineCount} oneLink
      (λ canonical → observable (originalNativeBlockAs64 canonical))
    ≡ Haar.productIntegral {n = 64} oneLink observable
  originalR445PureHaarBlockedIsOriginalCoarseHaar weld observable =
    trans
      (productHaarCongruent
        (λ canonical → observable (originalNativeBlockAs64 canonical))
        (λ canonical → observable
          (originalFlatBlock
            (Haar.permuteLinks (originalPermutationWord weld)
              (originalCanonicalAs1024 canonical))))
        (λ canonical →
          trans
            (cong observable
              (actualNativeBlockIsFlatPairBlock weld canonical))
            (cong (λ flat → observable (originalFlatBlock flat))
              (sym (permutationIsOriginalReorder weld canonical)))))
      (trans
        (productHaarTransportLength
          Codec.originalSideFourCountIs1024
          (λ flat → observable (originalFlatBlock
            (Haar.permuteLinks (originalPermutationWord weld) flat))))
        (trans
          (Haar.productHaarPermutationInvariant oneLink
            (originalPermutationWord weld)
            (λ flat → observable (originalFlatBlock flat)))
          (Flat.sideFourSideTwoFlatHaarBlock
            theory oneLink ordered bilateral observable)))
