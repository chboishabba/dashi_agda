module DASHI.Physics.YangMills.YMClaySUNFinitePairedHaarBlockPushforwardExact where

------------------------------------------------------------------------
-- R443/R445: ALL-FINITE-N native SU(N) paired Haar-block theorem.
--
-- At any finite number n of disjoint, independently Haar-integrated
-- fine pairs (U_i,V_i), the vector of native ordered products U_i V_i
-- has the EXACT original n-link product Haar distribution:
--
--  integratePairs_n F (mapPairs product)
--    = productIntegral_n F.
--
-- An arbitrary finite number m of unused original Haar links can be
-- integrated out with no change (normalization). The proof is genuine
-- induction from the existing one-link Haar source, bilateral invariance,
-- and scalar normalization, not a new n-link pushforward postulate.
--
-- IMPORTANT: this is an abstract DISJOINT FINITE-PAIR theorem on the
-- same native certified SU(N) link carrier. The exact bond-index
-- permutation witnessing the actual 1024 fine -> 64 coarse R445
-- periodic block as 64 disjoint pairs + 896 unused fine links is
-- NOT constructed here. Original interacting Wilson density control
-- and UV mass-gap estimates remain open.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClaySUNOneLinkHaarConvolutionSourceExact as Convolution

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  PairVector : Nat → Set
  PairVector n = Vec (Link × Link) n

  blockPairs : ∀ {n} → PairVector n → Vec Link n
  blockPairs [] = []
  blockPairs ((U , V) ∷ rest) =
    SUN.sunMultiply theory U V ∷ blockPairs rest

  -- Original product-Haar two-link integration at EACH of n pairs.
  -- This is not an independently supplied pair-measure functional.
  pairedIntegral : ∀ {n} → (PairVector n → ℝ) → ℝ
  pairedIntegral {zero} test = test []
  pairedIntegral {suc n} test =
    Haar.integrateOne oneLink
      (λ U → Haar.integrateOne oneLink
        (λ V →
          pairedIntegral {n = n}
            (λ rest → test ((U , V) ∷ rest))))

  pairedIntegralCongruent :
    ∀ {n} (left right : PairVector n → ℝ) →
    (∀ pairs → left pairs ≡ right pairs) →
    pairedIntegral left ≡ pairedIntegral right
  pairedIntegralCongruent {zero} left right equal =
    equal []
  pairedIntegralCongruent {suc n} left right equal =
    Haar.integrateCongruent oneLink
      (λ U → Haar.integrateOne oneLink
        (λ V → pairedIntegral {n = n}
          (λ rest → left ((U , V) ∷ rest))))
      (λ U → Haar.integrateOne oneLink
        (λ V → pairedIntegral {n = n}
          (λ rest → right ((U , V) ∷ rest))))
      (λ U →
        Haar.integrateCongruent oneLink
          (λ V → pairedIntegral {n = n}
            (λ rest → left ((U , V) ∷ rest)))
          (λ V → pairedIntegral {n = n}
            (λ rest → right ((U , V) ∷ rest)))
          (λ V →
            pairedIntegralCongruent {n = n}
              (λ rest → left ((U , V) ∷ rest))
              (λ rest → right ((U , V) ∷ rest))
              (λ rest → equal ((U , V) ∷ rest))))

  -- This is the source-first ALL-LENGTH proof. Its inductive step
  -- consumes exactly the native two-link Haar convolution theorem.
  finiteNativePairedBlockPreservesProductHaar :
    ∀ {n} (observable : Vec Link n → ℝ) →
    pairedIntegral (λ pairs → observable (blockPairs pairs))
    ≡ Haar.productIntegral {n = n} oneLink observable
  finiteNativePairedBlockPreservesProductHaar {zero} observable = refl
  finiteNativePairedBlockPreservesProductHaar {suc n} observable =
    trans
      (Haar.integrateCongruent oneLink
        (λ U → Haar.integrateOne oneLink
          (λ V → pairedIntegral {n = n}
            (λ pairs → observable
              (SUN.sunMultiply theory U V ∷ blockPairs pairs))))
        (λ U → Haar.integrateOne oneLink
          (λ V → Haar.productIntegral {n = n} oneLink
            (λ coarseTail → observable
              (SUN.sunMultiply theory U V ∷ coarseTail))))
        (λ U →
          Haar.integrateCongruent oneLink
            (λ V → pairedIntegral {n = n}
              (λ pairs → observable
                (SUN.sunMultiply theory U V ∷ blockPairs pairs)))
            (λ V → Haar.productIntegral {n = n} oneLink
              (λ coarseTail → observable
                (SUN.sunMultiply theory U V ∷ coarseTail)))
            (λ V →
              finiteNativePairedBlockPreservesProductHaar {n = n}
                (λ coarseTail → observable
                  (SUN.sunMultiply theory U V ∷ coarseTail)))))
      (Convolution.leftOrderedTwoLinkHaarConvolution
        theory oneLink ordered bilateral
        (λ coarseLink → Haar.productIntegral {n = n} oneLink
          (λ coarseTail → observable (coarseLink ∷ coarseTail))))

  -- A finite vector of unused original product-Haar links integrates
  -- to one total mass. No arbitrary new "discard" measure.
  unusedHaarIntegralOfConstant :
    ∀ {n} (scalar : ℝ) →
    Haar.productIntegral {n = n} oneLink (λ _ → scalar)
      ≡ scalar
  unusedHaarIntegralOfConstant {zero} scalar = refl
  unusedHaarIntegralOfConstant {suc n} scalar =
    trans
      (Haar.integrateCongruent oneLink
        (λ _ → Haar.productIntegral {n = n} oneLink
          (λ _ → scalar))
        (λ _ → scalar)
        (λ _ → unusedHaarIntegralOfConstant {n = n} scalar))
      (Convolution.oneLinkConstantIntegral
        theory oneLink ordered bilateral scalar)

  -- A generic disjoint-pair coordinate decomposition of 2n+m
  -- original links therefore has exact Haar pushforward to n links.
  -- Physically identifying the literal R445 codec with these
  -- coordinates is a separate, visible source obligation.
  finiteNativePairedBlockWithUnusedLinks :
    ∀ {n m} (observable : Vec Link n → ℝ) →
    pairedIntegral {n = n}
      (λ pairs →
        Haar.productIntegral {n = m} oneLink
          (λ _ → observable (blockPairs pairs)))
    ≡ Haar.productIntegral {n = n} oneLink observable
  finiteNativePairedBlockWithUnusedLinks {n} {m} observable =
    trans
      (pairedIntegralCongruent {n = n}
        (λ pairs →
          Haar.productIntegral {n = m} oneLink
            (λ _ → observable (blockPairs pairs)))
        (λ pairs → observable (blockPairs pairs))
        (λ pairs →
          unusedHaarIntegralOfConstant {n = m}
            (observable (blockPairs pairs))))
      (finiteNativePairedBlockPreservesProductHaar {n = n} observable)

  -- Side-four -> side-two R445 CARDINALITIES:
  -- 4*4^4 = 1024 original fine positive bonds,
  -- 4*2^4 =   64 original coarse positive bonds.
  -- If the source codec identifies 64 disjoint two-link pairs,
  -- 896 unused fine bonds remain. This theorem pays exact Haar
  -- integration for THOSE cardinalities; the native codec bijection
  -- between the original site/bond field and these coordinates
  -- is still open and must be explicitly proved.
  sideFourSideTwoCandidatePairHaarWithInterior :
    (observable : Vec Link 64 → ℝ) →
    pairedIntegral {n = 64}
      (λ pairs →
        Haar.productIntegral {n = 896} oneLink
          (λ _ → observable (blockPairs pairs)))
    ≡ Haar.productIntegral {n = 64} oneLink observable
  sideFourSideTwoCandidatePairHaarWithInterior observable =
    finiteNativePairedBlockWithUnusedLinks
      {n = 64} {m = 896} observable
