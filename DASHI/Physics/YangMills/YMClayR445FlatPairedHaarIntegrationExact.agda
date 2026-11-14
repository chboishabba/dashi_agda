module DASHI.Physics.YangMills.YMClayR445FlatPairedHaarIntegrationExact where

------------------------------------------------------------------------
-- P0.D: FLAT 2n+m PRODUCT-HAAR -> n PAIRS + m RESIDUALS.
--
-- This pays the finite *order-flattening* part of original R445:
-- the n native SU(N) products of pairwise consecutive fine links
-- have exactly the n-link original product-Haar distribution,
-- and all residual m Haar links integrate away.
--
-- Proof = original iterated productIntegral definition + induction,
-- pairedIntegral introduction, source congruence and already proved
-- all-n native paired Haar block theorem. No extra Haar axiom,
-- new measure, physical UV rate or constructed original bond order.
--
-- The actual original 1024-bond vector must still be identified with
-- this flat pair/residual order through the P0.B source permutation.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Product as Pair using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (cong; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClaySUNFinitePairedHaarBlockPushforwardExact as Paired

two : Nat → Nat
two zero = zero
two (suc n) = suc (suc (two n))

appendVec :
  ∀ {A : Set} {n m : Nat} →
  Vec A n → Vec A m → Vec A (n + m)
appendVec [] right = right
appendVec (x ∷ left) right = x ∷ appendVec left right

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  Pairs : Nat → Set
  Pairs n = Vec (Link × Link) n

  flattenPairs : ∀ {n} → Pairs n → Vec Link (two n)
  flattenPairs [] = []
  flattenPairs ((U , V) ∷ rest) =
    U ∷ V ∷ flattenPairs rest

  splitFlatPairs :
    ∀ {n m} → Vec Link (two n + m) → Pairs n × Vec Link m
  splitFlatPairs {zero} flat = ([] , flat)
  splitFlatPairs {suc n} (U ∷ V ∷ rest)
    with splitFlatPairs {n = n} rest
  ... | (pairs , residual) = ((U , V) ∷ pairs , residual)

  splitFlattenRoundTrip :
    ∀ {n m} (pairs : Pairs n) (residual : Vec Link m) →
    splitFlatPairs {n = n}
      (appendVec (flattenPairs pairs) residual)
    ≡ (pairs , residual)
  splitFlattenRoundTrip [] residual = refl
  splitFlattenRoundTrip ((U , V) ∷ rest) residual
    rewrite splitFlattenRoundTrip rest residual = refl

  -- Existing one-link integral extensionality induces pointwise
  -- congruence for arbitrary finite original product-Haar integrals.
  productIntegralCongruent :
    ∀ {n} (left right : Vec Link n → ℝ) →
    (∀ links → left links ≡ right links) →
    Haar.productIntegral oneLink left
      ≡ Haar.productIntegral oneLink right
  productIntegralCongruent {zero} left right same = same []
  productIntegralCongruent {suc n} left right same =
    Haar.integrateCongruent oneLink
      (λ U → Haar.productIntegral {n = n} oneLink
        (λ tail → left (U ∷ tail)))
      (λ U → Haar.productIntegral {n = n} oneLink
        (λ tail → right (U ∷ tail)))
      (λ U → productIntegralCongruent
        (λ tail → left (U ∷ tail))
        (λ tail → right (U ∷ tail))
        (λ tail → same (U ∷ tail)))

  -- An exact n-pair/m-residual Fubini identity written using only
  -- the SAME original iterated one-link product integration.
  flatHaarIsPairedResidualHaar :
    ∀ {n m} (test : Vec Link (two n + m) → ℝ) →
    Haar.productIntegral oneLink test
    ≡ Paired.pairedIntegral
        theory oneLink ordered bilateral
        (λ pairs →
          Haar.productIntegral {n = m} oneLink
            (λ residual →
              test (appendVec (flattenPairs pairs) residual)))
  flatHaarIsPairedResidualHaar {zero} test = refl
  flatHaarIsPairedResidualHaar {suc n} test =
    Haar.integrateCongruent oneLink
      (λ U → Haar.integrateOne oneLink
        (λ V → Haar.productIntegral oneLink
          (λ tail → test (U ∷ V ∷ tail))))
      (λ U → Haar.integrateOne oneLink
        (λ V → Paired.pairedIntegral
          theory oneLink ordered bilateral
          (λ pairs →
            Haar.productIntegral oneLink
              (λ residual →
                test (U ∷ V ∷
                  appendVec (flattenPairs pairs) residual)))))
      (λ U →
        Haar.integrateCongruent oneLink
          (λ V → Haar.productIntegral oneLink
            (λ tail → test (U ∷ V ∷ tail)))
          (λ V → Paired.pairedIntegral
            theory oneLink ordered bilateral
            (λ pairs →
              Haar.productIntegral oneLink
                (λ residual →
                  test (U ∷ V ∷
                    appendVec (flattenPairs pairs) residual))))
          (λ V →
            flatHaarIsPairedResidualHaar {n = n}
              (λ tail → test (U ∷ V ∷ tail))))

  -- Main genuine all-test Haar theorem in flat coordinates:
  -- the native product of pairs is distributed as original coarse
  -- product Haar. The original interaction weight is NOT constant,
  -- so this theorem is NOT the interacting Wilson RG estimate.
  flatHaarNativeBlockWithResidualIsCoarseHaar :
    ∀ {n m} (observable : Vec Link n → ℝ) →
    Haar.productIntegral {n = two n + m} oneLink
      (λ flat →
        observable
          (Paired.blockPairs theory oneLink ordered bilateral
            (Pair.proj₁ (splitFlatPairs {n = n} flat))))
    ≡ Haar.productIntegral {n = n} oneLink observable
  flatHaarNativeBlockWithResidualIsCoarseHaar {n} {m} observable =
    trans
      (flatHaarIsPairedResidualHaar
        (λ flat → observable
          (Paired.blockPairs theory oneLink ordered bilateral
            (Pair.proj₁ (splitFlatPairs {n = n} flat)))))
      (trans
        (Paired.pairedIntegralCongruent
          theory oneLink ordered bilateral
          (λ pairs → Haar.productIntegral {n = m} oneLink
            (λ residual →
              observable
                (Paired.blockPairs theory oneLink ordered bilateral
                  (Pair.proj₁
                    (splitFlatPairs {n = n}
                      (appendVec (flattenPairs pairs) residual))))))
          (λ pairs → Haar.productIntegral {n = m} oneLink
            (λ _ →
              observable
                (Paired.blockPairs theory oneLink ordered bilateral
                  pairs)))
          (λ pairs →
            productIntegralCongruent
              (λ residual →
                observable
                  (Paired.blockPairs theory oneLink ordered bilateral
                    (Pair.proj₁
                      (splitFlatPairs {n = n}
                        (appendVec (flattenPairs pairs) residual)))))
              (λ _ → observable
                (Paired.blockPairs theory oneLink ordered bilateral
                  pairs))
              (λ residual →
                cong
                  (λ result →
                    observable
                      (Paired.blockPairs theory oneLink ordered bilateral
                        (Pair.proj₁ result)))
                  (splitFlattenRoundTrip pairs residual))))
        (Paired.finiteNativePairedBlockWithUnusedLinks
          theory oneLink ordered bilateral
          {n = n} {m = m} observable))

  -- Literal dimensions of the source R445 4-to-2 step, under
  -- the already constructed P0.B pair/residual vector codec.
  sideFourSideTwoFlatHaarBlock :
    (observable : Vec Link 64 → ℝ) →
    Haar.productIntegral {n = 1024} oneLink
      (λ flat →
        observable
          (Paired.blockPairs theory oneLink ordered bilateral
            (Pair.proj₁ (splitFlatPairs {n = 64} {m = 896} flat))))
    ≡ Haar.productIntegral {n = 64} oneLink observable
  sideFourSideTwoFlatHaarBlock observable =
    flatHaarNativeBlockWithResidualIsCoarseHaar
      {n = 64} {m = 896} observable
