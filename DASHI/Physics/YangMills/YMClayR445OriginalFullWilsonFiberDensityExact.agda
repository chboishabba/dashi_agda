module DASHI.Physics.YangMills.YMClayR445OriginalFullWilsonFiberDensityExact where

------------------------------------------------------------------------
-- P0.E: FULL-LATTICE SOURCE WRITTEN WILSON EFFECTIVE FIBER DENSITY.
--
-- Original side-four SU(N) Gibbs weight, NOT a synthetic 2-link test:
--   exp(-S_W^{n=3}(U))
-- exactly evaluated on the original canonical 1024-bond decoder.
--
-- Uses the proved P0.B canonical 128-selected+896-residual vector
-- encoder/decoder and 64 relative SU(N) links U. Each coarse W
-- is reconstituted from native pair (U,U^{-1}W), with all 896
-- remaining original fine bonds included literally.
--
-- This file constructs the full interacting positive fiber density,
-- proves strict positivity under the already existing original
-- one-link strict Haar integration authority, and proves the exact
-- native SU(N) pair-product recovery of all 64 coarse coordinates.
--
-- The weighted ALL-PARTITION disintegration equality with the
-- actual original Gibbs source is a SEPARATE open theorem requiring
-- original canonical Haar permutation and weighted finite Fubini.
-- Positive rho alone does NOT supply its UV effective-bare decay.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Product as Pair using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; trans; sym; subst)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _<ℝ_; _≤ℝ_; _*ℝ_; -ℝ_; mulOneʳ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.CompactLieGroupCore as Group
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayR445CanonicalBondPermutationCodecExact as Perm
import DASHI.Physics.YangMills.YMClayR445FlatPairedHaarIntegrationExact as Flat
import DASHI.Physics.YangMills.YMClaySUNFinitePairedHaarBlockPushforwardExact as Paired
import DASHI.Physics.YangMills.YMClaySUNTwoLinkHaarEffectiveFiberDensityExact as Fiber

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  Coarse : Set
  Coarse = Vec Link 64

  Relative : Set
  Relative = Vec Link 64

  Interior : Set
  Interior = Vec Link 896

  FinePairs : Set
  FinePairs = Vec (Link × Link) 64

  nativePairReconstitute :
    ∀ {n} → Vec Link n → Vec Link n → Vec (Link × Link) n
  nativePairReconstitute [] [] = []
  nativePairReconstitute (W ∷ coarse) (U ∷ relative) =
    (U , SUN.sunMultiply theory (SUN.sunInverse theory U) W)
      ∷ nativePairReconstitute coarse relative

  originalR445ReconstructedFlatFine :
    Coarse → Relative → Interior → Vec Link 1024
  originalR445ReconstructedFlatFine coarse relative interior =
    Flat.appendVec
      (Flat.flattenPairs theory oneLink ordered bilateral
        (nativePairReconstitute coarse relative))
      interior

  originalR445ReconstructedCanonicalFine :
    Coarse → Relative → Interior →
    Vec Link (Codec.originalPositiveBondCount 4)
  originalR445ReconstructedCanonicalFine coarse relative interior =
    Perm.originalR445PairResidualToCanonical
      (subst (Vec Link)
        (sym Perm.originalR445PairResidualCountIs1024)
        (originalR445ReconstructedFlatFine coarse relative interior))

  -- Actual original side-four periodic SU(N) bond field, decoded
  -- through the already proved canonical bond finite enumeration.
  originalR445ReconstructedPhysicalFine :
    Coarse → Relative → Interior → Variable.SUNPeriodicLinks theory 3
  originalR445ReconstructedPhysicalFine coarse relative interior =
    Codec.decodeOriginalBonds 4
      (originalR445ReconstructedCanonicalFine coarse relative interior)

  -- This IS the selected ORIGINAL Wilson interaction, not an
  -- independently chosen coarse action or Gaussian approximation.
  originalR445ReconstructedWilsonWeight :
    Coarse → Relative → Interior → ℝ
  originalR445ReconstructedWilsonWeight coarse relative interior =
    Variable.periodicSUNGibbsDensity theory traceData exponential
      3 (beta 3)
      (originalR445ReconstructedPhysicalFine coarse relative interior)

  originalR445ReconstructedWilsonWeightPositive :
    (coarse : Coarse) (relative : Relative)
    (interior : Interior) →
    0ℝ <ℝ originalR445ReconstructedWilsonWeight
      coarse relative interior
  originalR445ReconstructedWilsonWeightPositive coarse relative interior =
    Exp.expPositive exponential
      (-ℝ_
        (Variable.periodicSUNWilsonAction
          theory traceData 3 (beta 3)
          (originalR445ReconstructedPhysicalFine
            coarse relative interior)))

  -- The candidate effective density integrates all *960* original
  -- fine fiber links at fixed native 64-link coarse configuration.
  -- The group-fiber Jacobian here is exactly Haar by native
  -- multiplication invariance, not a speculative exp(ad) determinant.
  originalR445FullInteractingEffectiveDensity : Coarse → ℝ
  originalR445FullInteractingEffectiveDensity coarse =
    Haar.productIntegral {n = 64} oneLink
      (λ relative →
        Haar.productIntegral {n = 896} oneLink
          (λ interior →
            originalR445ReconstructedWilsonWeight
              coarse relative interior))

  originalR445FullEffectiveDensityStrictlyPositive :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink) →
    (coarse : Coarse) →
    0ℝ <ℝ originalR445FullInteractingEffectiveDensity coarse
  originalR445FullEffectiveDensityStrictlyPositive strict coarse =
    Ordered.productIntegralStrictlyPositive
      oneLink strict
      (λ relative →
        Haar.productIntegral {n = 896} oneLink
          (λ interior →
            originalR445ReconstructedWilsonWeight
              coarse relative interior))
      (λ relative →
        Ordered.productIntegralStrictlyPositive
          oneLink strict
          (λ interior →
            originalR445ReconstructedWilsonWeight
              coarse relative interior)
          (λ interior →
            originalR445ReconstructedWilsonWeightPositive
              coarse relative interior))

  originalR445FullEffectiveDensityNonnegative :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink)
    (strictToWeak : ∀ {x} → 0ℝ <ℝ x → 0ℝ ≤ℝ x) →
    (coarse : Coarse) →
    0ℝ ≤ℝ originalR445FullInteractingEffectiveDensity coarse
  originalR445FullEffectiveDensityNonnegative strict strictToWeak coarse =
    strictToWeak (originalR445FullEffectiveDensityStrictlyPositive
      strict coarse)

  originalR445CandidateEffectivePartition : ℝ
  originalR445CandidateEffectivePartition =
    Haar.productIntegral {n = 64} oneLink
      originalR445FullInteractingEffectiveDensity

  originalR445CandidateEffectivePartitionPositive :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink) →
    0ℝ <ℝ originalR445CandidateEffectivePartition
  originalR445CandidateEffectivePartitionPositive strict =
    Ordered.productIntegralStrictlyPositive oneLink strict
      originalR445FullInteractingEffectiveDensity
      (originalR445FullEffectiveDensityStrictlyPositive strict)

  -- Exact finite SU(N) recomposition:
  -- native product U*(U^{-1}W) = W for EVERY coarse link and pair.
  originalNativePairRecomposition :
    (U W : Link) →
    SUN.sunMultiply theory U
      (SUN.sunMultiply theory (SUN.sunInverse theory U) W)
    ≡ W
  originalNativePairRecomposition U W =
    trans
      (sym (Group.multiplyAssociative
        (SUN.sunMatrixGroup theory)
        U (SUN.sunInverse theory U) W))
      (trans
        (cong (λ X → SUN.sunMultiply theory X W)
          (Group.inverseRight (SUN.sunMatrixGroup theory) U))
        (Group.identityLeft (SUN.sunMatrixGroup theory) W))

  originalR445AllPairsRecomposeCoarse :
    ∀ {n} (coarse : Vec Link n) (relative : Vec Link n) →
    Paired.blockPairs theory oneLink ordered bilateral
      (nativePairReconstitute coarse relative)
    ≡ coarse
  originalR445AllPairsRecomposeCoarse [] [] = refl
  originalR445AllPairsRecomposeCoarse (W ∷ coarse) (U ∷ relative) =
    cong₂ Vec._∷_
      (originalNativePairRecomposition U W)
      (originalR445AllPairsRecomposeCoarse coarse relative)

  originalR445FlatBlockOfReconstructedFineIsCoarse :
    (coarse : Coarse) (relative : Relative)
    (interior : Interior) →
    Paired.blockPairs theory oneLink ordered bilateral
      (proj₁
        (Flat.splitFlatPairs theory oneLink ordered bilateral
          {n = 64} {m = 896}
          (originalR445ReconstructedFlatFine
            coarse relative interior)))
    ≡ coarse
  originalR445FlatBlockOfReconstructedFineIsCoarse
    coarse relative interior =
    trans
      (cong
        (Paired.blockPairs theory oneLink ordered bilateral)
        (cong proj₁
          (Flat.splitFlattenRoundTrip
            theory oneLink ordered bilateral
            (nativePairReconstitute coarse relative)
            interior)))
      (originalR445AllPairsRecomposeCoarse coarse relative)

  ----------------------------------------------------------------------
  -- P0.E original-Gibbs first-pair transport, with all other original
  -- fine bonds fixed. No factorization of the Wilson action is used.
  --
  -- Source pair order is EXACTLY P0.B's 128 selected fine bonds,
  -- followed by the 896 canonical residual fine bonds. A 1022-link
  -- tail means 126 other pair-bonds + 896 residual bonds; the first
  -- two coordinates are the FIRST original selected pair.
  ----------------------------------------------------------------------

  originalR445FineWilsonWeightAtFirstSelectedPair :
    Vec Link 1022 → Link → Link → ℝ
  originalR445FineWilsonWeightAtFirstSelectedPair tail U V =
    Variable.periodicSUNGibbsDensity
      theory traceData exponential 3 (beta 3)
      (Codec.decodeOriginalBonds 4
        (Perm.originalR445PairResidualToCanonical
          (subst (Vec Link)
            (sym Perm.originalR445PairResidualCountIs1024)
            (U ∷ V ∷ tail))))

  -- This is the actual original 1024-bond Wilson density with the
  -- other 1022 canonical-reordered fine bond values frozen. The
  -- source action may couple this pair to EVERY other link.
  originalR445FirstSelectedPairWeightedNumerator :
    (tail : Vec Link 1022) (observable : Link → ℝ) → ℝ
  originalR445FirstSelectedPairWeightedNumerator tail observable =
    Haar.integrateOne oneLink
      (λ U → Haar.integrateOne oneLink
        (λ V →
          originalR445FineWilsonWeightAtFirstSelectedPair tail U V
            *ℝ observable (SUN.sunMultiply theory U V)))

  originalR445FirstSelectedPairEffectiveDensity :
    (tail : Vec Link 1022) → Link → ℝ
  originalR445FirstSelectedPairEffectiveDensity tail W =
    Haar.integrateOne oneLink
      (λ U →
        originalR445FineWilsonWeightAtFirstSelectedPair
          tail U
          (SUN.sunMultiply theory (SUN.sunInverse theory U) W))

  -- EXACT original-source first-pair change of variables and
  -- effective-density identification. Only native SU(N) Haar
  -- invariance, original group inverse and finite Fubini are used.
  -- This does not infer that the other 63 pairs and 896 interior
  -- links have been integrated into one effective coarse measure.
  originalR445FirstSelectedPairWeightedHaarTransport :
    (tail : Vec Link 1022) (observable : Link → ℝ) →
    originalR445FirstSelectedPairWeightedNumerator tail observable
    ≡ Haar.integrateOne oneLink
        (λ W →
          originalR445FirstSelectedPairEffectiveDensity tail W
            *ℝ observable W)
  originalR445FirstSelectedPairWeightedHaarTransport
      tail observable =
    Fiber.nativeTwoLinkWeightedPushforwardIsEffectiveDensity
      theory oneLink ordered bilateral
      (originalR445FineWilsonWeightAtFirstSelectedPair tail)
      observable

  originalR445FirstSelectedPairPartitionTransport :
    (tail : Vec Link 1022) →
    originalR445FirstSelectedPairWeightedNumerator
      tail (λ _ → 1ℝ)
    ≡ Haar.integrateOne oneLink
        (originalR445FirstSelectedPairEffectiveDensity tail)
  originalR445FirstSelectedPairPartitionTransport tail =
    Fiber.nativeTwoLinkEffectiveDensityPreservesPartition
      theory oneLink ordered bilateral
      (originalR445FineWilsonWeightAtFirstSelectedPair tail)
