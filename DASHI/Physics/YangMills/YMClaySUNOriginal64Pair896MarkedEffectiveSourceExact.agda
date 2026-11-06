module DASHI.Physics.YangMills.YMClaySUNOriginal64Pair896MarkedEffectiveSourceExact where

------------------------------------------------------------------------
-- R445 Y.01: FULL TWO-MARKED ORIGINAL 64-PAIR / 896-SPECTATOR FIBRE
--            EFFECTIVE DENSITY, WITH NO BARE-WILSON SUBSTITUTION.
--
-- The existing SOURCE-EXACT noncommutative Haar reparametrization proves
-- disintegration of ANY genuinely interacting weight, including weights
-- that couple all 128 paired fine links to 896 spectators.  Apply that
-- theorem to one actual two-source affine observable.  The derivative
-- coefficient cannot be assigned a different coarse density because
-- the entire two-source polynomial is transported on the original Haar.
--
-- This is all-arbitrary-weight FINITE physical fibre mathematics. It
-- does NOT identify a hypothetical canonical original 1024-Bond Vec
-- decoder without the existing native pair/spectator permutation proof,
-- and it does not close CMP119's E/R/B/V or continuum RG estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂)
open import Data.Vec.Base using (Vec)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _<ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNWeightedDisjointPairFibreReparamExact as Fibre
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (source : Product.OneLinkProductHaar
      (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory source)
    (linear : Ordered.OneLinkOrderedHaarAlgebra source)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  Pair : Set
  Pair = Fibre.Pair theory source bilateral

  OriginalFineWeight : Set
  OriginalFineWeight = Vec Pair 64 → Vec Link 896 → ℝ

  OriginalCoarseTest : Set
  OriginalCoarseTest = Vec Link 64 → ℝ

  actualTwoMarkedCoarseTest :
    OriginalCoarseTest → OriginalCoarseTest →
    ℝ → ℝ → OriginalCoarseTest
  actualTwoMarkedCoarseTest left right s t coarse =
    (1ℝ +ℝ s *ℝ left coarse)
    *ℝ
    (1ℝ +ℝ t *ℝ right coarse)

  -- The two marks refer only to the actual 64 original ordered
  -- non-Abelian block holonomies, not a separate coarse action.
  actualOriginalFineTwoMarkedNumerator :
    OriginalFineWeight →
    OriginalCoarseTest → OriginalCoarseTest → ℝ → ℝ → ℝ
  actualOriginalFineTwoMarkedNumerator fineWeight left right s t =
    Fibre.finePairsIntegral theory source bilateral
      (λ pairs →
        Product.productIntegral source
          (λ spectators → fineWeight pairs spectators)
          *ℝ
          actualTwoMarkedCoarseTest left right s t
            (Fibre.actualPairBlockVector
              theory source bilateral pairs))

  actualEffectiveTwoMarkedNumerator :
    OriginalFineWeight →
    OriginalCoarseTest → OriginalCoarseTest → ℝ → ℝ → ℝ
  actualEffectiveTwoMarkedNumerator fineWeight left right s t =
    Product.productIntegral source
      (λ blocks →
        Fibre.originalSelected64Pair896SpectatorEffectiveDensity
          theory source bilateral linear fineWeight blocks
        *ℝ actualTwoMarkedCoarseTest left right s t blocks)

  -- The proof is a specialization of the existing genuine fibre theorem,
  -- not a new assertion that integrating a mark commutes with a made-up RG.
  originalFullTwoMarkedFibreEqualsActualEffectiveDensity :
    ∀ (fineWeight : OriginalFineWeight)
      (left right : OriginalCoarseTest) s t →
    actualOriginalFineTwoMarkedNumerator fineWeight left right s t
    ≡ actualEffectiveTwoMarkedNumerator fineWeight left right s t
  originalFullTwoMarkedFibreEqualsActualEffectiveDensity
      fineWeight left right s t =
    Fibre.selected64Pair896SpectatorWeightedDisintegration
      theory source bilateral linear
      fineWeight (actualTwoMarkedCoarseTest left right s t)

  -- The same partition is used to NORMALIZE both entire two-source
  -- functions, not merely their mixed second-order coefficient.  Division
  -- is one selected real scalar operation on both sides.  The displayed
  -- denominator is explicitly Z_aff(0,0), so no second coarse partition
  -- can be injected by an alleged RG covariance identity.
  actualFineNormalizedTwoMarkedSource :
    (divide : ℝ → ℝ → ℝ)
    (fineWeight : OriginalFineWeight)
    (left right : OriginalCoarseTest) s t → ℝ
  actualFineNormalizedTwoMarkedSource
      divide fineWeight left right s t =
    divide
      (actualOriginalFineTwoMarkedNumerator fineWeight left right s t)
      (actualOriginalFineTwoMarkedNumerator
        fineWeight left right 0ℝ 0ℝ)

  actualEffectiveNormalizedTwoMarkedSource :
    (divide : ℝ → ℝ → ℝ)
    (fineWeight : OriginalFineWeight)
    (left right : OriginalCoarseTest) s t → ℝ
  actualEffectiveNormalizedTwoMarkedSource
      divide fineWeight left right s t =
    divide
      (actualEffectiveTwoMarkedNumerator fineWeight left right s t)
      (actualEffectiveTwoMarkedNumerator
        fineWeight left right 0ℝ 0ℝ)

  originalSamePartitionNormalizedMarkedSource :
    (divide : ℝ → ℝ → ℝ)
    ∀ (fineWeight : OriginalFineWeight)
      (left right : OriginalCoarseTest) s t →
    actualFineNormalizedTwoMarkedSource
      divide fineWeight left right s t
    ≡
    actualEffectiveNormalizedTwoMarkedSource
      divide fineWeight left right s t
  originalSamePartitionNormalizedMarkedSource
      divide fineWeight left right s t =
    cong₂ divide
      (originalFullTwoMarkedFibreEqualsActualEffectiveDensity
        fineWeight left right s t)
      (originalFullTwoMarkedFibreEqualsActualEffectiveDensity
        fineWeight left right 0ℝ 0ℝ)

  -- The effective density remains strictly positive on every block
  -- whenever the original interacting weight is pointwise positive:
  -- no sign-changing RG "probability" is silently substituted.
  originalSelectedEffectiveMarkedDensityStrictlyPositive :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration source)
    (fineWeight : OriginalFineWeight)
    (fineWeightPositive :
      ∀ pairs spectators → 0ℝ <ℝ fineWeight pairs spectators) →
    ∀ blocks →
    0ℝ <ℝ
      Fibre.originalSelected64Pair896SpectatorEffectiveDensity
        theory source bilateral linear fineWeight blocks
  originalSelectedEffectiveMarkedDensityStrictlyPositive
      strict fineWeight fineWeightPositive =
    Fibre.originalAllPairsFibreDensityStrictlyPositive
      theory source bilateral strict
      (λ pairs →
        Product.productIntegral source
          (λ spectators → fineWeight pairs spectators))
      (λ pairs →
        Ordered.productIntegralStrictlyPositive source strict
          (λ spectators → fineWeight pairs spectators)
          (fineWeightPositive pairs))

-- The remaining original-native step is to give the reordering of the
-- 1024 Wilson links (128 selected pair links plus 896 spectators) its
-- exact Agda equality witness. The canonical native sorter already
-- constructs the permutation; its resulting target equality must be paid.
