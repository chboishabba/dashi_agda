module DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovIsomorphismExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Upgrade the Round61 reduced flat ghost inverse to a genuine two-sided
-- inverse between
--
--   * anchored site gauge parameters, and
--   * colourwise mean-zero ghost sources.
--
-- The new analytic input is not external: periodic reindexing already proves
-- that forward and backward shifts preserve the exact side-four site sum.
-- Hence the periodic Laplacian, and therefore the literal flat FP operator,
-- has colourwise mean-zero image.
--
-- For the converse direction, the existing Green commutation identity gives
--
--   G (L f) = L (G f) = f - mean(f).
--
-- Re-anchoring cancels the constant mean exactly.  Thus for every anchored f,
--
--   anchor (G (M0 f)) = f.
--
-- Together with the already-proved right inverse on mean-zero sources this is
-- the exact finite reduced M0^{-1} needed as the base operator for a
-- background log-det expansion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair; allCyclicIndices; four)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Fibre
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as FiniteAverage
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Average
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as Global
import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact as Reindex
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalFaddeevPopovOperatorExact as FP
import DASHI.Physics.YangMills.BalabanP33FaddeevPopovAnchoredGaugeReductionExact as Anchored
import DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovGreenInverseExact as Inverse
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact as Green

------------------------------------------------------------------------
-- Periodic Laplacian has exact zero site sum.
------------------------------------------------------------------------

sumStencilNoWeight :
  ∀ {A : Set} (values : List A)
    (center forward backward : A → ℚ) →
  Sums.sumRational values (λ value →
    (center value + center value) - (forward value + backward value))
  ≡ (Sums.sumRational values center + Sums.sumRational values center)
    - (Sums.sumRational values forward + Sums.sumRational values backward)
sumStencilNoWeight [] center forward backward = ℚRing.solve-∀
sumStencilNoWeight (value ∷ values) center forward backward
  rewrite sumStencilNoWeight values center forward backward = ℚRing.solve-∀

axisLaplacianSiteSumZero :
  ∀ axis (field : Sums.SiteField Average.side4) →
  Reindex.siteSum4 (λ site →
    (field site + field site)
    - (field (Reindex.shiftForward4 axis site)
      + field (Reindex.shiftBackward4 axis site)))
  ≡ 0ℚ
axisLaplacianSiteSumZero axis field =
  trans
    (sumStencilNoWeight
      (Fibre.physicalBlockSites Average.side4)
      field
      (λ site → field (Reindex.shiftForward4 axis site))
      (λ site → field (Reindex.shiftBackward4 axis site)))
    (trans
      (cong
        (λ forwardSum →
          (Reindex.siteSum4 field + Reindex.siteSum4 field)
          - (forwardSum
            + Reindex.siteSum4
                (λ site → field (Reindex.shiftBackward4 axis site))))
        (Reindex.periodicForwardReindexing axis field))
      (trans
        (cong
          (λ backwardSum →
            (Reindex.siteSum4 field + Reindex.siteSum4 field)
            - (Reindex.siteSum4 field + backwardSum))
          (Reindex.periodicBackwardReindexing axis field))
        (ℚRing.solve-∀ (Reindex.siteSum4 field))))

siteLocalLaplacianSumZero :
  ∀ (field : Sums.SiteField Average.side4) →
  Reindex.siteSum4 (Green.siteLocalLaplacian field) ≡ 0ℚ
siteLocalLaplacianSumZero field =
  trans
    (Fubini.sumSwap
      (Fibre.physicalBlockSites Average.side4)
      (allCyclicIndices four)
      (λ site axis →
        (field site + field site)
        - (field (Reindex.shiftForward4 axis site)
          + field (Reindex.shiftBackward4 axis site))))
    (trans
      (Sums.sumRationalCong
        (allCyclicIndices four)
        (λ axis → Reindex.siteSum4 (λ site →
          (field site + field site)
          - (field (Reindex.shiftForward4 axis site)
            + field (Reindex.shiftBackward4 axis site))))
        (λ _ → 0ℚ)
        (λ axis → axisLaplacianSiteSumZero axis field))
      (FiniteAverage.sumRationalConstant (allCyclicIndices four) 0ℚ))

------------------------------------------------------------------------
-- The literal flat FP image is therefore colourwise mean-zero.
------------------------------------------------------------------------

flatFPSource : FP.SiteGaugeParameter4 → FP.SiteGaugeParameter4
flatFPSource parameter (pair coordinate site) =
  FP.flatFaddeevPopovApply parameter (pair coordinate site)

flatFPSourceColourIsLaplacian :
  ∀ parameter coordinate site →
  Kernel.colourSiteField (flatFPSource parameter) coordinate site
  ≡ Green.siteLocalLaplacian
      (Kernel.colourSiteField parameter coordinate) site
flatFPSourceColourIsLaplacian parameter coordinate site =
  Kernel.flatFPColourIsScalarLaplacian parameter coordinate site

flatFPImageColourwiseMeanZero :
  ∀ parameter → Inverse.ColourwiseMeanZero (flatFPSource parameter)
flatFPImageColourwiseMeanZero parameter coordinate =
  trans
    (Sums.sumRationalCong
      (Fibre.physicalBlockSites Average.side4)
      (Kernel.colourSiteField (flatFPSource parameter) coordinate)
      (Green.siteLocalLaplacian
        (Kernel.colourSiteField parameter coordinate))
      (flatFPSourceColourIsLaplacian parameter coordinate))
    (siteLocalLaplacianSumZero
      (Kernel.colourSiteField parameter coordinate))

------------------------------------------------------------------------
-- Green of the flat FP source is the field minus its global mean.
------------------------------------------------------------------------

greenFlatFPSourceExact :
  ∀ parameter coordinate site →
  Inverse.flatGreenGaugeParameter (flatFPSource parameter)
    (pair coordinate site)
  ≡ parameter (pair coordinate site)
    - Global.oneTwoFiftySix
      * Reindex.siteSum4 (Kernel.colourSiteField parameter coordinate)
greenFlatFPSourceExact parameter coordinate site =
  let field = Kernel.colourSiteField parameter coordinate
  in
  trans
    (Green.scalarGreenRespectsPointwise
      (flatFPSourceColourIsLaplacian parameter coordinate) site)
    (trans
      (Green.siteGreenLaplacianCommutes field site)
      (Green.siteGreenLaplacianIdentity field site))

AnchoredAt : FP.SiteGaugeParameter4 → Periodic.Site4 → Set
AnchoredAt parameter anchor =
  ∀ coordinate → parameter (pair coordinate anchor) ≡ 0ℚ

reducedFlatGreenLeftInverse :
  ∀ parameter anchor →
  AnchoredAt parameter anchor →
  ∀ coordinate site →
  Inverse.reducedFlatGreenInverse (flatFPSource parameter) anchor
    (pair coordinate site)
  ≡ parameter (pair coordinate site)
reducedFlatGreenLeftInverse parameter anchor anchored coordinate site =
  let
    mean = Global.oneTwoFiftySix
      * Reindex.siteSum4 (Kernel.colourSiteField parameter coordinate)
  in
  trans
    (cong
      (λ current →
        current
        - Inverse.flatGreenGaugeParameter (flatFPSource parameter)
            (pair coordinate anchor))
      (greenFlatFPSourceExact parameter coordinate site))
    (trans
      (cong
        (λ anchorValue →
          (parameter (pair coordinate site) - mean) - anchorValue)
        (greenFlatFPSourceExact parameter coordinate anchor))
      (trans
        (cong
          (λ anchorParameter →
            (parameter (pair coordinate site) - mean)
            - (anchorParameter - mean))
          (anchored coordinate))
        (ℚRing.solve-∀
          (parameter (pair coordinate site)) mean)))

------------------------------------------------------------------------
-- Exact two-sided reduced inverse package.
------------------------------------------------------------------------

record ReducedFlatFaddeevPopovIsomorphism (anchor : Periodic.Site4) : Set₁ where
  field
    sourceToGauge : FP.SiteGaugeParameter4 → FP.SiteGaugeParameter4
    gaugeToSource : FP.SiteGaugeParameter4 → FP.SiteGaugeParameter4

    sourceToGaugeAnchored : ∀ source →
      Inverse.ColourwiseMeanZero source →
      AnchoredAt (sourceToGauge source) anchor

    gaugeToSourceMeanZero : ∀ parameter →
      Inverse.ColourwiseMeanZero (gaugeToSource parameter)

    rightInverse : ∀ source →
      Inverse.ColourwiseMeanZero source →
      ∀ coordinate site →
      gaugeToSource (sourceToGauge source) (pair coordinate site)
      ≡ source (pair coordinate site)

    leftInverse : ∀ parameter →
      AnchoredAt parameter anchor →
      ∀ coordinate site →
      sourceToGauge (gaugeToSource parameter) (pair coordinate site)
      ≡ parameter (pair coordinate site)

open ReducedFlatFaddeevPopovIsomorphism public

reducedFlatFaddeevPopovIsomorphism :
  ∀ anchor → ReducedFlatFaddeevPopovIsomorphism anchor
reducedFlatFaddeevPopovIsomorphism anchor = record
  { sourceToGauge = λ source → Inverse.reducedFlatGreenInverse source anchor
  ; gaugeToSource = flatFPSource
  ; sourceToGaugeAnchored = λ source meanZero coordinate →
      Inverse.reducedFlatGreenInverseAtAnchorZero source anchor coordinate
  ; gaugeToSourceMeanZero = flatFPImageColourwiseMeanZero
  ; rightInverse = λ source meanZero coordinate site →
      Inverse.reducedFlatGreenRightInverse source anchor meanZero coordinate site
  ; leftInverse = λ parameter anchored coordinate site →
      reducedFlatGreenLeftInverse parameter anchor anchored coordinate site
  }

flatFPImageMeanZeroLevel : ProofLevel
flatFPImageMeanZeroLevel = machineChecked

reducedFlatFaddeevPopovTwoSidedGreenInverseLevel : ProofLevel
reducedFlatFaddeevPopovTwoSidedGreenInverseLevel = machineChecked

literalReducedFaddeevPopovLogDetExpansionLevel : ProofLevel
literalReducedFaddeevPopovLogDetExpansionLevel = conditional
