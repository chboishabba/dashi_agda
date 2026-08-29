module DASHI.Physics.YangMills.BalabanSelectedFlatGaugeGramPreservesReducedExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Prove directly on the configured side-four torus that the flat multiplier
-- Gram has zero global mean in each su(2) component.  Each local Laplacian
-- stencil has zero total by periodic forward/backward reindexing, hence the
-- flat Gram lands in the same componentwise-mean-zero quotient used by the
-- selected 12 + 765 reduced KKT presentation.
--
-- This is the quotient-preservation lemma needed to reconstruct the full
-- reduced Schur inverse from the projected gauge Green without silently
-- identifying the regularized full gauge carrier with its mean-zero sector.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as GlobalAverage
import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact as Reindex
import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact as Vec
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact as Green
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeRegularizedGreenExact as FlatGreen
import DASHI.Physics.YangMills.BalabanSelectedCombinedMultiplierSplitExact as Split
import DASHI.Physics.YangMills.BalabanSelectedGaugeMeanDecompositionExact as Mean

axisStencilTotalZero :
  ∀ field axis →
  Reindex.siteSum4 (λ site →
    (field site + field site)
    - (field (Reindex.shiftForward4 axis site)
      + field (Reindex.shiftBackward4 axis site)))
  ≡ 0ℚ
axisStencilTotalZero field axis =
  let
    stencil = λ site →
      (field site + field site)
      - (field (Reindex.shiftForward4 axis site)
        + field (Reindex.shiftBackward4 axis site))

    centerWeighted :
      Reindex.siteSum4 (λ site → field site * 1ℚ)
      ≡ Reindex.siteSum4 field
    centerWeighted = Vec.siteSum4Cong _ _ (λ site → ℚRing.solve-∀ (field site))

    forwardWeighted :
      Reindex.siteSum4
        (λ site → field (Reindex.shiftForward4 axis site) * 1ℚ)
      ≡ Reindex.siteSum4 field
    forwardWeighted =
      trans
        (Vec.siteSum4Cong _ _
          (λ site → ℚRing.solve-∀
            (field (Reindex.shiftForward4 axis site))))
        (Reindex.periodicForwardReindexing axis field)

    backwardWeighted :
      Reindex.siteSum4
        (λ site → field (Reindex.shiftBackward4 axis site) * 1ℚ)
      ≡ Reindex.siteSum4 field
    backwardWeighted =
      trans
        (Vec.siteSum4Cong _ _
          (λ site → ℚRing.solve-∀
            (field (Reindex.shiftBackward4 axis site))))
        (Reindex.periodicBackwardReindexing axis field)

    toWeighted :
      Reindex.siteSum4 stencil
      ≡ Reindex.siteSum4 (λ site → stencil site * 1ℚ)
    toWeighted = Vec.siteSum4Cong _ _
      (λ site → ℚRing.solve-∀ (stencil site))

    distribute = Green.sumStencilDistribute
      (Block.physicalBlockSites Path4.side4)
      field
      (λ site → field (Reindex.shiftForward4 axis site))
      (λ site → field (Reindex.shiftBackward4 axis site))
      (λ _ → 1ℚ)
  in
  trans toWeighted
    (trans distribute
      (trans
        (cong₂ _-_
          (cong₂ _+_ centerWeighted centerWeighted)
          (cong₂ _+_ forwardWeighted backwardWeighted))
        (ℚRing.solve-∀ (Reindex.siteSum4 field))))

siteLocalLaplacianTotalZero :
  ∀ field →
  Reindex.siteSum4 (Green.siteLocalLaplacian field) ≡ 0ℚ
siteLocalLaplacianTotalZero field =
  let
    axes = Torus.allCyclicIndices Torus.four
    stencil = λ axis site →
      (field site + field site)
      - (field (Reindex.shiftForward4 axis site)
        + field (Reindex.shiftBackward4 axis site))
  in
  trans
    (Fubini.sumSwap
      (Block.physicalBlockSites Path4.side4)
      axes
      (λ site axis → stencil axis site))
    (trans
      (Sums.sumRationalCong axes
        (λ axis → Reindex.siteSum4 (stencil axis))
        (λ _ → 0ℚ)
        (axisStencilTotalZero field))
      (ℚRing.solve []))

flatGaugeGramComponentTotalZero :
  ∀ multiplier coordinate →
  Reindex.siteSum4
    (FlatFloor.gaugeMultiplierField
      (FlatGreen.flatGaugeGramApply multiplier) coordinate)
  ≡ 0ℚ
flatGaugeGramComponentTotalZero multiplier coordinate =
  let
    source = FlatFloor.gaugeMultiplierField multiplier coordinate
    target = FlatFloor.gaugeMultiplierField
      (FlatGreen.flatGaugeGramApply multiplier) coordinate
  in
  trans
    (Vec.siteSum4Cong target (Green.siteLocalLaplacian source)
      (λ site → FlatGreen.flatGaugeGramApplyExact multiplier coordinate site))
    (siteLocalLaplacianTotalZero source)

flatGaugeGramApplyReduced :
  ∀ multiplier →
  FlatFloor.FlatGaugeReducedMultiplier
    (FlatGreen.flatGaugeGramApply multiplier)
flatGaugeGramApplyReduced multiplier = record
  { FlatFloor.FlatGaugeReducedMultiplier.coordinateXMeanZero =
      λ site →
        trans
          (GlobalAverage.average0123EqualsGlobalMean
            (FlatFloor.gaugeMultiplierField
              (FlatGreen.flatGaugeGramApply multiplier)
              Coordinates.coordinateX)
            site)
          (trans
            (cong (GlobalAverage.oneTwoFiftySix *_)
              (flatGaugeGramComponentTotalZero
                multiplier Coordinates.coordinateX))
            (ℚRing.solve []))
  ; FlatFloor.FlatGaugeReducedMultiplier.coordinateYMeanZero =
      λ site →
        trans
          (GlobalAverage.average0123EqualsGlobalMean
            (FlatFloor.gaugeMultiplierField
              (FlatGreen.flatGaugeGramApply multiplier)
              Coordinates.coordinateY)
            site)
          (trans
            (cong (GlobalAverage.oneTwoFiftySix *_)
              (flatGaugeGramComponentTotalZero
                multiplier Coordinates.coordinateY))
            (ℚRing.solve []))
  ; FlatFloor.FlatGaugeReducedMultiplier.coordinateZMeanZero =
      λ site →
        trans
          (GlobalAverage.average0123EqualsGlobalMean
            (FlatFloor.gaugeMultiplierField
              (FlatGreen.flatGaugeGramApply multiplier)
              Coordinates.coordinateZ)
            site)
          (trans
            (cong (GlobalAverage.oneTwoFiftySix *_)
              (flatGaugeGramComponentTotalZero
                multiplier Coordinates.coordinateZ))
            (ℚRing.solve []))
  }

flatGaugeGramCenteredExact :
  ∀ multiplier coordinate site →
  Mean.centeredMultiplier (FlatGreen.flatGaugeGramApply multiplier)
    (Torus.pair coordinate site)
  ≡ FlatGreen.flatGaugeGramApply multiplier (Torus.pair coordinate site)
flatGaugeGramCenteredExact multiplier coordinate site =
  Split.centeredMultiplierFixesReduced
    (FlatGreen.flatGaugeGramApply multiplier)
    (flatGaugeGramApplyReduced multiplier)
    coordinate site

selectedFlatGaugeGramPreservesReducedLevel : ProofLevel
selectedFlatGaugeGramPreservesReducedLevel = machineChecked
