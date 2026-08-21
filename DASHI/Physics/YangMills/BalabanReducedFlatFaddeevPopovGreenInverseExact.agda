module DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovGreenInverseExact where

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
-- Strengthen the reduced-kernel theorem by constructing an explicit Green
-- right inverse on the colourwise mean-zero ghost source space.
--
-- For source s with zero site sum in each colour, the existing exact side-four
-- scalar Green identity gives
--
--     L (G s) = s - (1/256) sum s = s.
--
-- Re-anchoring G s changes no nearest-neighbour differences, hence changes no
-- flat Faddeev--Popov value.  Therefore
--
--     M0 ( anchor (G s) ) = s
--
-- exactly on the SAME three-colour finite site carrier.  This is the natural
-- base inverse for the later reduced background determinant/log-det expansion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact as Reindex
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as Global
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalFaddeevPopovOperatorExact as FP
import DASHI.Physics.YangMills.BalabanP33FaddeevPopovAnchoredGaugeReductionExact as Anchored
import DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact as Green

ColourwiseMeanZero : FP.SiteGaugeParameter4 → Set
ColourwiseMeanZero source =
  ∀ coordinate →
  Reindex.siteSum4 (Kernel.colourSiteField source coordinate) ≡ 0ℚ

flatGreenGaugeParameter :
  FP.SiteGaugeParameter4 → FP.SiteGaugeParameter4
flatGreenGaugeParameter source (pair coordinate site) =
  Green.scalarGreen (Kernel.colourSiteField source coordinate) site

flatGreenGaugeParameterColourExact :
  ∀ source coordinate site →
  Kernel.colourSiteField (flatGreenGaugeParameter source) coordinate site
  ≡ Green.scalarGreen (Kernel.colourSiteField source coordinate) site
flatGreenGaugeParameterColourExact source coordinate site = refl

flatFPOfGreenMeanZeroExact :
  ∀ source →
  ColourwiseMeanZero source →
  ∀ coordinate site →
  FP.flatFaddeevPopovApply
    (flatGreenGaugeParameter source) (pair coordinate site)
  ≡ source (pair coordinate site)
flatFPOfGreenMeanZeroExact source meanZero coordinate site =
  let
    scalarSource = Kernel.colourSiteField source coordinate
  in
  trans
    (Kernel.flatFPColourIsScalarLaplacian
      (flatGreenGaugeParameter source) coordinate site)
    (trans
      (Green.siteGreenLaplacianIdentity scalarSource site)
      (trans
        (cong
          (λ total → source (pair coordinate site)
            - Global.oneTwoFiftySix * total)
          (meanZero coordinate))
        (ℚRing.solve-∀ (source (pair coordinate site)))))

reducedFlatGreenInverse :
  FP.SiteGaugeParameter4 → Periodic.Site4 → FP.SiteGaugeParameter4
reducedFlatGreenInverse source anchor =
  Anchored.anchoredGaugeParameter (flatGreenGaugeParameter source) anchor

reducedFlatGreenInverseAtAnchorZero :
  ∀ source anchor coordinate →
  reducedFlatGreenInverse source anchor (pair coordinate anchor) ≡ 0ℚ
reducedFlatGreenInverseAtAnchorZero source anchor coordinate =
  Anchored.anchoredGaugeParameterAtAnchorZero
    (flatGreenGaugeParameter source) anchor coordinate

reducedFlatGreenRightInverse :
  ∀ source anchor →
  ColourwiseMeanZero source →
  ∀ coordinate site →
  FP.flatFaddeevPopovApply
    (reducedFlatGreenInverse source anchor)
    (pair coordinate site)
  ≡ source (pair coordinate site)
reducedFlatGreenRightInverse source anchor meanZero coordinate site =
  trans
    (Anchored.anchoredFlatFaddeevPopovExact
      (flatGreenGaugeParameter source) anchor coordinate site)
    (flatFPOfGreenMeanZeroExact source meanZero coordinate site)

reducedFlatFaddeevPopovGreenRightInverseLevel : ProofLevel
reducedFlatFaddeevPopovGreenRightInverseLevel = machineChecked

reducedBackgroundLogDetPerturbationLevel : ProofLevel
reducedBackgroundLogDetPerturbationLevel = conditional
