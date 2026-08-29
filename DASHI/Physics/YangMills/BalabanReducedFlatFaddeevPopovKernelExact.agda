module DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovKernelExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- DASHI CONTRIBUTION
--
-- Close the remaining flat-ghost kernel theorem on the ACTUAL side-four
-- carrier.  The repository already computed an exact scalar Green convolution
-- G satisfying a two-sided inverse law for
--
--     L + global-average,
--
-- where L is the periodic nearest-neighbour scalar Laplacian.  The physical
-- flat Faddeev--Popov operator is already proved to be exactly this same L in
-- each SU(2) colour coordinate.
--
-- If L f = 0, then
--
--   f = G ((L + avg) f) = G (avg f) = avg f,
--
-- so f is constant.  The anchored gauge representative vanishes at its anchor,
-- hence that constant is zero.  Therefore the anchored/reduced flat FP carrier
-- has NO kernel beyond the removed global gauge modes.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Average
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as Global
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalFaddeevPopovOperatorExact as FP
import DASHI.Physics.YangMills.BalabanP33FaddeevPopovAnchoredGaugeReductionExact as Anchored
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact as Green

colourSiteField :
  FP.SiteGaugeParameter4 → Coordinates.LieCoordinate3 →
  Sums.SiteField Average.side4
colourSiteField parameter coordinate site =
  parameter (pair coordinate site)

flatFPColourIsScalarLaplacian :
  ∀ parameter coordinate site →
  FP.flatFaddeevPopovApply parameter (pair coordinate site)
  ≡ Green.siteLocalLaplacian (colourSiteField parameter coordinate) site
flatFPColourIsScalarLaplacian parameter coordinate site =
  trans
    (FP.flatFaddeevPopovIsPeriodicLaplacian parameter coordinate site)
    refl

zeroFlatFPImpliesZeroScalarLaplacian :
  ∀ parameter coordinate →
  (∀ site →
    FP.flatFaddeevPopovApply parameter (pair coordinate site) ≡ 0ℚ) →
  ∀ site →
    Green.siteLocalLaplacian (colourSiteField parameter coordinate) site
    ≡ 0ℚ
zeroFlatFPImpliesZeroScalarLaplacian parameter coordinate fpZero site =
  trans
    (sym (flatFPColourIsScalarLaplacian parameter coordinate site))
    (fpZero site)

zeroLaplacianConfiguredIsAverage :
  ∀ (field : Sums.SiteField Average.side4) →
  (∀ site → Green.siteLocalLaplacian field site ≡ 0ℚ) →
  ∀ site →
  Green.configuredSiteOperator field site ≡ Average.average0123 field site
zeroLaplacianConfiguredIsAverage field laplacianZero site =
  trans
    (cong₂ _+_ (laplacianZero site) refl)
    refl

zeroLaplacianFieldEqualsAverage :
  ∀ (field : Sums.SiteField Average.side4) →
  (∀ site → Green.siteLocalLaplacian field site ≡ 0ℚ) →
  ∀ site → field site ≡ Average.average0123 field site
zeroLaplacianFieldEqualsAverage field laplacianZero site =
  let
    configuredIsAverage : ∀ selected →
      Green.configuredSiteOperator field selected
      ≡ Average.average0123 field selected
    configuredIsAverage =
      zeroLaplacianConfiguredIsAverage field laplacianZero
  in
  trans
    (sym (Green.configuredSiteGreenLeftInverse field site))
    (trans
      (Green.scalarGreenRespectsPointwise configuredIsAverage site)
      (trans
        (Green.scalarGreenAverageExact field site)
        (trans
          (Green.averageScalarGreenExact field site)
          (sym (Global.average0123EqualsGlobalMean field site)))))

average0123SameAtEverySite :
  ∀ (field : Sums.SiteField Average.side4) left right →
  Average.average0123 field left ≡ Average.average0123 field right
average0123SameAtEverySite field left right =
  trans
    (Global.average0123EqualsGlobalMean field left)
    (sym (Global.average0123EqualsGlobalMean field right))

flatFaddeevPopovKernelIsColourwiseConstant :
  ∀ parameter →
  (∀ coordinate site →
    FP.flatFaddeevPopovApply parameter (pair coordinate site) ≡ 0ℚ) →
  ∀ coordinate left right →
  parameter (pair coordinate left) ≡ parameter (pair coordinate right)
flatFaddeevPopovKernelIsColourwiseConstant parameter fpZero coordinate left right =
  let
    field = colourSiteField parameter coordinate
    laplacianZero : ∀ site → Green.siteLocalLaplacian field site ≡ 0ℚ
    laplacianZero =
      zeroFlatFPImpliesZeroScalarLaplacian parameter coordinate (fpZero coordinate)

    leftAverage : field left ≡ Average.average0123 field left
    leftAverage = zeroLaplacianFieldEqualsAverage field laplacianZero left

    rightAverage : field right ≡ Average.average0123 field right
    rightAverage = zeroLaplacianFieldEqualsAverage field laplacianZero right
  in
  trans
    leftAverage
    (trans
      (average0123SameAtEverySite field left right)
      (sym rightAverage))

anchoredFlatFaddeevPopovKernelTrivial :
  ∀ parameter anchor →
  (∀ coordinate site →
    FP.flatFaddeevPopovApply
      (Anchored.anchoredGaugeParameter parameter anchor)
      (pair coordinate site)
    ≡ 0ℚ) →
  ∀ coordinate site →
  Anchored.anchoredGaugeParameter parameter anchor (pair coordinate site)
  ≡ 0ℚ
anchoredFlatFaddeevPopovKernelTrivial parameter anchor fpZero coordinate site =
  trans
    (flatFaddeevPopovKernelIsColourwiseConstant
      (Anchored.anchoredGaugeParameter parameter anchor)
      fpZero coordinate site anchor)
    (Anchored.anchoredGaugeParameterAtAnchorZero
      parameter anchor coordinate)

reducedFlatFaddeevPopovKernelOnlyGlobalGaugeLevel : ProofLevel
reducedFlatFaddeevPopovKernelOnlyGlobalGaugeLevel = machineChecked

-- The next B1 theorem is now determinant/log-det construction on this
-- kernel-free reduced carrier, followed by the background Taylor expansion.
literalReducedFaddeevPopovLogDetExpansionLevel : ProofLevel
literalReducedFaddeevPopovLogDetExpansionLevel = conditional
