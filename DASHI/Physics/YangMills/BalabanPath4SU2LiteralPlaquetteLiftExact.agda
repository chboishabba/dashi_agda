module DASHI.Physics.YangMills.BalabanPath4SU2LiteralPlaquetteLiftExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; _+_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL; physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanSU2WilsonPlaquetteSecondJetExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
  using (shiftForward4; siteSum4)

------------------------------------------------------------------------
-- The literal su(2) value carried by one configured positive bond.
------------------------------------------------------------------------

physicalTangentAtSiteAxisAsLie3 :
  PhysicalSU2Tangent4 → Axis4 → PhysicalBlockL side4 → Lie3
physicalTangentAtSiteAxisAsLie3 tangent axis site =
  lie3
    (physicalTangentComponent tangent component1 axis site)
    (physicalTangentComponent tangent component2 axis site)
    (physicalTangentComponent tangent component3 axis site)

------------------------------------------------------------------------
-- The four positively-oriented link values around one plaquette.
------------------------------------------------------------------------

record LiteralPlaquetteFourLinks : Set where
  constructor fourLinks
  field
    firstLink secondLink thirdLink fourthLink : Lie3

open LiteralPlaquetteFourLinks public

literalPlaquetteFourLinks :
  PhysicalSU2Tangent4 → PositivePlaquettePlane4 →
  PhysicalBlockL side4 → LiteralPlaquetteFourLinks
literalPlaquetteFourLinks tangent plane site =
  fourLinks
    (physicalTangentAtSiteAxisAsLie3 tangent
      (positivePlaneFirst plane) site)
    (physicalTangentAtSiteAxisAsLie3 tangent
      (positivePlaneSecond plane)
      (shiftForward4 (positivePlaneFirst plane) site))
    (physicalTangentAtSiteAxisAsLie3 tangent
      (positivePlaneFirst plane)
      (shiftForward4 (positivePlaneSecond plane) site))
    (physicalTangentAtSiteAxisAsLie3 tangent
      (positivePlaneSecond plane) site)

literalPlaquetteJet :
  PhysicalSU2Tangent4 → PositivePlaquettePlane4 →
  PhysicalBlockL side4 → SU2SecondJet
literalPlaquetteJet tangent plane site =
  plaquetteJet
    (firstLink links) (secondLink links) (thirdLink links) (fourthLink links)
  where
  links = literalPlaquetteFourLinks tangent plane site

literalPlaquetteLinearCurl :
  PhysicalSU2Tangent4 → PositivePlaquettePlane4 →
  PhysicalBlockL side4 → Lie3
literalPlaquetteLinearCurl tangent plane site =
  plaquetteLinearCurl
    (firstLink links) (secondLink links) (thirdLink links) (fourthLink links)
  where
  links = literalPlaquetteFourLinks tangent plane site

------------------------------------------------------------------------
-- The same curvature written as forward differences.
------------------------------------------------------------------------

forwardDifferenceLie3 :
  Axis4 → (PhysicalBlockL side4 → Lie3) → PhysicalBlockL side4 → Lie3
forwardDifferenceLie3 axis fld site =
  fld (shiftForward4 axis site) +v negV (fld site)

literalForwardDifferenceCurl :
  PhysicalSU2Tangent4 → PositivePlaquettePlane4 →
  PhysicalBlockL side4 → Lie3
literalForwardDifferenceCurl tangent plane site =
  forwardDifferenceLie3
    (positivePlaneFirst plane)
    (physicalTangentAtSiteAxisAsLie3 tangent (positivePlaneSecond plane))
    site
  +v negV
    (forwardDifferenceLie3
      (positivePlaneSecond plane)
      (physicalTangentAtSiteAxisAsLie3 tangent (positivePlaneFirst plane))
      site)

curlComponentRearrangeRaw : ∀ a b c d →
  (a + b) + (- c + - d) ≡ (b + - d) + - (c + - a)
curlComponentRearrangeRaw = ℚRing.solve-∀

literalPlaquetteLinearCurlEqualsForwardDifferenceCurl :
  ∀ tangent plane site →
  literalPlaquetteLinearCurl tangent plane site
  ≡ literalForwardDifferenceCurl tangent plane site
literalPlaquetteLinearCurlEqualsForwardDifferenceCurl tangent plane site =
  lie3Ext
    (curlComponentRearrangeRaw (x a) (x b) (x c) (x d))
    (curlComponentRearrangeRaw (y a) (y b) (y c) (y d))
    (curlComponentRearrangeRaw (z a) (z b) (z c) (z d))
  where
  links = literalPlaquetteFourLinks tangent plane site
  a = firstLink links
  b = secondLink links
  c = thirdLink links
  d = fourthLink links

------------------------------------------------------------------------
-- Lift the exact one-plaquette Wilson theorem through sites and six planes.
------------------------------------------------------------------------

literalPlaquetteWilsonSecondVariation :
  PhysicalSU2Tangent4 → PositivePlaquettePlane4 →
  PhysicalBlockL side4 → ℚ
literalPlaquetteWilsonSecondVariation tangent plane site =
  wilsonPlaquetteSecondVariation (literalPlaquetteJet tangent plane site)

literalPlaquetteCurlNormSq :
  PhysicalSU2Tangent4 → PositivePlaquettePlane4 →
  PhysicalBlockL side4 → ℚ
literalPlaquetteCurlNormSq tangent plane site =
  normSqV (literalForwardDifferenceCurl tangent plane site)

literalPlaquetteWilsonSecondVariationExact :
  ∀ tangent plane site →
  literalPlaquetteWilsonSecondVariation tangent plane site
  ≡ literalPlaquetteCurlNormSq tangent plane site
literalPlaquetteWilsonSecondVariationExact tangent plane site =
  trans
    (singlePlaquetteWilsonSecondVariationEqualsCurlNormSq
      (firstLink links) (secondLink links) (thirdLink links) (fourthLink links))
    (cong normSqV
      (literalPlaquetteLinearCurlEqualsForwardDifferenceCurl tangent plane site))
  where
  links = literalPlaquetteFourLinks tangent plane site

literalWilsonHessianPositivePlaneFold : PhysicalSU2Tangent4 → ℚ
literalWilsonHessianPositivePlaneFold tangent =
  sumRational positivePlaquettePlanes4
    (λ plane → siteSum4
      (literalPlaquetteWilsonSecondVariation tangent plane))

literalDiscreteCurlEnergy : PhysicalSU2Tangent4 → ℚ
literalDiscreteCurlEnergy tangent =
  sumRational positivePlaquettePlanes4
    (λ plane → siteSum4 (literalPlaquetteCurlNormSq tangent plane))

literalWilsonHessianPositivePlaneFoldExact : ∀ tangent →
  literalWilsonHessianPositivePlaneFold tangent
  ≡ literalDiscreteCurlEnergy tangent
literalWilsonHessianPositivePlaneFoldExact tangent =
  sumRationalCong positivePlaquettePlanes4
    (λ plane → siteSum4 (literalPlaquetteWilsonSecondVariation tangent plane))
    (λ plane → siteSum4 (literalPlaquetteCurlNormSq tangent plane))
    (λ plane →
      sumRationalCong (physicalBlockSites side4)
        (literalPlaquetteWilsonSecondVariation tangent plane)
        (literalPlaquetteCurlNormSq tangent plane)
        (literalPlaquetteWilsonSecondVariationExact tangent plane))

literalWilsonHessianEqualsCurlEnergy : ∀ tangent →
  literalWilsonHessianPositivePlaneFold tangent
  ≡ literalDiscreteCurlEnergy tangent
literalWilsonHessianEqualsCurlEnergy = literalWilsonHessianPositivePlaneFoldExact

physicalTangentAtSiteAxisAsLie3Level : ProofLevel
physicalTangentAtSiteAxisAsLie3Level = machineChecked

literalPlaquetteFourLinksLevel : ProofLevel
literalPlaquetteFourLinksLevel = machineChecked

literalPlaquetteWilsonSecondVariationLevel : ProofLevel
literalPlaquetteWilsonSecondVariationLevel = machineChecked

literalWilsonHessianPositivePlaneFoldLevel : ProofLevel
literalWilsonHessianPositivePlaneFoldLevel = machineChecked
