module DASHI.Physics.YangMills.BalabanConfiguredSide4TranslatedWilsonExtractionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL; physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanSU2WilsonPlaquetteSecondJetExact using
  (normSqV)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
open import DASHI.Physics.YangMills.BalabanPath4SU2LiteralPlaquetteLiftExact

------------------------------------------------------------------------
-- Coordinate translations of the configured four-torus.
------------------------------------------------------------------------

shiftForward4Commutes : ∀ firstAxis secondAxis site →
  shiftForward4 firstAxis (shiftForward4 secondAxis site)
  ≡ shiftForward4 secondAxis (shiftForward4 firstAxis site)
shiftForward4Commutes zeroᵢ zeroᵢ
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForward4Commutes zeroᵢ (sucᵢ zeroᵢ)
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForward4Commutes zeroᵢ (sucᵢ (sucᵢ zeroᵢ))
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForward4Commutes zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForward4Commutes (sucᵢ zeroᵢ) zeroᵢ
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForward4Commutes (sucᵢ zeroᵢ) (sucᵢ zeroᵢ)
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForward4Commutes (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ))
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForward4Commutes (sucᵢ zeroᵢ)
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForward4Commutes (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForward4Commutes (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ)
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForward4Commutes (sucᵢ (sucᵢ zeroᵢ))
  (sucᵢ (sucᵢ zeroᵢ))
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForward4Commutes (sucᵢ (sucᵢ zeroᵢ))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForward4Commutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForward4Commutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ zeroᵢ)
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForward4Commutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ zeroᵢ))
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForward4Commutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) = refl

iterateForward4 :
  Axis4 → CyclicIndex side4 → PhysicalBlockL side4 → PhysicalBlockL side4
iterateForward4 axis zeroᵢ site = site
iterateForward4 axis (sucᵢ offset) site =
  iterateForward4 axis offset (shiftForward4 axis site)

iterateForward4Commutes : ∀ iterateAxis offset forwardAxis site →
  iterateForward4 iterateAxis offset (shiftForward4 forwardAxis site)
  ≡ shiftForward4 forwardAxis (iterateForward4 iterateAxis offset site)
iterateForward4Commutes iterateAxis zeroᵢ forwardAxis site = refl
iterateForward4Commutes iterateAxis (sucᵢ offset) forwardAxis site =
  trans
    (cong (iterateForward4 iterateAxis offset)
      (shiftForward4Commutes iterateAxis forwardAxis site))
    (iterateForward4Commutes iterateAxis offset forwardAxis
      (shiftForward4 iterateAxis site))

iterateForward4SumInvariant : ∀ axis offset term →
  siteSum4 (λ site → term (iterateForward4 axis offset site))
  ≡ siteSum4 term
iterateForward4SumInvariant axis zeroᵢ term = refl
iterateForward4SumInvariant axis (sucᵢ offset) term =
  trans
    (periodicForwardReindexing axis
      (λ site → term (iterateForward4 axis offset site)))
    (iterateForward4SumInvariant axis offset term)

translateSite4 :
  PhysicalBlockL side4 → PhysicalBlockL side4 → PhysicalBlockL side4
translateSite4 (pair (pair origin0 origin1) (pair origin2 origin3)) site =
  iterateForward4 axis3 origin3
    (iterateForward4 axis2 origin2
      (iterateForward4 axis1 origin1
        (iterateForward4 axis0 origin0 site)))
  where
  axis0 = zeroᵢ
  axis1 = sucᵢ zeroᵢ
  axis2 = sucᵢ (sucᵢ zeroᵢ)
  axis3 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))

translateSite4ForwardCommutes : ∀ origin axis site →
  translateSite4 origin (shiftForward4 axis site)
  ≡ shiftForward4 axis (translateSite4 origin site)
translateSite4ForwardCommutes
  (pair (pair origin0 origin1) (pair origin2 origin3)) axis site =
  trans
    (cong (iterateForward4 axis3 origin3)
      (trans
        (cong (iterateForward4 axis2 origin2)
          (trans
            (cong (iterateForward4 axis1 origin1)
              (iterateForward4Commutes axis0 origin0 axis site))
            (iterateForward4Commutes axis1 origin1 axis
              (iterateForward4 axis0 origin0 site))))
        (iterateForward4Commutes axis2 origin2 axis
          (iterateForward4 axis1 origin1
            (iterateForward4 axis0 origin0 site)))))
    (iterateForward4Commutes axis3 origin3 axis
      (iterateForward4 axis2 origin2
        (iterateForward4 axis1 origin1
          (iterateForward4 axis0 origin0 site))))
  where
  axis0 = zeroᵢ
  axis1 = sucᵢ zeroᵢ
  axis2 = sucᵢ (sucᵢ zeroᵢ)
  axis3 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))

siteSumTranslationInvariant : ∀ origin term →
  siteSum4 (λ site → term (translateSite4 origin site))
  ≡ siteSum4 term
siteSumTranslationInvariant
  (pair (pair origin0 origin1) (pair origin2 origin3)) term =
  trans
    (iterateForward4SumInvariant axis0 origin0
      (λ site → term
        (iterateForward4 axis3 origin3
          (iterateForward4 axis2 origin2
            (iterateForward4 axis1 origin1 site)))))
    (trans
      (iterateForward4SumInvariant axis1 origin1
        (λ site → term
          (iterateForward4 axis3 origin3
            (iterateForward4 axis2 origin2 site))))
      (trans
        (iterateForward4SumInvariant axis2 origin2
          (λ site → term (iterateForward4 axis3 origin3 site)))
        (iterateForward4SumInvariant axis3 origin3 term)))
  where
  axis0 = zeroᵢ
  axis1 = sucᵢ zeroᵢ
  axis2 = sucᵢ (sucᵢ zeroᵢ)
  axis3 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))

------------------------------------------------------------------------
-- Restrict a configured global side-four tangent to translated coordinates.
------------------------------------------------------------------------

translatedBondRestriction :
  PhysicalBlockL side4 → PhysicalSU2Tangent4 → PhysicalSU2Tangent4
translatedBondRestriction origin tangent component (pair site axis) =
  tangent component (pair (translateSite4 origin site) axis)

translatedBondRestrictionAtSiteAxis : ∀ origin tangent component axis site →
  physicalTangentComponent (translatedBondRestriction origin tangent)
    component axis site
  ≡ physicalTangentComponent tangent component axis
      (translateSite4 origin site)
translatedBondRestrictionAtSiteAxis origin tangent component axis site = refl

translatedBondRestrictionCommutesWithForwardShift :
  ∀ origin tangent component bondAxis shiftAxis site →
  physicalTangentComponent (translatedBondRestriction origin tangent)
    component bondAxis (shiftForward4 shiftAxis site)
  ≡ physicalTangentComponent tangent component bondAxis
      (shiftForward4 shiftAxis (translateSite4 origin site))
translatedBondRestrictionCommutesWithForwardShift
  origin tangent component bondAxis shiftAxis site =
  cong
    (physicalTangentComponent tangent component bondAxis)
    (translateSite4ForwardCommutes origin shiftAxis site)

translatedPlaquetteRestrictionCommutesWithCurl :
  ∀ origin tangent plane site →
  literalForwardDifferenceCurl (translatedBondRestriction origin tangent)
    plane site
  ≡ literalForwardDifferenceCurl tangent plane (translateSite4 origin site)
translatedPlaquetteRestrictionCommutesWithCurl origin tangent plane site =
  lie3Ext
    (componentProof component1)
    (componentProof component2)
    (componentProof component3)
  where
  componentProof : ∀ component →
    lie3Component component
      (literalForwardDifferenceCurl (translatedBondRestriction origin tangent)
        plane site)
    ≡ lie3Component component
      (literalForwardDifferenceCurl tangent plane (translateSite4 origin site))
  componentProof component
    rewrite translatedBondRestrictionCommutesWithForwardShift
      origin tangent component (positivePlaneSecond plane)
      (positivePlaneFirst plane) site
          | translatedBondRestrictionAtSiteAxis
      origin tangent component (positivePlaneSecond plane) site
          | translatedBondRestrictionCommutesWithForwardShift
      origin tangent component (positivePlaneFirst plane)
      (positivePlaneSecond plane) site
          | translatedBondRestrictionAtSiteAxis
      origin tangent component (positivePlaneFirst plane) site = refl

translatedWilsonPlaquetteHessianReindexing :
  ∀ origin tangent plane site →
  literalPlaquetteWilsonSecondVariation
    (translatedBondRestriction origin tangent) plane site
  ≡ literalPlaquetteWilsonSecondVariation tangent plane
      (translateSite4 origin site)
translatedWilsonPlaquetteHessianReindexing origin tangent plane site =
  trans
    (literalPlaquetteWilsonSecondVariationExact
      (translatedBondRestriction origin tangent) plane site)
    (trans
      (cong normSqV
        (translatedPlaquetteRestrictionCommutesWithCurl
          origin tangent plane site))
      (sym (literalPlaquetteWilsonSecondVariationExact tangent plane
        (translateSite4 origin site))))

translatedWilsonPositivePlaneSiteFoldExact : ∀ origin tangent →
  literalWilsonHessianPositivePlaneFold
    (translatedBondRestriction origin tangent)
  ≡ literalWilsonHessianPositivePlaneFold tangent
translatedWilsonPositivePlaneSiteFoldExact origin tangent =
  sumRationalCong positivePlaquettePlanes4 _ _ (λ plane →
    trans
      (sumRationalCong (physicalBlockSites side4) _ _
        (translatedWilsonPlaquetteHessianReindexing origin tangent plane))
      (siteSumTranslationInvariant origin
        (literalPlaquetteWilsonSecondVariation tangent plane)))

globalWilsonToLocalTranslatedBlock : ∀ origin tangent →
  literalWilsonHessianPositivePlaneFold
    (translatedBondRestriction origin tangent)
  ≡ literalWilsonHessianPositivePlaneFold tangent
globalWilsonToLocalTranslatedBlock = translatedWilsonPositivePlaneSiteFoldExact

configuredSide4TranslationCommutationLevel : ProofLevel
configuredSide4TranslationCommutationLevel = machineChecked

translatedWilsonPlaquetteExtractionLevel : ProofLevel
translatedWilsonPlaquetteExtractionLevel = machineChecked

globalWilsonToLocalTranslatedBlockLevel : ProofLevel
globalWilsonToLocalTranslatedBlockLevel = machineChecked
