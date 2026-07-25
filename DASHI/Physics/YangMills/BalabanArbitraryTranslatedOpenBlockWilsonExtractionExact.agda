module DASHI.Physics.YangMills.BalabanArbitraryTranslatedOpenBlockWilsonExtractionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational using (ℚ)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL; weakenIndex)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact using
  (shiftForward4)
open import DASHI.Physics.YangMills.BalabanSU2WilsonPlaquetteSecondJetExact
open import DASHI.Physics.YangMills.BalabanPath4SU2LiteralPlaquetteLiftExact using
  ( literalPlaquetteWilsonSecondVariation
  ; literalPlaquetteWilsonSecondVariationExact
  ; literalForwardDifferenceCurl
  )

------------------------------------------------------------------------
-- Concrete forward translation on an arbitrary nonempty cyclic carrier.
------------------------------------------------------------------------

cyclicNext : ∀ {n} → CyclicIndex (suc n) → CyclicIndex (suc n)
cyclicNext {zero} zeroᵢ = zeroᵢ
cyclicNext {suc n} zeroᵢ = sucᵢ zeroᵢ
cyclicNext {suc n} (sucᵢ index) with cyclicNext {n} index
... | zeroᵢ = zeroᵢ
... | sucᵢ next = sucᵢ (sucᵢ next)

iterateCyclicNext :
  ∀ {globalSideMinusOne localSide} →
  CyclicIndex localSide → CyclicIndex (suc globalSideMinusOne) →
  CyclicIndex (suc globalSideMinusOne)
iterateCyclicNext zeroᵢ origin = origin
iterateCyclicNext (sucᵢ offset) origin =
  cyclicNext (iterateCyclicNext offset origin)

iterateWeakenIndex :
  ∀ {globalSideMinusOne localSide}
    (offset : CyclicIndex localSide)
    (origin : CyclicIndex (suc globalSideMinusOne)) →
  iterateCyclicNext (weakenIndex offset) origin
  ≡ iterateCyclicNext offset origin
iterateWeakenIndex zeroᵢ origin = refl
iterateWeakenIndex (sucᵢ offset) origin =
  cong cyclicNext (iterateWeakenIndex offset origin)

three : Nat
three = suc (suc (suc zero))

next4WeakenIndex : ∀ (offset : CyclicIndex three) →
  next4 (weakenIndex offset) ≡ sucᵢ offset
next4WeakenIndex zeroᵢ = refl
next4WeakenIndex (sucᵢ zeroᵢ) = refl
next4WeakenIndex (sucᵢ (sucᵢ zeroᵢ)) = refl

GlobalSite4 : Nat → Set
GlobalSite4 globalSideMinusOne =
  periodicTorus4Definition (suc globalSideMinusOne)

GlobalSU2Tangent4 : Nat → Set
GlobalSU2Tangent4 globalSideMinusOne =
  SU2Component → Axis4 → GlobalSite4 globalSideMinusOne → ℚ

globalShiftForward4 :
  ∀ {n} → Axis4 → GlobalSite4 n → GlobalSite4 n
globalShiftForward4 zeroᵢ (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair (cyclicNext x0) x1) (pair x2 x3)
globalShiftForward4 (sucᵢ zeroᵢ)
  (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 (cyclicNext x1)) (pair x2 x3)
globalShiftForward4 (sucᵢ (sucᵢ zeroᵢ))
  (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair (cyclicNext x2) x3)
globalShiftForward4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair x2 (cyclicNext x3))

translateLocalSiteToGlobal :
  ∀ {n} → GlobalSite4 n → PhysicalBlockL side4 → GlobalSite4 n
translateLocalSiteToGlobal
  (pair (pair origin0 origin1) (pair origin2 origin3))
  (pair (pair local0 local1) (pair local2 local3)) =
  pair
    (pair
      (iterateCyclicNext local0 origin0)
      (iterateCyclicNext local1 origin1))
    (pair
      (iterateCyclicNext local2 origin2)
      (iterateCyclicNext local3 origin3))

------------------------------------------------------------------------
-- Open plaquette bases use coordinates 0,1,2 in the two plaquette axes.
------------------------------------------------------------------------

openPlaquetteBaseSite :
  PositivePlaquettePlane4 → CyclicIndex three → CyclicIndex three →
  CyclicIndex side4 → CyclicIndex side4 → PhysicalBlockL side4
openPlaquetteBaseSite plane01 first second transverse0 transverse1 =
  pair (pair (weakenIndex first) (weakenIndex second))
    (pair transverse0 transverse1)
openPlaquetteBaseSite plane02 first second transverse0 transverse1 =
  pair (pair (weakenIndex first) transverse0)
    (pair (weakenIndex second) transverse1)
openPlaquetteBaseSite plane03 first second transverse0 transverse1 =
  pair (pair (weakenIndex first) transverse0)
    (pair transverse1 (weakenIndex second))
openPlaquetteBaseSite plane12 first second transverse0 transverse1 =
  pair (pair transverse0 (weakenIndex first))
    (pair (weakenIndex second) transverse1)
openPlaquetteBaseSite plane13 first second transverse0 transverse1 =
  pair (pair transverse0 (weakenIndex first))
    (pair transverse1 (weakenIndex second))
openPlaquetteBaseSite plane23 first second transverse0 transverse1 =
  pair (pair transverse0 transverse1)
    (pair (weakenIndex first) (weakenIndex second))

translatedOpenPlaquetteFirstShift :
  ∀ {n} origin plane first second transverse0 transverse1 →
  translateLocalSiteToGlobal origin
    (shiftForward4 (positivePlaneFirst plane)
      (openPlaquetteBaseSite plane first second transverse0 transverse1))
  ≡ globalShiftForward4 (positivePlaneFirst plane)
      (translateLocalSiteToGlobal origin
        (openPlaquetteBaseSite plane first second transverse0 transverse1))
translatedOpenPlaquetteFirstShift
  (pair (pair o0 o1) (pair o2 o3)) plane01 first second t0 t1
  rewrite next4WeakenIndex first | iterateWeakenIndex first o0 = refl
translatedOpenPlaquetteFirstShift
  (pair (pair o0 o1) (pair o2 o3)) plane02 first second t0 t1
  rewrite next4WeakenIndex first | iterateWeakenIndex first o0 = refl
translatedOpenPlaquetteFirstShift
  (pair (pair o0 o1) (pair o2 o3)) plane03 first second t0 t1
  rewrite next4WeakenIndex first | iterateWeakenIndex first o0 = refl
translatedOpenPlaquetteFirstShift
  (pair (pair o0 o1) (pair o2 o3)) plane12 first second t0 t1
  rewrite next4WeakenIndex first | iterateWeakenIndex first o1 = refl
translatedOpenPlaquetteFirstShift
  (pair (pair o0 o1) (pair o2 o3)) plane13 first second t0 t1
  rewrite next4WeakenIndex first | iterateWeakenIndex first o1 = refl
translatedOpenPlaquetteFirstShift
  (pair (pair o0 o1) (pair o2 o3)) plane23 first second t0 t1
  rewrite next4WeakenIndex first | iterateWeakenIndex first o2 = refl

translatedOpenPlaquetteSecondShift :
  ∀ {n} origin plane first second transverse0 transverse1 →
  translateLocalSiteToGlobal origin
    (shiftForward4 (positivePlaneSecond plane)
      (openPlaquetteBaseSite plane first second transverse0 transverse1))
  ≡ globalShiftForward4 (positivePlaneSecond plane)
      (translateLocalSiteToGlobal origin
        (openPlaquetteBaseSite plane first second transverse0 transverse1))
translatedOpenPlaquetteSecondShift
  (pair (pair o0 o1) (pair o2 o3)) plane01 first second t0 t1
  rewrite next4WeakenIndex second | iterateWeakenIndex second o1 = refl
translatedOpenPlaquetteSecondShift
  (pair (pair o0 o1) (pair o2 o3)) plane02 first second t0 t1
  rewrite next4WeakenIndex second | iterateWeakenIndex second o2 = refl
translatedOpenPlaquetteSecondShift
  (pair (pair o0 o1) (pair o2 o3)) plane03 first second t0 t1
  rewrite next4WeakenIndex second | iterateWeakenIndex second o3 = refl
translatedOpenPlaquetteSecondShift
  (pair (pair o0 o1) (pair o2 o3)) plane12 first second t0 t1
  rewrite next4WeakenIndex second | iterateWeakenIndex second o2 = refl
translatedOpenPlaquetteSecondShift
  (pair (pair o0 o1) (pair o2 o3)) plane13 first second t0 t1
  rewrite next4WeakenIndex second | iterateWeakenIndex second o3 = refl
translatedOpenPlaquetteSecondShift
  (pair (pair o0 o1) (pair o2 o3)) plane23 first second t0 t1
  rewrite next4WeakenIndex second | iterateWeakenIndex second o3 = refl

------------------------------------------------------------------------
-- Restriction and pointwise Wilson extraction.
------------------------------------------------------------------------

restrictGlobalTangentToTranslatedOpenBlock :
  ∀ {n} → GlobalSite4 n → GlobalSU2Tangent4 n → PhysicalSU2Tangent4
restrictGlobalTangentToTranslatedOpenBlock origin tangent component
  (pair localSite axis) =
  tangent component axis (translateLocalSiteToGlobal origin localSite)

globalTangentAtSiteAxisAsLie3 :
  ∀ {n} → GlobalSU2Tangent4 n → Axis4 → GlobalSite4 n → Lie3
globalTangentAtSiteAxisAsLie3 tangent axis site =
  lie3
    (tangent component1 axis site)
    (tangent component2 axis site)
    (tangent component3 axis site)

globalForwardDifferenceLie3 :
  ∀ {n} → Axis4 → (GlobalSite4 n → Lie3) → GlobalSite4 n → Lie3
globalForwardDifferenceLie3 axis field site =
  field (globalShiftForward4 axis site) +v negV (field site)

globalForwardDifferenceCurl :
  ∀ {n} → GlobalSU2Tangent4 n → PositivePlaquettePlane4 →
  GlobalSite4 n → Lie3
globalForwardDifferenceCurl tangent plane site =
  globalForwardDifferenceLie3
    (positivePlaneFirst plane)
    (globalTangentAtSiteAxisAsLie3 tangent (positivePlaneSecond plane)) site
  +v negV
    (globalForwardDifferenceLie3
      (positivePlaneSecond plane)
      (globalTangentAtSiteAxisAsLie3 tangent (positivePlaneFirst plane)) site)

lie3Component : SU2Component → Lie3 → ℚ
lie3Component component1 value = x value
lie3Component component2 value = y value
lie3Component component3 value = z value

translatedOpenPlaquetteCurlExact :
  ∀ {n} origin tangent plane first second transverse0 transverse1 →
  literalForwardDifferenceCurl
    (restrictGlobalTangentToTranslatedOpenBlock origin tangent)
    plane (openPlaquetteBaseSite plane first second transverse0 transverse1)
  ≡ globalForwardDifferenceCurl tangent plane
      (translateLocalSiteToGlobal origin
        (openPlaquetteBaseSite plane first second transverse0 transverse1))
translatedOpenPlaquetteCurlExact origin tangent plane first second t0 t1 =
  lie3Ext
    (componentProof component1)
    (componentProof component2)
    (componentProof component3)
  where
  base = openPlaquetteBaseSite plane first second t0 t1

  componentProof : ∀ component →
    lie3Component component
      (literalForwardDifferenceCurl
        (restrictGlobalTangentToTranslatedOpenBlock origin tangent) plane base)
    ≡ lie3Component component
      (globalForwardDifferenceCurl tangent plane
        (translateLocalSiteToGlobal origin base))
  componentProof component1
    rewrite translatedOpenPlaquetteFirstShift
      origin plane first second t0 t1
          | translatedOpenPlaquetteSecondShift
      origin plane first second t0 t1 = refl
  componentProof component2
    rewrite translatedOpenPlaquetteFirstShift
      origin plane first second t0 t1
          | translatedOpenPlaquetteSecondShift
      origin plane first second t0 t1 = refl
  componentProof component3
    rewrite translatedOpenPlaquetteFirstShift
      origin plane first second t0 t1
          | translatedOpenPlaquetteSecondShift
      origin plane first second t0 t1 = refl

globalPlaquetteFourLinks :
  ∀ {n} → GlobalSU2Tangent4 n → PositivePlaquettePlane4 →
  GlobalSite4 n → LiteralPlaquetteFourLinks
globalPlaquetteFourLinks tangent plane site =
  fourLinks
    (globalTangentAtSiteAxisAsLie3 tangent (positivePlaneFirst plane) site)
    (globalTangentAtSiteAxisAsLie3 tangent (positivePlaneSecond plane)
      (globalShiftForward4 (positivePlaneFirst plane) site))
    (globalTangentAtSiteAxisAsLie3 tangent (positivePlaneFirst plane)
      (globalShiftForward4 (positivePlaneSecond plane) site))
    (globalTangentAtSiteAxisAsLie3 tangent (positivePlaneSecond plane) site)

globalPlaquetteWilsonSecondVariation :
  ∀ {n} → GlobalSU2Tangent4 n → PositivePlaquettePlane4 →
  GlobalSite4 n → ℚ
globalPlaquetteWilsonSecondVariation tangent plane site =
  wilsonPlaquetteSecondVariation
    (plaquetteJet
      (firstLink links) (secondLink links) (thirdLink links) (fourthLink links))
  where
  links = globalPlaquetteFourLinks tangent plane site

globalPlaquetteWilsonSecondVariationExact :
  ∀ {n} tangent plane site →
  globalPlaquetteWilsonSecondVariation tangent plane site
  ≡ normSqV (globalForwardDifferenceCurl tangent plane site)
globalPlaquetteWilsonSecondVariationExact tangent plane site =
  trans
    (singlePlaquetteWilsonSecondVariationEqualsCurlNormSq
      (firstLink links) (secondLink links) (thirdLink links) (fourthLink links))
    (cong normSqV
      (lie3Ext
        (ℚRing.solve-∀
          (x (firstLink links)) (x (secondLink links))
          (x (thirdLink links)) (x (fourthLink links)))
        (ℚRing.solve-∀
          (y (firstLink links)) (y (secondLink links))
          (y (thirdLink links)) (y (fourthLink links)))
        (ℚRing.solve-∀
          (z (firstLink links)) (z (secondLink links))
          (z (thirdLink links)) (z (fourthLink links)))))
  where
  links = globalPlaquetteFourLinks tangent plane site

translatedOpenPlaquetteWilsonHessianExact :
  ∀ {n} origin tangent plane first second transverse0 transverse1 →
  literalPlaquetteWilsonSecondVariation
    (restrictGlobalTangentToTranslatedOpenBlock origin tangent)
    plane (openPlaquetteBaseSite plane first second transverse0 transverse1)
  ≡ globalPlaquetteWilsonSecondVariation tangent plane
      (translateLocalSiteToGlobal origin
        (openPlaquetteBaseSite plane first second transverse0 transverse1))
translatedOpenPlaquetteWilsonHessianExact
  origin tangent plane first second t0 t1 =
  trans
    (literalPlaquetteWilsonSecondVariationExact
      (restrictGlobalTangentToTranslatedOpenBlock origin tangent)
      plane base)
    (trans
      (cong normSqV
        (translatedOpenPlaquetteCurlExact
          origin tangent plane first second t0 t1))
      (sym (globalPlaquetteWilsonSecondVariationExact tangent plane
        (translateLocalSiteToGlobal origin base))))
  where
  base = openPlaquetteBaseSite plane first second t0 t1

------------------------------------------------------------------------
-- Exact finite folds over six planes and all open plaquette bases.
------------------------------------------------------------------------

openPlaquetteFold :
  (PositivePlaquettePlane4 → PhysicalBlockL side4 → ℚ) → ℚ
openPlaquetteFold term =
  sumRational positivePlaquettePlanes4 (λ plane →
    sumRational (allCyclicIndices three) (λ first →
      sumRational (allCyclicIndices three) (λ second →
        sumRational (allCyclicIndices side4) (λ transverse0 →
          sumRational (allCyclicIndices side4) (λ transverse1 →
            term plane
              (openPlaquetteBaseSite plane first second
                transverse0 transverse1))))))

openPlaquetteFoldCong : ∀ left right →
  (∀ plane first second transverse0 transverse1 →
    left plane (openPlaquetteBaseSite plane first second transverse0 transverse1)
    ≡ right plane (openPlaquetteBaseSite plane first second transverse0 transverse1)) →
  openPlaquetteFold left ≡ openPlaquetteFold right
openPlaquetteFoldCong left right pointwise =
  sumRationalCong positivePlaquettePlanes4 _ _ (λ plane →
    sumRationalCong (allCyclicIndices three) _ _ (λ first →
      sumRationalCong (allCyclicIndices three) _ _ (λ second →
        sumRationalCong (allCyclicIndices side4) _ _ (λ transverse0 →
          sumRationalCong (allCyclicIndices side4) _ _ (λ transverse1 →
            pointwise plane first second transverse0 transverse1)))))

localTranslatedOpenWilsonHessian :
  ∀ {n} → GlobalSite4 n → GlobalSU2Tangent4 n → ℚ
localTranslatedOpenWilsonHessian origin tangent =
  openPlaquetteFold
    (literalPlaquetteWilsonSecondVariation
      (restrictGlobalTangentToTranslatedOpenBlock origin tangent))

globalRestrictedOpenWilsonHessian :
  ∀ {n} → GlobalSite4 n → GlobalSU2Tangent4 n → ℚ
globalRestrictedOpenWilsonHessian origin tangent =
  openPlaquetteFold (λ plane localSite →
    globalPlaquetteWilsonSecondVariation tangent plane
      (translateLocalSiteToGlobal origin localSite))

globalWilsonToLocalTranslatedOpenBlock :
  ∀ {n} (origin : GlobalSite4 n) tangent →
  localTranslatedOpenWilsonHessian origin tangent
  ≡ globalRestrictedOpenWilsonHessian origin tangent
globalWilsonToLocalTranslatedOpenBlock origin tangent =
  openPlaquetteFoldCong _ _
    (translatedOpenPlaquetteWilsonHessianExact origin tangent)

arbitraryTranslatedOpenBlockCarrierLevel : ProofLevel
arbitraryTranslatedOpenBlockCarrierLevel = machineChecked

translatedOpenPlaquetteExtractionLevel : ProofLevel
translatedOpenPlaquetteExtractionLevel = machineChecked

arbitraryGlobalWilsonToLocalTranslatedBlockLevel : ProofLevel
arbitraryGlobalWilsonToLocalTranslatedBlockLevel = machineChecked
