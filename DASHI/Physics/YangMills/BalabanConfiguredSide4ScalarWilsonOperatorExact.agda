module DASHI.Physics.YangMills.BalabanConfiguredSide4ScalarWilsonOperatorExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL; physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (SiteField; sumRational; sumRationalNegate)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using (ScalarBondField4; scalarBondInner; siteSum4Cong; siteSum4Add;
    siteSum4Scale; axis0; axis1; axis2; axis3)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicHodgeExact
  using (curlPlaneEnergy)

scalarPlaneCurl : PositivePlaquettePlane4 → ScalarBondField4 → SiteField side4
scalarPlaneCurl plane fld site =
  forwardDifference4 (positivePlaneFirst plane)
    (fld (positivePlaneSecond plane)) site
  - forwardDifference4 (positivePlaneSecond plane)
    (fld (positivePlaneFirst plane)) site

planeWilsonContribution :
  PositivePlaquettePlane4 → ScalarBondField4 → ScalarBondField4
planeWilsonContribution plane01 f zeroᵢ s =
  backwardDifference4 axis1 (scalarPlaneCurl plane01 f) s
planeWilsonContribution plane01 f (sucᵢ zeroᵢ) s =
  - backwardDifference4 axis0 (scalarPlaneCurl plane01 f) s
planeWilsonContribution plane01 f (sucᵢ (sucᵢ zeroᵢ)) s = 0ℚ
planeWilsonContribution plane01 f (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) s = 0ℚ
planeWilsonContribution plane02 f zeroᵢ s =
  backwardDifference4 axis2 (scalarPlaneCurl plane02 f) s
planeWilsonContribution plane02 f (sucᵢ zeroᵢ) s = 0ℚ
planeWilsonContribution plane02 f (sucᵢ (sucᵢ zeroᵢ)) s =
  - backwardDifference4 axis0 (scalarPlaneCurl plane02 f) s
planeWilsonContribution plane02 f (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) s = 0ℚ
planeWilsonContribution plane03 f zeroᵢ s =
  backwardDifference4 axis3 (scalarPlaneCurl plane03 f) s
planeWilsonContribution plane03 f (sucᵢ zeroᵢ) s = 0ℚ
planeWilsonContribution plane03 f (sucᵢ (sucᵢ zeroᵢ)) s = 0ℚ
planeWilsonContribution plane03 f (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) s =
  - backwardDifference4 axis0 (scalarPlaneCurl plane03 f) s
planeWilsonContribution plane12 f zeroᵢ s = 0ℚ
planeWilsonContribution plane12 f (sucᵢ zeroᵢ) s =
  backwardDifference4 axis2 (scalarPlaneCurl plane12 f) s
planeWilsonContribution plane12 f (sucᵢ (sucᵢ zeroᵢ)) s =
  - backwardDifference4 axis1 (scalarPlaneCurl plane12 f) s
planeWilsonContribution plane12 f (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) s = 0ℚ
planeWilsonContribution plane13 f zeroᵢ s = 0ℚ
planeWilsonContribution plane13 f (sucᵢ zeroᵢ) s =
  backwardDifference4 axis3 (scalarPlaneCurl plane13 f) s
planeWilsonContribution plane13 f (sucᵢ (sucᵢ zeroᵢ)) s = 0ℚ
planeWilsonContribution plane13 f (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) s =
  - backwardDifference4 axis1 (scalarPlaneCurl plane13 f) s
planeWilsonContribution plane23 f zeroᵢ s = 0ℚ
planeWilsonContribution plane23 f (sucᵢ zeroᵢ) s = 0ℚ
planeWilsonContribution plane23 f (sucᵢ (sucᵢ zeroᵢ)) s =
  backwardDifference4 axis3 (scalarPlaneCurl plane23 f) s
planeWilsonContribution plane23 f (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) s =
  - backwardDifference4 axis2 (scalarPlaneCurl plane23 f) s

scalarWilsonOperator : ScalarBondField4 → ScalarBondField4
scalarWilsonOperator fld axis site =
  sumRational positivePlaquettePlanes4
    (λ plane → planeWilsonContribution plane fld axis site)

siteSum4Zero : siteSum4 (λ _ → 0ℚ) ≡ 0ℚ
siteSum4Zero = go (physicalBlockSites side4)
  where
  go : ∀ (values : List (PhysicalBlockL side4)) →
    sumRational values (λ _ → 0ℚ) ≡ 0ℚ
  go [] = refl
  go (value ∷ values) = cong (0ℚ +_) (go values)

mulZeroRightRaw : ∀ x → x * 0ℚ ≡ 0ℚ
mulZeroRightRaw = ℚRing.solve-∀

doubleNegCancelRaw : ∀ x → x ≡ - (- x)
doubleNegCancelRaw = ℚRing.solve-∀

mulNegRightRaw : ∀ a b → a * (- b) ≡ - (a * b)
mulNegRightRaw = ℚRing.solve-∀

curlPairingPointwiseRaw : ∀ a b → - (b * (a - b)) + a * (a - b) ≡ (a - b) * (a - b)
curlPairingPointwiseRaw = ℚRing.solve-∀

siteSumProductZero : (fld : PhysicalBlockL side4 → ℚ) →
  siteSum4 (λ site → fld site * 0ℚ) ≡ 0ℚ
siteSumProductZero fld =
  trans
    (siteSum4Cong
      (λ site → fld site * 0ℚ)
      (λ _ → 0ℚ)
      (λ site → mulZeroRightRaw (fld site)))
    siteSum4Zero

firstBackwardPairing : ∀ secondAxis fld curvature →
  siteSum4 (λ site → fld site * backwardDifference4 secondAxis curvature site)
  ≡ - siteSum4 (λ site →
      forwardDifference4 secondAxis fld site * curvature site)
firstBackwardPairing secondAxis fld curvature =
  trans
    (doubleNegCancelRaw
      (siteSum4 (λ site → fld site * backwardDifference4 secondAxis curvature site)))
    (sym
      (cong (-_)
        (periodicForwardBackwardSummationByParts
          secondAxis fld curvature)))

secondNegativeBackwardPairing : ∀ firstAxis fld curvature →
  siteSum4 (λ site → fld site *
    (- backwardDifference4 firstAxis curvature site))
  ≡ siteSum4 (λ site →
      forwardDifference4 firstAxis fld site * curvature site)
secondNegativeBackwardPairing firstAxis fld curvature =
  trans
    (siteSum4Cong
      (λ site → fld site * (- backwardDifference4 firstAxis curvature site))
      (λ site → - (fld site * backwardDifference4 firstAxis curvature site))
      (λ site → mulNegRightRaw (fld site) (backwardDifference4 firstAxis curvature site)))
    (trans
      (sumRationalNegate (physicalBlockSites side4)
        (λ site → fld site * backwardDifference4 firstAxis curvature site))
      (sym
        (periodicForwardBackwardSummationByParts
          firstAxis fld curvature)))

planeTwoAxisPairingExact : ∀ plane fld →
  siteSum4 (λ site → fld (positivePlaneFirst plane) site
    * backwardDifference4 (positivePlaneSecond plane)
      (scalarPlaneCurl plane fld) site)
  + siteSum4 (λ site → fld (positivePlaneSecond plane) site
    * (- backwardDifference4 (positivePlaneFirst plane)
      (scalarPlaneCurl plane fld) site))
  ≡ curlPlaneEnergy plane fld
planeTwoAxisPairingExact plane fld =
  let dFirst = forwardDifference4 (positivePlaneFirst plane) (fld (positivePlaneSecond plane))
      dSecond = forwardDifference4 (positivePlaneSecond plane) (fld (positivePlaneFirst plane))
      curl = scalarPlaneCurl plane fld
  in
  trans
    (cong₂ _+_
      (firstBackwardPairing (positivePlaneSecond plane)
        (fld (positivePlaneFirst plane)) curl)
      (secondNegativeBackwardPairing (positivePlaneFirst plane)
        (fld (positivePlaneSecond plane)) curl))
    (trans
      (cong (_+ siteSum4 (λ site → dFirst site * curl site))
        (sym (sumRationalNegate (physicalBlockSites side4)
          (λ site → dSecond site * curl site))))
      (trans
        (sym (siteSum4Add
          (λ site → - (dSecond site * curl site))
          (λ site → dFirst site * curl site)))
        (siteSum4Cong
          (λ site → - (dSecond site * curl site) + dFirst site * curl site)
          (λ site → (dFirst site - dSecond site) * (dFirst site - dSecond site))
          (λ site → curlPairingPointwiseRaw (dFirst site) (dSecond site)))))

drop23Raw : ∀ a b → a + (b + (0ℚ + (0ℚ + 0ℚ))) ≡ a + b
drop23Raw = ℚRing.solve-∀

drop13Raw : ∀ a b → a + (0ℚ + (b + (0ℚ + 0ℚ))) ≡ a + b
drop13Raw = ℚRing.solve-∀

drop12Raw : ∀ a b → a + (0ℚ + (0ℚ + (b + 0ℚ))) ≡ a + b
drop12Raw = ℚRing.solve-∀

drop03Raw : ∀ a b → 0ℚ + (a + (b + (0ℚ + 0ℚ))) ≡ a + b
drop03Raw = ℚRing.solve-∀

drop02Raw : ∀ a b → 0ℚ + (a + (0ℚ + (b + 0ℚ))) ≡ a + b
drop02Raw = ℚRing.solve-∀

drop01Raw : ∀ a b → 0ℚ + (0ℚ + (a + (b + 0ℚ))) ≡ a + b
drop01Raw = ℚRing.solve-∀

scalarPlanePairingExact : ∀ plane fld →
  scalarBondInner fld (planeWilsonContribution plane fld)
  ≡ curlPlaneEnergy plane fld
scalarPlanePairingExact plane01 fld =
  let a = siteSum4 (λ site → fld axis0 site * planeWilsonContribution plane01 fld axis0 site)
      b = siteSum4 (λ site → fld axis1 site * planeWilsonContribution plane01 fld axis1 site)
  in
  trans
    (cong (a +_) (cong (b +_) (cong₂ _+_ (siteSumProductZero (fld axis2))
      (cong (_+ 0ℚ) (siteSumProductZero (fld axis3))))))
    (trans (drop23Raw a b) (planeTwoAxisPairingExact plane01 fld))
scalarPlanePairingExact plane02 fld =
  let a = siteSum4 (λ site → fld axis0 site * planeWilsonContribution plane02 fld axis0 site)
      b = siteSum4 (λ site → fld axis2 site * planeWilsonContribution plane02 fld axis2 site)
  in
  trans
    (cong (a +_) (cong₂ _+_ (siteSumProductZero (fld axis1))
      (cong (b +_) (cong (_+ 0ℚ) (siteSumProductZero (fld axis3))))))
    (trans (drop13Raw a b) (planeTwoAxisPairingExact plane02 fld))
scalarPlanePairingExact plane03 fld =
  let a = siteSum4 (λ site → fld axis0 site * planeWilsonContribution plane03 fld axis0 site)
      b = siteSum4 (λ site → fld axis3 site * planeWilsonContribution plane03 fld axis3 site)
  in
  trans
    (cong (a +_) (cong₂ _+_ (siteSumProductZero (fld axis1))
      (cong (_+ (b + 0ℚ)) (siteSumProductZero (fld axis2)))))
    (trans (drop12Raw a b) (planeTwoAxisPairingExact plane03 fld))
scalarPlanePairingExact plane12 fld =
  let a = siteSum4 (λ site → fld axis1 site * planeWilsonContribution plane12 fld axis1 site)
      b = siteSum4 (λ site → fld axis2 site * planeWilsonContribution plane12 fld axis2 site)
  in
  trans
    (cong₂ _+_ (siteSumProductZero (fld axis0))
      (cong (a +_) (cong (b +_) (cong (_+ 0ℚ) (siteSumProductZero (fld axis3))))))
    (trans (drop03Raw a b) (planeTwoAxisPairingExact plane12 fld))
scalarPlanePairingExact plane13 fld =
  let a = siteSum4 (λ site → fld axis1 site * planeWilsonContribution plane13 fld axis1 site)
      b = siteSum4 (λ site → fld axis3 site * planeWilsonContribution plane13 fld axis3 site)
  in
  trans
    (cong₂ _+_ (siteSumProductZero (fld axis0))
      (cong (a +_) (cong (_+ (b + 0ℚ)) (siteSumProductZero (fld axis2)))))
    (trans (drop02Raw a b) (planeTwoAxisPairingExact plane13 fld))
scalarPlanePairingExact plane23 fld =
  let a = siteSum4 (λ site → fld axis2 site * planeWilsonContribution plane23 fld axis2 site)
      b = siteSum4 (λ site → fld axis3 site * planeWilsonContribution plane23 fld axis3 site)
  in
  trans
    (cong₂ _+_ (siteSumProductZero (fld axis0))
      (cong (_+ (a + (b + 0ℚ))) (siteSumProductZero (fld axis1))))
    (trans (drop01Raw a b) (planeTwoAxisPairingExact plane23 fld))

scalarWilsonPlaneRieszLevel : ProofLevel
scalarWilsonPlaneRieszLevel = machineChecked
