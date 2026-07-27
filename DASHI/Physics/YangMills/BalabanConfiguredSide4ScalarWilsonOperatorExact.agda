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
  (SiteField; sumRational)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using (ScalarBondField4; scalarBondInner; siteSum4Cong; siteSum4Add;
    siteSum4Scale; axis0; axis1; axis2; axis3)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicHodgeExact
  using (curlPlaneEnergy)

scalarPlaneCurl : PositivePlaquettePlane4 → ScalarBondField4 → SiteField side4
scalarPlaneCurl plane field site =
  forwardDifference4 (positivePlaneFirst plane)
    (field (positivePlaneSecond plane)) site
  - forwardDifference4 (positivePlaneSecond plane)
    (field (positivePlaneFirst plane)) site

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
scalarWilsonOperator field axis site =
  sumRational positivePlaquettePlanes4
    (λ plane → planeWilsonContribution plane field axis site)

siteSum4Zero : siteSum4 (λ _ → 0ℚ) ≡ 0ℚ
siteSum4Zero = go (physicalBlockSites side4)
  where
  go : ∀ (values : List (PhysicalBlockL side4)) →
    sumRational values (λ _ → 0ℚ) ≡ 0ℚ
  go [] = refl
  go (value ∷ values) rewrite go values = ℚRing.solve-∀

siteSumProductZero : ∀ field →
  siteSum4 (λ site → field site * 0ℚ) ≡ 0ℚ
siteSumProductZero field =
  trans
    (siteSum4Cong _ _ (λ site → ℚRing.solve-∀ (field site)))
    siteSum4Zero

firstBackwardPairing : ∀ secondAxis field curvature →
  siteSum4 (λ site → field site * backwardDifference4 secondAxis curvature site)
  ≡ - siteSum4 (λ site →
      forwardDifference4 secondAxis field site * curvature site)
firstBackwardPairing secondAxis field curvature =
  trans
    (ℚRing.solve-∀
      (siteSum4 (λ site →
        field site * backwardDifference4 secondAxis curvature site)))
    (sym
      (cong (λ value → - value)
        (periodicForwardBackwardSummationByParts
          secondAxis field curvature)))

secondNegativeBackwardPairing : ∀ firstAxis field curvature →
  siteSum4 (λ site → field site *
    (- backwardDifference4 firstAxis curvature site))
  ≡ siteSum4 (λ site →
      forwardDifference4 firstAxis field site * curvature site)
secondNegativeBackwardPairing firstAxis field curvature =
  trans
    (siteSum4Cong _ _ (λ site → ℚRing.solve-∀
      (field site) (backwardDifference4 firstAxis curvature site)))
    (trans
      (siteSum4Scale (- 1ℚ)
        (λ site → field site * backwardDifference4 firstAxis curvature site))
      (trans
        (ℚRing.solve-∀
          (siteSum4 (λ site →
            field site * backwardDifference4 firstAxis curvature site)))
        (sym
          (periodicForwardBackwardSummationByParts
            firstAxis field curvature))))

planeTwoAxisPairingExact : ∀ plane field →
  siteSum4 (λ site → field (positivePlaneFirst plane) site
    * backwardDifference4 (positivePlaneSecond plane)
      (scalarPlaneCurl plane field) site)
  + siteSum4 (λ site → field (positivePlaneSecond plane) site
    * (- backwardDifference4 (positivePlaneFirst plane)
      (scalarPlaneCurl plane field) site))
  ≡ curlPlaneEnergy plane field
planeTwoAxisPairingExact plane field =
  trans
    (cong₂ _+_
      (firstBackwardPairing (positivePlaneSecond plane)
        (field (positivePlaneFirst plane)) (scalarPlaneCurl plane field))
      (secondNegativeBackwardPairing (positivePlaneFirst plane)
        (field (positivePlaneSecond plane)) (scalarPlaneCurl plane field)))
    (trans
      (sym (siteSum4Add
        (λ site → - (forwardDifference4 (positivePlaneSecond plane)
          (field (positivePlaneFirst plane)) site * scalarPlaneCurl plane field site))
        (λ site → forwardDifference4 (positivePlaneFirst plane)
          (field (positivePlaneSecond plane)) site * scalarPlaneCurl plane field site)))
      (siteSum4Cong _ _ (λ site → ℚRing.solve-∀
        (forwardDifference4 (positivePlaneFirst plane)
          (field (positivePlaneSecond plane)) site)
        (forwardDifference4 (positivePlaneSecond plane)
          (field (positivePlaneFirst plane)) site))))

scalarPlanePairingExact : ∀ plane field →
  scalarBondInner field (planeWilsonContribution plane field)
  ≡ curlPlaneEnergy plane field
scalarPlanePairingExact plane01 field
  rewrite siteSumProductZero (field axis2)
        | siteSumProductZero (field axis3) =
  trans (ℚRing.solve-∀
    (siteSum4 (λ site → field axis0 site *
      backwardDifference4 axis1 (scalarPlaneCurl plane01 field) site))
    (siteSum4 (λ site → field axis1 site *
      (- backwardDifference4 axis0 (scalarPlaneCurl plane01 field) site))))
    (planeTwoAxisPairingExact plane01 field)
scalarPlanePairingExact plane02 field
  rewrite siteSumProductZero (field axis1)
        | siteSumProductZero (field axis3) =
  trans (ℚRing.solve-∀
    (siteSum4 (λ site → field axis0 site *
      backwardDifference4 axis2 (scalarPlaneCurl plane02 field) site))
    (siteSum4 (λ site → field axis2 site *
      (- backwardDifference4 axis0 (scalarPlaneCurl plane02 field) site))))
    (planeTwoAxisPairingExact plane02 field)
scalarPlanePairingExact plane03 field
  rewrite siteSumProductZero (field axis1)
        | siteSumProductZero (field axis2) =
  trans (ℚRing.solve-∀
    (siteSum4 (λ site → field axis0 site *
      backwardDifference4 axis3 (scalarPlaneCurl plane03 field) site))
    (siteSum4 (λ site → field axis3 site *
      (- backwardDifference4 axis0 (scalarPlaneCurl plane03 field) site))))
    (planeTwoAxisPairingExact plane03 field)
scalarPlanePairingExact plane12 field
  rewrite siteSumProductZero (field axis0)
        | siteSumProductZero (field axis3) =
  trans (ℚRing.solve-∀
    (siteSum4 (λ site → field axis1 site *
      backwardDifference4 axis2 (scalarPlaneCurl plane12 field) site))
    (siteSum4 (λ site → field axis2 site *
      (- backwardDifference4 axis1 (scalarPlaneCurl plane12 field) site))))
    (planeTwoAxisPairingExact plane12 field)
scalarPlanePairingExact plane13 field
  rewrite siteSumProductZero (field axis0)
        | siteSumProductZero (field axis2) =
  trans (ℚRing.solve-∀
    (siteSum4 (λ site → field axis1 site *
      backwardDifference4 axis3 (scalarPlaneCurl plane13 field) site))
    (siteSum4 (λ site → field axis3 site *
      (- backwardDifference4 axis1 (scalarPlaneCurl plane13 field) site))))
    (planeTwoAxisPairingExact plane13 field)
scalarPlanePairingExact plane23 field
  rewrite siteSumProductZero (field axis0)
        | siteSumProductZero (field axis1) =
  trans (ℚRing.solve-∀
    (siteSum4 (λ site → field axis2 site *
      backwardDifference4 axis3 (scalarPlaneCurl plane23 field) site))
    (siteSum4 (λ site → field axis3 site *
      (- backwardDifference4 axis2 (scalarPlaneCurl plane23 field) site))))
    (planeTwoAxisPairingExact plane23 field)

scalarWilsonPlaneRieszLevel : ProofLevel
scalarWilsonPlaneRieszLevel = machineChecked
