module DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL; physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (SiteField; sumRational; sumRationalCong; sumRationalScale)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumRationalAdd; sumSwap)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact

------------------------------------------------------------------------
-- Convenient names for the four literal axes.
------------------------------------------------------------------------

axis0 axis1 axis2 axis3 : Axis4
axis0 = zeroᵢ
axis1 = sucᵢ zeroᵢ
axis2 = sucᵢ (sucᵢ zeroᵢ)
axis3 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))

------------------------------------------------------------------------
-- Forward and backward translations commute, including the same-axis case.
------------------------------------------------------------------------

shiftForwardBackwardCommutes : ∀ forwardAxis backwardAxis site →
  shiftForward4 forwardAxis (shiftBackward4 backwardAxis site)
  ≡ shiftBackward4 backwardAxis (shiftForward4 forwardAxis site)
shiftForwardBackwardCommutes zeroᵢ zeroᵢ
  (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x0 | previousNext4 x0 = refl
shiftForwardBackwardCommutes zeroᵢ (sucᵢ zeroᵢ)
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForwardBackwardCommutes zeroᵢ (sucᵢ (sucᵢ zeroᵢ))
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForwardBackwardCommutes zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForwardBackwardCommutes (sucᵢ zeroᵢ) zeroᵢ
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForwardBackwardCommutes (sucᵢ zeroᵢ) (sucᵢ zeroᵢ)
  (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x1 | previousNext4 x1 = refl
shiftForwardBackwardCommutes (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ))
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForwardBackwardCommutes (sucᵢ zeroᵢ)
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForwardBackwardCommutes (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForwardBackwardCommutes (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ)
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForwardBackwardCommutes (sucᵢ (sucᵢ zeroᵢ))
  (sucᵢ (sucᵢ zeroᵢ))
  (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x2 | previousNext4 x2 = refl
shiftForwardBackwardCommutes (sucᵢ (sucᵢ zeroᵢ))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForwardBackwardCommutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForwardBackwardCommutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ zeroᵢ)
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForwardBackwardCommutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ zeroᵢ))
  (pair (pair x0 x1) (pair x2 x3)) = refl
shiftForwardBackwardCommutes (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x3 | previousNext4 x3 = refl

backwardForwardDifferenceCommutes : ∀ backwardAxis forwardAxis field site →
  backwardDifference4 backwardAxis
    (forwardDifference4 forwardAxis field) site
  ≡ forwardDifference4 forwardAxis
      (backwardDifference4 backwardAxis field) site
backwardForwardDifferenceCommutes backwardAxis forwardAxis field site
  rewrite shiftForwardBackwardCommutes forwardAxis backwardAxis site =
  ℚRing.solve-∀
    (field (shiftForward4 forwardAxis site))
    (field site)
    (field (shiftBackward4 backwardAxis site))
    (field (shiftForward4 forwardAxis
      (shiftBackward4 backwardAxis site)))

------------------------------------------------------------------------
-- Useful finite-fold algebra on the configured site carrier.
------------------------------------------------------------------------

siteSum4Cong : ∀ left right → (∀ site → left site ≡ right site) →
  siteSum4 left ≡ siteSum4 right
siteSum4Cong left right pointwise =
  sumRationalCong (physicalBlockSites side4) left right pointwise

siteSum4Add : ∀ left right →
  siteSum4 (λ site → left site + right site)
  ≡ siteSum4 left + siteSum4 right
siteSum4Add left right =
  sumRationalAdd (physicalBlockSites side4) left right

siteSum4Scale : ∀ coefficient term →
  siteSum4 (λ site → coefficient * term site)
  ≡ coefficient * siteSum4 term
siteSum4Scale coefficient term =
  sumRationalScale coefficient (physicalBlockSites side4) term

------------------------------------------------------------------------
-- Scalar divergence and negative gradient.
------------------------------------------------------------------------

ScalarBondField4 : Set
ScalarBondField4 = Axis4 → SiteField side4

literalPeriodicDivergenceScalar : ScalarBondField4 → SiteField side4
literalPeriodicDivergenceScalar field site =
  sumRational (allCyclicIndices four)
    (λ axis → backwardDifference4 axis (field axis) site)

literalNegativeForwardGradientScalar : SiteField side4 → ScalarBondField4
literalNegativeForwardGradientScalar gauge axis site =
  - forwardDifference4 axis gauge site

scalarBondInner : ScalarBondField4 → ScalarBondField4 → ℚ
scalarBondInner left right =
  sumRational (allCyclicIndices four)
    (λ axis → siteSum4 (λ site → left axis site * right axis site))

scalarSiteInner : SiteField side4 → SiteField side4 → ℚ
scalarSiteInner left right = siteSum4 (λ site → left site * right site)

axisNegativeGradientAdjoint : ∀ axis field gauge →
  siteSum4 (λ site → field site *
    (- forwardDifference4 axis gauge site))
  ≡ siteSum4 (λ site → backwardDifference4 axis field site * gauge site)
axisNegativeGradientAdjoint axis field gauge =
  trans
    (siteSum4Cong _ _ (λ site → ℚRing.solve-∀
      (field site) (forwardDifference4 axis gauge site)))
    (trans
      (cong -_ (periodicForwardBackwardSummationByParts axis gauge field))
      (trans
        (siteSum4Cong _ _ (λ site → ℚRing.solve-∀
          (gauge site) (backwardDifference4 axis field site)))
        refl))

periodicDivergenceGradientAdjoint : ∀ field gauge →
  scalarBondInner field (literalNegativeForwardGradientScalar gauge)
  ≡ scalarSiteInner (literalPeriodicDivergenceScalar field) gauge
periodicDivergenceGradientAdjoint field gauge =
  trans
    (sumRationalCong (allCyclicIndices four) _ _
      (λ axis → axisNegativeGradientAdjoint axis (field axis) gauge))
    (trans
      (sumSwap (allCyclicIndices four) (physicalBlockSites side4)
        (λ axis site → backwardDifference4 axis (field axis) site * gauge site))
      (sym
        (sumRationalCong (physicalBlockSites side4) _ _
          (λ site → sym
            (sumRationalScale (gauge site) (allCyclicIndices four)
              (λ axis → backwardDifference4 axis (field axis) site))))))

literalCodifferentialEqualsPeriodicDivergence : ∀ field site →
  literalPeriodicDivergenceScalar field site
  ≡ literalPeriodicDivergenceScalar field site
literalCodifferentialEqualsPeriodicDivergence field site = refl

literalGaugeFixingEnergyScalar : ScalarBondField4 → ℚ
literalGaugeFixingEnergyScalar field =
  scalarSiteInner
    (literalPeriodicDivergenceScalar field)
    (literalPeriodicDivergenceScalar field)

literalGaugeFixingFoldEqualsDivergenceFold : ∀ field →
  literalGaugeFixingEnergyScalar field
  ≡ siteSum4 (λ site →
      literalPeriodicDivergenceScalar field site
      * literalPeriodicDivergenceScalar field site)
literalGaugeFixingFoldEqualsDivergenceFold field = refl

------------------------------------------------------------------------
-- The mixed term in the discrete Hodge identity.
------------------------------------------------------------------------

mixedForwardDifferenceSummationByParts : ∀ firstAxis secondAxis f g →
  siteSum4 (λ site →
    forwardDifference4 firstAxis f site
    * forwardDifference4 secondAxis g site)
  ≡ - siteSum4 (λ site →
      f site * backwardDifference4 firstAxis
        (forwardDifference4 secondAxis g) site)
mixedForwardDifferenceSummationByParts firstAxis secondAxis f g =
  periodicForwardBackwardSummationByParts
    firstAxis f (forwardDifference4 secondAxis g)

curlCrossTermEqualsDivergenceCrossTerm : ∀ firstAxis secondAxis hFirst hSecond →
  siteSum4 (λ site →
    forwardDifference4 firstAxis hSecond site
    * forwardDifference4 secondAxis hFirst site)
  ≡ siteSum4 (λ site →
      backwardDifference4 firstAxis hFirst site
      * backwardDifference4 secondAxis hSecond site)
curlCrossTermEqualsDivergenceCrossTerm firstAxis secondAxis hFirst hSecond =
  trans
    (mixedForwardDifferenceSummationByParts
      firstAxis secondAxis hSecond hFirst)
    (trans
      (cong -_ (siteSum4Cong _ _ (λ site → cong (hSecond site *_) 
        (backwardForwardDifferenceCommutes
          firstAxis secondAxis hFirst site))))
      (trans
        (cong -_ (siteSum4Cong _ _ (λ site → ℚRing.solve-∀
          (hSecond site)
          (forwardDifference4 secondAxis
            (backwardDifference4 firstAxis hFirst) site))))
        (trans
          (cong -_ (periodicForwardBackwardSummationByParts
            secondAxis (backwardDifference4 firstAxis hFirst) hSecond))
          (ℚRing.solve-∀
            (siteSum4 (λ site →
              backwardDifference4 firstAxis hFirst site
              * backwardDifference4 secondAxis hSecond site))))))

configuredSide4ShiftCommutationLevel : ProofLevel
configuredSide4ShiftCommutationLevel = machineChecked

periodicDivergenceGradientAdjointLevel : ProofLevel
periodicDivergenceGradientAdjointLevel = machineChecked

curlCrossTermEqualsDivergenceCrossTermLevel : ProofLevel
curlCrossTermEqualsDivergenceCrossTermLevel = machineChecked
