module DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL; physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (SiteField; sumRational; sumRationalCong; sumRationalScale; sumRationalNegate)
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

diffCommuteRaw : ∀ a b c d → (a - b) - (c - d) ≡ (a - c) - (b - d)
diffCommuteRaw = ℚRing.solve-∀

mulNegCommRaw : ∀ a b → a * (- b) ≡ - (b * a)
mulNegCommRaw = ℚRing.solve-∀

mulCommRaw : ∀ a b → a * b ≡ b * a
mulCommRaw = ℚRing.solve-∀

doubleNegRaw : ∀ x → - (- x) ≡ x
doubleNegRaw = ℚRing.solve-∀

backwardForwardDifferenceCommutes : ∀ backwardAxis forwardAxis fld site →
  backwardDifference4 backwardAxis
    (forwardDifference4 forwardAxis fld) site
  ≡ forwardDifference4 forwardAxis
      (backwardDifference4 backwardAxis fld) site
backwardForwardDifferenceCommutes backwardAxis forwardAxis fld site =
  trans
    (cong
      (λ shiftedSite →
        (fld (shiftForward4 forwardAxis site) - fld site)
        - (fld shiftedSite - fld (shiftBackward4 backwardAxis site)))
      (shiftForwardBackwardCommutes forwardAxis backwardAxis site))
    (diffCommuteRaw
      (fld (shiftForward4 forwardAxis site))
      (fld site)
      (fld (shiftBackward4 backwardAxis (shiftForward4 forwardAxis site)))
      (fld (shiftBackward4 backwardAxis site)))

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
literalPeriodicDivergenceScalar fld site =
  sumRational (allCyclicIndices four)
    (λ axis → backwardDifference4 axis (fld axis) site)

literalNegativeForwardGradientScalar : SiteField side4 → ScalarBondField4
literalNegativeForwardGradientScalar gauge axis site =
  - forwardDifference4 axis gauge site

scalarBondInner : ScalarBondField4 → ScalarBondField4 → ℚ
scalarBondInner left right =
  sumRational (allCyclicIndices four)
    (λ axis → siteSum4 (λ site → left axis site * right axis site))

scalarSiteInner : SiteField side4 → SiteField side4 → ℚ
scalarSiteInner left right = siteSum4 (λ site → left site * right site)

axisNegativeGradientAdjoint : ∀ axis fld gauge →
  siteSum4 (λ site → fld site *
    (- forwardDifference4 axis gauge site))
  ≡ siteSum4 (λ site → backwardDifference4 axis fld site * gauge site)
axisNegativeGradientAdjoint axis fld gauge =
  trans
    (siteSum4Cong
      (λ site → fld site * (- forwardDifference4 axis gauge site))
      (λ site → - (forwardDifference4 axis gauge site * fld site))
      (λ site → mulNegCommRaw (fld site) (forwardDifference4 axis gauge site)))
    (trans
      (sumRationalNegate (physicalBlockSites side4)
        (λ site → forwardDifference4 axis gauge site * fld site))
      (trans
        (cong (-_)
          (periodicForwardBackwardSummationByParts axis gauge fld))
        (trans
          (doubleNegRaw
            (siteSum4 (λ site → gauge site * backwardDifference4 axis fld site)))
          (siteSum4Cong
            (λ site → gauge site * backwardDifference4 axis fld site)
            (λ site → backwardDifference4 axis fld site * gauge site)
            (λ site → mulCommRaw (gauge site) (backwardDifference4 axis fld site))))))

axisFoldTimesRight :
  (fld : ScalarBondField4) (gauge : SiteField side4)
  (site : PhysicalBlockL side4) →
  sumRational (allCyclicIndices four)
    (λ axis → backwardDifference4 axis (fld axis) site * gauge site)
  ≡ literalPeriodicDivergenceScalar fld site * gauge site
axisFoldTimesRight fld gauge site =
  trans
    (sumRationalCong (allCyclicIndices four)
      (λ axis → backwardDifference4 axis (fld axis) site * gauge site)
      (λ axis → gauge site * backwardDifference4 axis (fld axis) site)
      (λ axis → mulCommRaw (backwardDifference4 axis (fld axis) site) (gauge site)))
    (trans
      (sumRationalScale (gauge site) (allCyclicIndices four)
        (λ axis → backwardDifference4 axis (fld axis) site))
      (mulCommRaw (gauge site) (literalPeriodicDivergenceScalar fld site)))

periodicDivergenceGradientAdjoint : ∀ fld gauge →
  scalarBondInner fld (literalNegativeForwardGradientScalar gauge)
  ≡ scalarSiteInner (literalPeriodicDivergenceScalar fld) gauge
periodicDivergenceGradientAdjoint fld gauge =
  trans
    (sumRationalCong (allCyclicIndices four)
      (λ axis → siteSum4 (λ site → fld axis site * (- forwardDifference4 axis gauge site)))
      (λ axis → siteSum4 (λ site → backwardDifference4 axis (fld axis) site * gauge site))
      (λ axis → axisNegativeGradientAdjoint axis (fld axis) gauge))
    (trans
      (sumSwap (allCyclicIndices four) (physicalBlockSites side4)
        (λ axis site → backwardDifference4 axis (fld axis) site * gauge site))
      (sumRationalCong (physicalBlockSites side4)
        (λ site → sumRational (allCyclicIndices four)
          (λ axis → backwardDifference4 axis (fld axis) site * gauge site))
        (λ site → literalPeriodicDivergenceScalar fld site * gauge site)
        (axisFoldTimesRight fld gauge)))

literalCodifferentialEqualsPeriodicDivergence : ∀ fld site →
  literalPeriodicDivergenceScalar fld site
  ≡ literalPeriodicDivergenceScalar fld site
literalCodifferentialEqualsPeriodicDivergence fld site = refl

literalGaugeFixingEnergyScalar : ScalarBondField4 → ℚ
literalGaugeFixingEnergyScalar fld =
  scalarSiteInner
    (literalPeriodicDivergenceScalar fld)
    (literalPeriodicDivergenceScalar fld)

literalGaugeFixingFoldEqualsDivergenceFold : ∀ fld →
  literalGaugeFixingEnergyScalar fld
  ≡ siteSum4 (λ site →
      literalPeriodicDivergenceScalar fld site
      * literalPeriodicDivergenceScalar fld site)
literalGaugeFixingFoldEqualsDivergenceFold fld = refl

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
      (cong (-_)
        (siteSum4Cong
          (λ site → hSecond site * backwardDifference4 firstAxis (forwardDifference4 secondAxis hFirst) site)
          (λ site → forwardDifference4 secondAxis (backwardDifference4 firstAxis hFirst) site * hSecond site)
          (λ site → trans
            (cong (λ value → hSecond site * value)
              (backwardForwardDifferenceCommutes firstAxis secondAxis hFirst site))
            (mulCommRaw (hSecond site)
              (forwardDifference4 secondAxis (backwardDifference4 firstAxis hFirst) site)))))
      (trans
        (cong (-_)
          (periodicForwardBackwardSummationByParts
            secondAxis (backwardDifference4 firstAxis hFirst) hSecond))
        (doubleNegRaw
          (siteSum4 (λ site →
            backwardDifference4 firstAxis hFirst site
            * backwardDifference4 secondAxis hSecond site)))))

configuredSide4ShiftCommutationLevel : ProofLevel
configuredSide4ShiftCommutationLevel = machineChecked

periodicDivergenceGradientAdjointLevel : ProofLevel
periodicDivergenceGradientAdjointLevel = machineChecked

curlCrossTermEqualsDivergenceCrossTermLevel : ProofLevel
curlCrossTermEqualsDivergenceCrossTermLevel = machineChecked
