module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceFilteredRegionLiveExact where

------------------------------------------------------------------------
-- S2b2d1b2 / LIVE d1b2 -> FILTERED PHYSICAL R236 COVARIANCES
--
-- The filtered-list owner gives an exact decomposition of the input-mass pair
-- graph into six physical region covariances.  Compose that with the live
-- viscosity factor:
--
--   C_k = -nu * [
--       Cov(DFL)
--     + Bip(DFL,DHH)
--     + Bip(DFL,Core)
--     + Cov(DHH)
--     + Bip(DHH,Core)
--     + Cov(Core) ].
--
-- Every term is now carried by an actual filtered list and inherits a closed
-- form from either pairDifferenceClosedForm or bipartiteClosedForm.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _-_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as RateLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianCriticalRegionFilteredExact as Filtered

F : C3.RealField _
F = Rational.rationalRealField

module LiveFiltered
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Rate = RateLive.LiveBony physicalSystem S output

  nu : ℚ
  nu = Field30.viscosity physicalSystem

  filteredSignedTotal : ℚ
  filteredSignedTotal =
    Filtered.sixFilteredRegionCovariance
      Rate.inputMass
      (Live.work output)
      (Live.fibre output)

  inputPairGraphIsFilteredRegionCovariance :
    Pair.pairDifferenceWorkSum
      Rate.inputMass
      (Live.work output)
      (Live.fibre output)
    ≡ filteredSignedTotal
  inputPairGraphIsFilteredRegionCovariance =
    Filtered.pairDifferenceIsSixFilteredRegionCovariances
      Rate.inputMass
      (Live.work output)
      (Live.fibre output)

  liveCovarianceIsNegativeViscosityFilteredRegions :
    Live.coherentCovarianceNumerator output
    ≡ 0ℚ - nu * filteredSignedTotal
  liveCovarianceIsNegativeViscosityFilteredRegions =
    trans
      (Live.exactCentering output)
      (trans
        (cong (0ℚ -_) Rate.pairDifferenceRateIsViscosityInput)
        (cong
          (λ selected → 0ℚ - nu * selected)
          inputPairGraphIsFilteredRegionCovariance))

liveD1b2FilteredPhysicalRegionNormalFormClosed : Bool
liveD1b2FilteredPhysicalRegionNormalFormClosed = true

liveD1b2FilteredRegionBlocksHaveListCarriers : Bool
liveD1b2FilteredRegionBlocksHaveListCarriers = true

liveD1b2FilteredRegionNormalFormIntroducesNorm : Bool
liveD1b2FilteredRegionNormalFormIntroducesNorm = false

liveD1b2FilteredRegionNormalFormIntroducesCardinalityEstimate : Bool
liveD1b2FilteredRegionNormalFormIntroducesCardinalityEstimate = false

liveD1b2FilteredRegionQuantitativePaymentClosedHere : Bool
liveD1b2FilteredRegionQuantitativePaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

liveD1b2FilteredPhysicalRegionNormalFormClosedIsTrue :
  liveD1b2FilteredPhysicalRegionNormalFormClosed ≡ true
liveD1b2FilteredPhysicalRegionNormalFormClosedIsTrue = refl
