module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceCriticalRegionLiveExact where

------------------------------------------------------------------------
-- S2b2d1b2 / LIVE d1b2 -> SIX PHYSICAL R236 REGION-PAIR BLOCKS
--
-- The complete input-Laplacian pair graph is now routed by the literal R236
-- classifier, retaining every multiplier difference:
--
--   DFL-DFL, DFL-DHH, DFL-Core,
--   DHH-DHH, DHH-Core, Core-Core.
--
-- Combining with rate_tau = nu S_tau and exact d1b2 centering gives the live
-- covariance as viscosity times the NEGATIVE sum of those six signed blocks.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as RateLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianCriticalRegionPairBlocksExact as Region

F : C3.RealField _
F = Rational.rationalRealField

module LiveRegion
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Rate = RateLive.LiveBony physicalSystem S output

  nu : ℚ
  nu = Field30.viscosity physicalSystem

  regionBlocks : Region.RegionPairBlocks
  regionBlocks =
    Region.pairBlocks
      Rate.inputMass
      (Live.work output)
      (Live.fibre output)

  sixRegionSignedTotal : ℚ
  sixRegionSignedTotal = Region.sixRegionTotal regionBlocks

  inputPairGraphIsSixPhysicalRegionBlocks :
    Pair.pairDifferenceWorkSum
      Rate.inputMass
      (Live.work output)
      (Live.fibre output)
    ≡ sixRegionSignedTotal
  inputPairGraphIsSixPhysicalRegionBlocks =
    Region.pairDifferenceIsSixPhysicalRegionBlocks
      Rate.inputMass
      (Live.work output)
      (Live.fibre output)

  liveCovarianceIsNegativeViscositySixRegionBlocks :
    Live.coherentCovarianceNumerator output
    ≡ 0ℚ - nu * sixRegionSignedTotal
  liveCovarianceIsNegativeViscositySixRegionBlocks =
    trans
      (Live.exactCentering output)
      (trans
        (cong (0ℚ -_) Rate.pairDifferenceRateIsViscosityInput)
        (cong
          (λ selected → 0ℚ - nu * selected)
          inputPairGraphIsSixPhysicalRegionBlocks))

  negativeRegionExpansion :
    0ℚ - sixRegionSignedTotal
    ≡
      (0ℚ - Region.deepFarLowDeepFarLow regionBlocks)
      + (0ℚ - Region.deepFarLowDeepHighHigh regionBlocks)
      + (0ℚ - Region.deepFarLowCriticalCore regionBlocks)
      + (0ℚ - Region.deepHighHighDeepHighHigh regionBlocks)
      + (0ℚ - Region.deepHighHighCriticalCore regionBlocks)
      + (0ℚ - Region.criticalCoreCriticalCore regionBlocks)
  negativeRegionExpansion =
    solve
      ( Region.deepFarLowDeepFarLow regionBlocks
      ∷ Region.deepFarLowDeepHighHigh regionBlocks
      ∷ Region.deepFarLowCriticalCore regionBlocks
      ∷ Region.deepHighHighDeepHighHigh regionBlocks
      ∷ Region.deepHighHighCriticalCore regionBlocks
      ∷ Region.criticalCoreCriticalCore regionBlocks
      ∷ [])

  liveCovarianceIsSixSignedPhysicalRegionBlocks :
    Live.coherentCovarianceNumerator output
    ≡
    nu *
      ( (0ℚ - Region.deepFarLowDeepFarLow regionBlocks)
      + (0ℚ - Region.deepFarLowDeepHighHigh regionBlocks)
      + (0ℚ - Region.deepFarLowCriticalCore regionBlocks)
      + (0ℚ - Region.deepHighHighDeepHighHigh regionBlocks)
      + (0ℚ - Region.deepHighHighCriticalCore regionBlocks)
      + (0ℚ - Region.criticalCoreCriticalCore regionBlocks) )
  liveCovarianceIsSixSignedPhysicalRegionBlocks =
    trans
      liveCovarianceIsNegativeViscositySixRegionBlocks
      (trans
        (solve (nu ∷ sixRegionSignedTotal ∷ []))
        (cong (nu *_) negativeRegionExpansion))

liveD1b2PhysicalR236SixBlockNormalFormClosed : Bool
liveD1b2PhysicalR236SixBlockNormalFormClosed = true

liveD1b2PhysicalR236NormalFormRetainsMultiplierDifferences : Bool
liveD1b2PhysicalR236NormalFormRetainsMultiplierDifferences = true

liveD1b2PhysicalR236NormalFormIntroducesFibreCardinality : Bool
liveD1b2PhysicalR236NormalFormIntroducesFibreCardinality = false

liveD1b2PhysicalR236QuantitativePaymentClosedHere : Bool
liveD1b2PhysicalR236QuantitativePaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

liveD1b2PhysicalR236SixBlockNormalFormClosedIsTrue :
  liveD1b2PhysicalR236SixBlockNormalFormClosed ≡ true
liveD1b2PhysicalR236SixBlockNormalFormClosedIsTrue = refl
