module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceSixBlockLiveExact where

------------------------------------------------------------------------
-- S2b2d1b2 / LIVE PHYSICAL COVARIANCE -> SIX SIGNED THREE-CLASS PAIR BLOCKS
--
-- This is the quantitatively safe Bony normal form for the actual d1b2
-- covariance.  It keeps the complete multiplier differences and therefore
-- never exposes the global n*S_tau-S_tot coefficient class-by-class.
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
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as RateLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianBonyPairBlocksExact as B16
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianThreeClassPairBlocksExact as B6

F : C3.RealField _
F = Rational.rationalRealField

module LiveSix
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Rate = RateLive.LiveBony physicalSystem S output

  nu : ℚ
  nu = Field30.viscosity physicalSystem

  blocks16 : B16.BonyPairBlocks
  blocks16 =
    B16.pairBlocks
      Rate.inputMass
      (Live.work output)
      (Live.fibre output)

  blocks6 : B6.ThreeClassPairBlocks
  blocks6 = B6.fromSixteen blocks16

  sixSignedTotal : ℚ
  sixSignedTotal = B6.sixBlockTotal blocks6

  inputPairGraphIsSixBlocks :
    Pair.pairDifferenceWorkSum
      Rate.inputMass
      (Live.work output)
      (Live.fibre output)
    ≡ sixSignedTotal
  inputPairGraphIsSixBlocks =
    B6.pairDifferenceIsSixThreeClassBlocks
      Rate.inputMass
      (Live.work output)
      (Live.fibre output)

  liveCovarianceIsNegativeViscositySixBlocks :
    Live.coherentCovarianceNumerator output
    ≡ 0ℚ - nu * sixSignedTotal
  liveCovarianceIsNegativeViscositySixBlocks =
    trans
      (Live.exactCentering output)
      (trans
        (cong (0ℚ -_) Rate.pairDifferenceRateIsViscosityInput)
        (cong
          (λ selected → 0ℚ - nu * selected)
          inputPairGraphIsSixBlocks))

  negativeSixBlockExpansion :
    0ℚ - sixSignedTotal
    ≡
      (0ℚ - B6.farLowFarLow blocks6)
      + (0ℚ - B6.farLowHighHigh blocks6)
      + (0ℚ - B6.farLowComparable blocks6)
      + (0ℚ - B6.highHighHighHigh blocks6)
      + (0ℚ - B6.highHighComparable blocks6)
      + (0ℚ - B6.comparableComparable blocks6)
  negativeSixBlockExpansion =
    solve
      ( B6.farLowFarLow blocks6
      ∷ B6.farLowHighHigh blocks6
      ∷ B6.farLowComparable blocks6
      ∷ B6.highHighHighHigh blocks6
      ∷ B6.highHighComparable blocks6
      ∷ B6.comparableComparable blocks6
      ∷ [])

  liveCovarianceIsSixSignedBonyBlocks :
    Live.coherentCovarianceNumerator output
    ≡
    nu *
      ( (0ℚ - B6.farLowFarLow blocks6)
      + (0ℚ - B6.farLowHighHigh blocks6)
      + (0ℚ - B6.farLowComparable blocks6)
      + (0ℚ - B6.highHighHighHigh blocks6)
      + (0ℚ - B6.highHighComparable blocks6)
      + (0ℚ - B6.comparableComparable blocks6) )
  liveCovarianceIsSixSignedBonyBlocks =
    trans
      liveCovarianceIsNegativeViscositySixBlocks
      (trans
        (solve (nu ∷ sixSignedTotal ∷ []))
        (cong (nu *_) negativeSixBlockExpansion))

liveD1b2SixSignedThreeClassPairBlockNormalFormClosed : Bool
liveD1b2SixSignedThreeClassPairBlockNormalFormClosed = true

liveD1b2SixBlockNormalFormRetainsMultiplierDifference : Bool
liveD1b2SixBlockNormalFormRetainsMultiplierDifference = true

liveD1b2SixBlockNormalFormIntroducesFibreCardinality : Bool
liveD1b2SixBlockNormalFormIntroducesFibreCardinality = false

liveD1b2SixBlockNormalFormIntroducesNorm : Bool
liveD1b2SixBlockNormalFormIntroducesNorm = false

liveD1b2SixBlockQuantitativePaymentClosedHere : Bool
liveD1b2SixBlockQuantitativePaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

liveD1b2SixSignedThreeClassPairBlockNormalFormClosedIsTrue :
  liveD1b2SixSignedThreeClassPairBlockNormalFormClosed ≡ true
liveD1b2SixSignedThreeClassPairBlockNormalFormClosedIsTrue = refl
