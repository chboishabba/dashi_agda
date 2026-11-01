module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalSixBlockPaymentLiveExact where

------------------------------------------------------------------------
-- S2b2d1b2 / LEAST-PRIVILEGE PAYMENT SOCKET ON THE SAFE SIX-BLOCK NORMAL FORM
--
-- The live d1b2 covariance is already exactly viscosity times the negative sum
-- of six fixed Bony pair blocks.  This owner asks for bounds on those six
-- signed coordinates directly and compiles them to a fixed-output payment.
--
-- It is intentionally weaker than a uniform Gram/operator theorem and avoids
-- the risky globally-centered class-vector estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceSixBlockLiveExact as SixLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianThreeClassPairBlocksExact as B6

F : C3.RealField _
F = Rational.rationalRealField

module SixBlockPayment
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Six = SixLive.LiveSix physicalSystem S output

  record PhysicalSixBlockPayment : Set where
    constructor physical-six-block-payment
    field
      farLowFarLowBudget
      farLowHighHighBudget
      farLowComparableBudget
      highHighHighHighBudget
      highHighComparableBudget
      comparableComparableBudget : ℚ

      viscosityNN :
        0ℚ ≤ Field30.viscosity physicalSystem

      farLowFarLowPaid :
        0ℚ - B6.farLowFarLow Six.blocks6
        ≤ farLowFarLowBudget

      farLowHighHighPaid :
        0ℚ - B6.farLowHighHigh Six.blocks6
        ≤ farLowHighHighBudget

      farLowComparablePaid :
        0ℚ - B6.farLowComparable Six.blocks6
        ≤ farLowComparableBudget

      highHighHighHighPaid :
        0ℚ - B6.highHighHighHigh Six.blocks6
        ≤ highHighHighHighBudget

      highHighComparablePaid :
        0ℚ - B6.highHighComparable Six.blocks6
        ≤ highHighComparableBudget

      comparableComparablePaid :
        0ℚ - B6.comparableComparable Six.blocks6
        ≤ comparableComparableBudget

  open PhysicalSixBlockPayment public

  totalSixBudget : PhysicalSixBlockPayment → ℚ
  totalSixBudget P =
      farLowFarLowBudget P
    + farLowHighHighBudget P
    + farLowComparableBudget P
    + highHighHighHighBudget P
    + highHighComparableBudget P
    + comparableComparableBudget P

  liveSixBudget : PhysicalSixBlockPayment → ℚ
  liveSixBudget P =
    Field30.viscosity physicalSystem * totalSixBudget P

  sixSignedBlocksBelowBudget :
    (P : PhysicalSixBlockPayment) →
    (0ℚ - B6.farLowFarLow Six.blocks6)
      + (0ℚ - B6.farLowHighHigh Six.blocks6)
      + (0ℚ - B6.farLowComparable Six.blocks6)
      + (0ℚ - B6.highHighHighHigh Six.blocks6)
      + (0ℚ - B6.highHighComparable Six.blocks6)
      + (0ℚ - B6.comparableComparable Six.blocks6)
    ≤ totalSixBudget P
  sixSignedBlocksBelowBudget P =
    ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (ℚP.+-mono-≤
            (ℚP.+-mono-≤
              (farLowFarLowPaid P)
              (farLowHighHighPaid P))
            (farLowComparablePaid P))
          (highHighHighHighPaid P))
        (highHighComparablePaid P))
      (comparableComparablePaid P)

  physicalSixBlockPaymentClosesFixedOutput :
    (P : PhysicalSixBlockPayment) →
    Live.coherentCovarianceNumerator output
    ≤ liveSixBudget P
  physicalSixBlockPaymentClosesFixedOutput P =
    let
      signed =
        (0ℚ - B6.farLowFarLow Six.blocks6)
        + (0ℚ - B6.farLowHighHigh Six.blocks6)
        + (0ℚ - B6.farLowComparable Six.blocks6)
        + (0ℚ - B6.highHighHighHigh Six.blocks6)
        + (0ℚ - B6.highHighComparable Six.blocks6)
        + (0ℚ - B6.comparableComparable Six.blocks6)

      scaled :
        Field30.viscosity physicalSystem * signed
        ≤ Field30.viscosity physicalSystem * totalSixBudget P
      scaled =
        let instance nuNN = nonNegative (viscosityNN P)
        in
        ℚP.*-monoˡ-≤-nonNeg
          (Field30.viscosity physicalSystem)
          (sixSignedBlocksBelowBudget P)
    in
    subst
      (_≤ liveSixBudget P)
      (sym Six.liveCovarianceIsSixSignedBonyBlocks)
      scaled

liveSixBlockPaymentCompilerClosed : Bool
liveSixBlockPaymentCompilerClosed = true

liveSixBlockProducerBoundsClosedHere : Bool
liveSixBlockProducerBoundsClosedHere = false

liveSixBlockPaymentIntroducesFibreCardinality : Bool
liveSixBlockPaymentIntroducesFibreCardinality = false

clayPromotion : Bool
clayPromotion = false

liveSixBlockPaymentCompilerClosedIsTrue :
  liveSixBlockPaymentCompilerClosed ≡ true
liveSixBlockPaymentCompilerClosedIsTrue = refl
