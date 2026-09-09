module DASHI.Physics.Closure.NSTriadKNModernCriticalConeSameObjectBidiRound588Exact where

------------------------------------------------------------------------
-- ROUND588 / MODERN THREE-CLASS NESTED CARRIER <-> HISTORICAL R434
-- CRITICAL-CONE PRODUCER: SAME-OBJECT FIREWALL
--
-- R587 gives a strong sufficient route on the live R573/R584 nested-slot
-- carrier: one far-low norm budget (LH = HL), one HH->low norm budget, and one
-- comparable norm budget.
--
-- The older R434 route is weaker and potentially higher-alpha analytically.  It
-- does not ask for all three full class norms.  Instead it splits the physical
-- Bony regions further into
--
--   deep FL       + FL shoulder
--   deep HH       + HH shoulder
--   comparable,
--
-- pays the two deep pieces by E*D, and retains
--
--   FL shoulder + HH shoulder + comparable
--
-- as one signed critical cone with a relative covariance payment.
--
-- IMPORTANT: R284/R434 store scalar payment coordinates.  They are NOT indexed
-- by R573's literal nested-slot cells and therefore cannot be silently used as
-- a theorem about the modern carrier.  The correct reuse boundary is one exact
-- same-object equality from the modern fixed-output signed response to R434's
-- fixedOutputCross.  Once that equality is supplied, the old conditional
-- compiler transports immediately; no new inequality is required here.
--
-- R440 already gives the exact finite modern signed scalar reached from R438:
--
--   fixedOutputPhysicalCommonCross W S system output.
--
-- This file therefore specializes the generic same-object weld to that literal
-- R440 scalar.  The specialization does NOT construct the equality receipt; it
-- merely ensures the surviving historical payment is asked on the exact modern
-- object rather than an untyped rational placeholder.
--
-- This file prevents three wrong turns:
--   * making R587's stronger three full-norm bounds mandatory;
--   * source-laundering R434's abstract scalar payment into R573 without a weld;
--   * identifying R434's OUTER Bony partition with R587's INNER post-slot Bony
--     partition merely because both use far-low/high-high/comparable names.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact as R440
import DASHI.Physics.Closure.NSTriadKNDeepFarLowCriticalShoulderRound234Exact as R234
import DASHI.Physics.Closure.NSTriadKNDeepHHNullCriticalShoulderRound235Exact as R235
import DASHI.Physics.Closure.NSTriadKNParabolicCriticalFrequencyConeRound236Exact as R236
import DASHI.Physics.Closure.NSTriadKNCriticalConeRelativeCovarianceTargetRound284Exact as R284
import DASHI.Physics.Closure.NSTriadKNFixedOutputCriticalConeCompilerRound434Exact as R434
import DASHI.Physics.Closure.NSTriadKNNestedSlotThreeClassNormCompilerRound587Exact as R587
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

------------------------------------------------------------------------
-- Exact scalar refinement shape needed to compare the coarse modern three
-- classes with the historical deep/shoulder critical-cone decomposition.
------------------------------------------------------------------------

record ThreeClassCriticalRefinement588 : Set where
  constructor three-class-critical-refinement-588
  field
    farLowSigned highHighSigned comparableSigned : ℚ
    deepFarLowSigned farLowShoulderSigned : ℚ
    deepHighHighSigned highHighShoulderSigned : ℚ
    criticalCoreSigned : ℚ

    farLowRefines588 :
      farLowSigned ≡ deepFarLowSigned + farLowShoulderSigned
    highHighRefines588 :
      highHighSigned ≡ deepHighHighSigned + highHighShoulderSigned
    criticalCoreRefines588 :
      criticalCoreSigned
      ≡ farLowShoulderSigned + highHighShoulderSigned + comparableSigned

open ThreeClassCriticalRefinement588 public

------------------------------------------------------------------------
-- Same-object transport of the HISTORICAL conditional bound.
------------------------------------------------------------------------

record HistoricalCriticalConeSameObjectWeld588
    (modernFixedOutputSignedResponse : ℚ) : Set where
  constructor historical-critical-cone-same-object-weld-588
  field
    historicalDecomposition588 : R434.FixedOutputCriticalConeDecomposition
    sameFixedOutputSignedResponse588 :
      modernFixedOutputSignedResponse
      ≡ R434.fixedOutputCross historicalDecomposition588

open HistoricalCriticalConeSameObjectWeld588 public

modernSignedResponseBelowHistoricalCriticalBudget588 :
  (modernFixedOutputSignedResponse : ℚ) →
  (weld : HistoricalCriticalConeSameObjectWeld588 modernFixedOutputSignedResponse) →
  modernFixedOutputSignedResponse
  ≤ R284.theta (R434.payment (historicalDecomposition588 weld))
      * R284.coreCompanionMass (R434.payment (historicalDecomposition588 weld))
    + (R284.paidDeepCoefficient (R434.payment (historicalDecomposition588 weld))
      + R284.coreEDCoefficient (R434.payment (historicalDecomposition588 weld)))
      * R284.energyDissipation (R434.payment (historicalDecomposition588 weld))
modernSignedResponseBelowHistoricalCriticalBudget588 modern weld =
  subst
    (λ lower →
      lower
      ≤ R284.theta (R434.payment (historicalDecomposition588 weld))
          * R284.coreCompanionMass (R434.payment (historicalDecomposition588 weld))
        + (R284.paidDeepCoefficient (R434.payment (historicalDecomposition588 weld))
          + R284.coreEDCoefficient (R434.payment (historicalDecomposition588 weld)))
          * R284.energyDissipation (R434.payment (historicalDecomposition588 weld)))
    (sym (sameFixedOutputSignedResponse588 weld))
    (R434.fixedOutputCrossBelowCriticalConeBudget
      (historicalDecomposition588 weld))

------------------------------------------------------------------------
-- Literal modern specialization: use exactly R440's finite common cross.
------------------------------------------------------------------------

liveR440CommonCrossBelowHistoricalCriticalBudget588 :
  ∀ {E : C3.IntegerEmbedding R440.F}
    {I : C3.ModeInverseSquare R440.F E}
    (W : R294.SwapInvariantCellWeight R440.F)
    (S : Helical.HelicalModeScalars R440.F)
    (system : Audit.FiniteComplex3GalerkinSystem R440.F E I)
    (output : Z3.FourierMode) →
  (weld : HistoricalCriticalConeSameObjectWeld588
    (R440.fixedOutputPhysicalCommonCross W S system output)) →
  R440.fixedOutputPhysicalCommonCross W S system output
  ≤ R284.theta (R434.payment (historicalDecomposition588 weld))
      * R284.coreCompanionMass (R434.payment (historicalDecomposition588 weld))
    + (R284.paidDeepCoefficient (R434.payment (historicalDecomposition588 weld))
      + R284.coreEDCoefficient (R434.payment (historicalDecomposition588 weld)))
      * R284.energyDissipation (R434.payment (historicalDecomposition588 weld))
liveR440CommonCrossBelowHistoricalCriticalBudget588 W S system output =
  modernSignedResponseBelowHistoricalCriticalBudget588
    (R440.fixedOutputPhysicalCommonCross W S system output)

------------------------------------------------------------------------
-- Introspective dependency correction.
------------------------------------------------------------------------

round588ModernThreeFullClassNormsMandatory : Bool
round588ModernThreeFullClassNormsMandatory = false

round588HistoricalCriticalConeIsAdmissibleWeakerProducer : Bool
round588HistoricalCriticalConeIsAdmissibleWeakerProducer = true

round588HistoricalScalarCarrierAutomaticallySameAsLiveR573Carrier : Bool
round588HistoricalScalarCarrierAutomaticallySameAsLiveR573Carrier = false

round588ExactLiveR440SignedCommonCrossTargeted : Bool
round588ExactLiveR440SignedCommonCrossTargeted = true

round588HistoricalOuterClassEqualsModernInnerPostSlotClass : Bool
round588HistoricalOuterClassEqualsModernInnerPostSlotClass = false

round588CriticalConeStrictlyLargerThanComparableClass : Bool
round588CriticalConeStrictlyLargerThanComparableClass =
  R236.round236CriticalConeStrictlyLargerThanComparableClass

round588DeepFarLowPhysicalPaymentClosed : Bool
round588DeepFarLowPhysicalPaymentClosed =
  R234.round234PhysicalBernsteinShellWeldClosed

round588DeepHighHighPhysicalPaymentClosed : Bool
round588DeepHighHighPhysicalPaymentClosed =
  R235.round235PhysicalHHConvolutionPaymentClosed

round588CriticalConeRelativeCovarianceClosed : Bool
round588CriticalConeRelativeCovarianceClosed =
  R284.round284PhysicalCriticalConeRelativeCovarianceClosed

round588AllHistoricalPhysicalPaymentsClosed : Bool
round588AllHistoricalPhysicalPaymentsClosed = false

round588LiveR440ToHistoricalR434SameObjectWeldConstructed : Bool
round588LiveR440ToHistoricalR434SameObjectWeldConstructed = false

round588CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round588CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round588ClayPromotion : Bool
round588ClayPromotion = false

round588ModernThreeFullClassNormsMandatoryIsFalse :
  round588ModernThreeFullClassNormsMandatory ≡ false
round588ModernThreeFullClassNormsMandatoryIsFalse = refl

round588HistoricalCriticalConeIsAdmissibleWeakerProducerIsTrue :
  round588HistoricalCriticalConeIsAdmissibleWeakerProducer ≡ true
round588HistoricalCriticalConeIsAdmissibleWeakerProducerIsTrue = refl

round588HistoricalScalarCarrierAutomaticallySameAsLiveR573CarrierIsFalse :
  round588HistoricalScalarCarrierAutomaticallySameAsLiveR573Carrier ≡ false
round588HistoricalScalarCarrierAutomaticallySameAsLiveR573CarrierIsFalse = refl

round588ExactLiveR440SignedCommonCrossTargetedIsTrue :
  round588ExactLiveR440SignedCommonCrossTargeted ≡ true
round588ExactLiveR440SignedCommonCrossTargetedIsTrue = refl

round588HistoricalOuterClassEqualsModernInnerPostSlotClassIsFalse :
  round588HistoricalOuterClassEqualsModernInnerPostSlotClass ≡ false
round588HistoricalOuterClassEqualsModernInnerPostSlotClassIsFalse = refl

round588ClayPromotionIsFalse : round588ClayPromotion ≡ false
round588ClayPromotionIsFalse = refl
