module DASHI.Physics.Closure.NSTriadKNFixedOutputNestedBonyCrossRound433Exact where

------------------------------------------------------------------------
-- ROUND433 / FIXED-OUTPUT NESTED CROSS -> THREE PHYSICAL BONY CLASSES
--
-- R432 reduces the live R406/R423 problem to coherence inside one fixed output
-- fibre.  R186 already proves that every literal physical incidence belongs to
-- one of three swap-invariant partner classes:
--
--   farLow = LH union HL,  highHigh = HH -> low,  comparable = CC.
--
-- An R329 nested cell stores its outer interaction as the SAME
-- `PhysicalTriadIncidence`, so the authoritative R186 classification applies
-- definitionally to the live outer cell.  No new shell classifier is needed.
--
-- Because the R299 aggregate cross is linear in the forcing aggregate, a fixed
-- output payment can be split into three class contributions.  The scalar
-- compiler below records the exact consequence: if the three class crosses are
-- bounded, their sum bounds the total cross with no factor depending on cutoff,
-- shell count, or fibre cardinality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact as R329
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlPartnerBonyRound186Exact as R186

F : C3.RealField _
F = R329.F

nestedOuterBonyClass :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F) →
  R329.StrongLowLiteralNestedCell E I O system S L H W →
  R186.PartnerBonyClass
nestedOuterBonyClass E I O system S L H W C =
  R186.partnerBonyClass (R329.outer C)

record ThreeBonyClassSignedCrossPayment : Set where
  constructor three-bony-class-signed-cross-payment
  field
    totalCross : ℚ
    farLowCross highHighCross comparableCross : ℚ
    farLowBudget highHighBudget comparableBudget : ℚ

    totalCrossSplits :
      totalCross ≡ farLowCross + highHighCross + comparableCross

    farLowPaid : farLowCross ≤ farLowBudget
    highHighPaid : highHighCross ≤ highHighBudget
    comparablePaid : comparableCross ≤ comparableBudget

open ThreeBonyClassSignedCrossPayment public

threeBonyClassPaymentsBoundTotalCross :
  (P : ThreeBonyClassSignedCrossPayment) →
  totalCross P
  ≤ farLowBudget P + highHighBudget P + comparableBudget P
threeBonyClassPaymentsBoundTotalCross P =
  let
    classSumBound :
      farLowCross P + highHighCross P + comparableCross P
      ≤ farLowBudget P + highHighBudget P + comparableBudget P
    classSumBound =
      ℚP.+-mono-≤
        (ℚP.+-mono-≤ (farLowPaid P) (highHighPaid P))
        (comparablePaid P)
  in
  subst
    (λ lower →
      lower ≤ farLowBudget P + highHighBudget P + comparableBudget P)
    (sym (totalCrossSplits P))
    classSumBound

round433NestedOuterUsesLiteralR186BonyClassification : Bool
round433NestedOuterUsesLiteralR186BonyClassification = true

round433PhysicalBonyClassCountIsFixedThree : Bool
round433PhysicalBonyClassCountIsFixedThree = true

round433BonyClassReductionAddsCutoffFactor : Bool
round433BonyClassReductionAddsCutoffFactor = false

round433FarLowClassCrossPaid : Bool
round433FarLowClassCrossPaid = false

round433HighHighClassCrossPaid : Bool
round433HighHighClassCrossPaid = false

round433ComparableClassCrossPaid : Bool
round433ComparableClassCrossPaid = false

round433FixedOutputCoherenceClosed : Bool
round433FixedOutputCoherenceClosed = false

round433R423SignedCommonCrossPaid : Bool
round433R423SignedCommonCrossPaid = false

round433PackageAClosed : Bool
round433PackageAClosed = false

round433ClayPromotion : Bool
round433ClayPromotion = false

round433NestedOuterUsesLiteralR186BonyClassificationIsTrue :
  round433NestedOuterUsesLiteralR186BonyClassification ≡ true
round433NestedOuterUsesLiteralR186BonyClassificationIsTrue = refl

round433BonyClassReductionAddsCutoffFactorIsFalse :
  round433BonyClassReductionAddsCutoffFactor ≡ false
round433BonyClassReductionAddsCutoffFactorIsFalse = refl

round433FixedOutputCoherenceClosedIsFalse :
  round433FixedOutputCoherenceClosed ≡ false
round433FixedOutputCoherenceClosedIsFalse = refl
