module DASHI.Physics.Closure.NSTriadKNFixedOutputCriticalConeCompilerRound434Exact where

------------------------------------------------------------------------
-- ROUND434 / R284 CRITICAL CONE -> FIXED-OUTPUT R423 CROSS BUDGET
--
-- R432 removes cross-output coherence. R433 reduces one fixed-output nested
-- family to the authoritative three physical Bony classes. R284 sharpens those
-- classes into deep far-low, deep high-high, and the critical cone
-- (FL shoulder + HH shoulder + comparable).
--
-- IMPORTANT STATUS CORRECTION
-- ---------------------------
-- R284 delegates the deep regions to R234/R235, but delegation is not physical
-- closure. R234 closes the scalar exponent/payment compiler while explicitly
-- leaving its physical Bernstein-shell weld open. R235 closes the HH exponent
-- and null-gain arithmetic while explicitly leaving its physical convolution
-- payment open.
--
-- The theorem below is therefore a CONDITIONAL compiler. A complete R284
-- payment already carries all three physical inequalities, and from it we get
--
--   fixedOutputCross
--     <= theta Q_core + (C_deep + C_core) E D.
--
-- The remaining physical producers are exactly:
--   (1) literal deep-FL Bernstein/convolution payment,
--   (2) literal deep-HH null/convolution payment,
--   (3) literal critical-cone relative covariance, theta < 1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNCriticalConeRelativeCovarianceTargetRound284Exact as R284
import DASHI.Physics.Closure.NSTriadKNDeepFarLowCriticalShoulderRound234Exact as R234
import DASHI.Physics.Closure.NSTriadKNDeepHHNullCriticalShoulderRound235Exact as R235
import DASHI.Physics.Closure.NSTriadKNFixedOutputNestedBonyCrossRound433Exact as R433

record FixedOutputCriticalConeDecomposition : Set where
  constructor fixed-output-critical-cone-decomposition
  field
    payment : R284.CriticalConeRelativeCovariancePayment
    fixedOutputCross : ℚ
    fixedOutputCrossMeaning :
      fixedOutputCross
      ≡ R284.paidDeepMass payment + R284.coreGramDebt payment

open FixedOutputCriticalConeDecomposition public

fixedOutputCrossBelowCriticalConeBudget :
  (D : FixedOutputCriticalConeDecomposition) →
  fixedOutputCross D
  ≤ R284.theta (payment D) * R284.coreCompanionMass (payment D)
    + (R284.paidDeepCoefficient (payment D)
      + R284.coreEDCoefficient (payment D))
      * R284.energyDissipation (payment D)
fixedOutputCrossBelowCriticalConeBudget D =
  let
    P = payment D
    summed :
      R284.paidDeepMass P + R284.coreGramDebt P
      ≤ R284.paidDeepCoefficient P * R284.energyDissipation P
        + (R284.theta P * R284.coreCompanionMass P
          + R284.coreEDCoefficient P * R284.energyDissipation P)
    summed = ℚP.+-mono-≤
      (R284.paidDeepRegionsCombine P)
      (R284.criticalCoreRelativeCovariance P)

    endpoint :
      R284.paidDeepCoefficient P * R284.energyDissipation P
        + (R284.theta P * R284.coreCompanionMass P
          + R284.coreEDCoefficient P * R284.energyDissipation P)
      ≡ R284.theta P * R284.coreCompanionMass P
        + (R284.paidDeepCoefficient P + R284.coreEDCoefficient P)
          * R284.energyDissipation P
    endpoint = solve
      ( R284.paidDeepCoefficient P
      ∷ R284.coreEDCoefficient P
      ∷ R284.energyDissipation P
      ∷ R284.theta P
      ∷ R284.coreCompanionMass P
      ∷ [])
  in
  subst
    (λ lower →
      lower
      ≤ R284.theta P * R284.coreCompanionMass P
        + (R284.paidDeepCoefficient P + R284.coreEDCoefficient P)
          * R284.energyDissipation P)
    (sym (fixedOutputCrossMeaning D))
    (subst
      (λ upper →
        R284.paidDeepMass P + R284.coreGramDebt P ≤ upper)
      endpoint
      summed)

round434CrossOutputCoherenceAlreadyRemoved : Bool
round434CrossOutputCoherenceAlreadyRemoved = true

round434ThreeBonyClassReductionAlreadyAvailable : Bool
round434ThreeBonyClassReductionAlreadyAvailable =
  R433.round433NestedOuterUsesLiteralR186BonyClassification

-- Compatibility names: delegated/routed, not physically closed.
round434DeepFarLowAlreadyDelegatedToED : Bool
round434DeepFarLowAlreadyDelegatedToED =
  R284.round284DeepFarLowDelegatedToRound234Region

round434DeepHighHighAlreadyDelegatedToED : Bool
round434DeepHighHighAlreadyDelegatedToED =
  R284.round284DeepHHDelegatedToRound235NullRegion

round434DeepFarLowScalarCompilerClosed : Bool
round434DeepFarLowScalarCompilerClosed =
  R234.round234DeepFarLowScalarPaymentCompilerClosed

round434DeepFarLowPhysicalWeldClosed : Bool
round434DeepFarLowPhysicalWeldClosed =
  R234.round234PhysicalBernsteinShellWeldClosed

round434DeepHighHighExponentCompilerClosed : Bool
round434DeepHighHighExponentCompilerClosed =
  R235.round235DeepHHThresholdIdentified

round434DeepHighHighPhysicalWeldClosed : Bool
round434DeepHighHighPhysicalWeldClosed =
  R235.round235PhysicalHHConvolutionPaymentClosed

round434NovelFixedOutputRegionIsCriticalCone : Bool
round434NovelFixedOutputRegionIsCriticalCone =
  R284.round284NovelRegionIsParabolicCriticalCone

round434CriticalConeCompilerClosed : Bool
round434CriticalConeCompilerClosed = true

round434PhysicalCriticalConeCovarianceClosed : Bool
round434PhysicalCriticalConeCovarianceClosed =
  R284.round284PhysicalCriticalConeRelativeCovarianceClosed

round434AllThreePhysicalRegionPaymentsClosed : Bool
round434AllThreePhysicalRegionPaymentsClosed = false

round434R423SignedCommonCrossPaid : Bool
round434R423SignedCommonCrossPaid = false

round434PackageAClosed : Bool
round434PackageAClosed = false

round434ClayPromotion : Bool
round434ClayPromotion = false

round434CrossOutputCoherenceAlreadyRemovedIsTrue :
  round434CrossOutputCoherenceAlreadyRemoved ≡ true
round434CrossOutputCoherenceAlreadyRemovedIsTrue = refl

round434CriticalConeCompilerClosedIsTrue :
  round434CriticalConeCompilerClosed ≡ true
round434CriticalConeCompilerClosedIsTrue = refl

round434DeepFarLowPhysicalWeldClosedIsFalse :
  round434DeepFarLowPhysicalWeldClosed ≡ false
round434DeepFarLowPhysicalWeldClosedIsFalse =
  R234.round234PhysicalBernsteinShellWeldClosedIsFalse

round434DeepHighHighPhysicalWeldClosedIsFalse :
  round434DeepHighHighPhysicalWeldClosed ≡ false
round434DeepHighHighPhysicalWeldClosedIsFalse = refl

round434PhysicalCriticalConeCovarianceClosedIsFalse :
  round434PhysicalCriticalConeCovarianceClosed ≡ false
round434PhysicalCriticalConeCovarianceClosedIsFalse =
  R284.round284PhysicalCriticalConeRelativeCovarianceClosedIsFalse

round434AllThreePhysicalRegionPaymentsClosedIsFalse :
  round434AllThreePhysicalRegionPaymentsClosed ≡ false
round434AllThreePhysicalRegionPaymentsClosedIsFalse = refl
