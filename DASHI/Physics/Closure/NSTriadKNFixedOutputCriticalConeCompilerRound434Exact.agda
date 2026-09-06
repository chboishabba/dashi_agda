module DASHI.Physics.Closure.NSTriadKNFixedOutputCriticalConeCompilerRound434Exact where

------------------------------------------------------------------------
-- ROUND434 / R284 CRITICAL CONE -> FIXED-OUTPUT R423 CROSS BUDGET
--
-- R432 removes cross-output coherence.  R433 reduces one fixed-output nested
-- family to the authoritative three physical Bony classes.  R284 already
-- sharpens those classes further:
--
--   deep far-low  -> E D,
--   deep high-high -> E D,
--   critical cone = FL shoulder + HH shoulder + comparable.
--
-- Thus the fixed-output coherent theorem does not need to re-pay the deep
-- regions.  If R284's critical-core relative covariance holds,
--
--   D_core <= theta Q_core + C_core E D,   theta < 1,
--
-- then adding the already-paid deep masses gives
--
--   fixedOutputCross
--     <= theta Q_core + (C_deep + C_core) E D.
--
-- This owner is only the scalar compiler.  It does not claim the physical
-- critical-cone covariance receipt is inhabited.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNCriticalConeRelativeCovarianceTargetRound284Exact as R284
import DASHI.Physics.Closure.NSTriadKNFixedOutputSignedCrossAggregationRound432Exact as R432
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
round434CrossOutputCoherenceAlreadyRemoved =
  not R432.round432CrossOutputCoherencePaymentRequired
  where
  not : Bool → Bool
  not true = false
  not false = true

round434ThreeBonyClassReductionAlreadyAvailable : Bool
round434ThreeBonyClassReductionAlreadyAvailable =
  R433.round433NestedOuterUsesLiteralR186BonyClassification

round434DeepFarLowAlreadyDelegatedToED : Bool
round434DeepFarLowAlreadyDelegatedToED =
  R284.round284DeepFarLowDelegatedToRound234Region

round434DeepHighHighAlreadyDelegatedToED : Bool
round434DeepHighHighAlreadyDelegatedToED =
  R284.round284DeepHHDelegatedToRound235NullRegion

round434NovelFixedOutputRegionIsCriticalCone : Bool
round434NovelFixedOutputRegionIsCriticalCone =
  R284.round284NovelRegionIsParabolicCriticalCone

round434CriticalConeCompilerClosed : Bool
round434CriticalConeCompilerClosed = true

round434PhysicalCriticalConeCovarianceClosed : Bool
round434PhysicalCriticalConeCovarianceClosed =
  R284.round284PhysicalCriticalConeRelativeCovarianceClosed

round434R423SignedCommonCrossPaid : Bool
round434R423SignedCommonCrossPaid = false

round434PackageAClosed : Bool
round434PackageAClosed = false

round434ClayPromotion : Bool
round434ClayPromotion = false

round434CriticalConeCompilerClosedIsTrue :
  round434CriticalConeCompilerClosed ≡ true
round434CriticalConeCompilerClosedIsTrue = refl

round434PhysicalCriticalConeCovarianceClosedIsFalse :
  round434PhysicalCriticalConeCovarianceClosed ≡ false
round434PhysicalCriticalConeCovarianceClosedIsFalse =
  R284.round284PhysicalCriticalConeRelativeCovarianceClosedIsFalse
