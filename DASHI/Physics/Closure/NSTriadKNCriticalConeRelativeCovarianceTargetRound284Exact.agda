module DASHI.Physics.Closure.NSTriadKNCriticalConeRelativeCovarianceTargetRound284Exact where

------------------------------------------------------------------------
-- ROUND284 / SHARP DIRECT PHYSICAL TARGET AFTER THE ROUND281 NO-GO
--
-- Forward decomposition from R234--R236:
--
--   deep FL: 3 l <= 2 m                  -> E*D-payable region
--   deep HH: 5 j <= 4 m                  -> null-gain E*D-payable region
--   critical cone:
--       FL shoulder  2 m < 3 l
--       HH shoulder  4 m < 5 j
--       comparable interactions.
--
-- R214 proves that constant-width CC localization alone cannot control same-
-- output Gram debt.  Thus the novel physical theorem belongs only to the
-- signed critical cone and must exploit convolution/phase/helicity structure.
--
-- Backward from R220/R283, it is sufficient for that core to satisfy a strict
-- relative covariance estimate
--
--   D_core <= theta * Q_core + C_core E D,      theta < 1,
--
-- while the deep regions are paid absolutely by E*D.  This is weaker than an
-- independently integrable absolute majorant for every coherent contribution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record CriticalConeRelativeCovariancePayment : Set where
  constructor critical-cone-relative-covariance-payment
  field
    energyDissipation : ℚ

    deepFarLowMass deepHHMass : ℚ
    coreCompanionMass coreGramDebt : ℚ

    deepFarLowCoefficient deepHHCoefficient coreEDCoefficient theta : ℚ

    energyDissipationNN : 0ℚ ≤ energyDissipation
    thetaNN : 0ℚ ≤ theta
    thetaStrictlyBelowOne : theta < 1

    deepFarLowPayment :
      deepFarLowMass ≤ deepFarLowCoefficient * energyDissipation

    deepHHPayment :
      deepHHMass ≤ deepHHCoefficient * energyDissipation

    criticalCoreRelativeCovariance :
      coreGramDebt
      ≤ theta * coreCompanionMass + coreEDCoefficient * energyDissipation

open CriticalConeRelativeCovariancePayment public

paidDeepMass : CriticalConeRelativeCovariancePayment → ℚ
paidDeepMass P = deepFarLowMass P + deepHHMass P

paidDeepCoefficient : CriticalConeRelativeCovariancePayment → ℚ
paidDeepCoefficient P = deepFarLowCoefficient P + deepHHCoefficient P

paidDeepRegionsCombine :
  (P : CriticalConeRelativeCovariancePayment) →
  paidDeepMass P ≤ paidDeepCoefficient P * energyDissipation P
paidDeepRegionsCombine P =
  let
    summed :
      deepFarLowMass P + deepHHMass P
      ≤ deepFarLowCoefficient P * energyDissipation P
        + deepHHCoefficient P * energyDissipation P
    summed = ℚP.+-mono-≤ (deepFarLowPayment P) (deepHHPayment P)

    endpoint :
      deepFarLowCoefficient P * energyDissipation P
        + deepHHCoefficient P * energyDissipation P
      ≡ paidDeepCoefficient P * energyDissipation P
    endpoint = solve
      (deepFarLowCoefficient P ∷ deepHHCoefficient P
        ∷ energyDissipation P ∷ [])
  in
  subst (λ upper → paidDeepMass P ≤ upper) endpoint summed

round284DeepFarLowDelegatedToRound234Region : Bool
round284DeepFarLowDelegatedToRound234Region = true

round284DeepHHDelegatedToRound235NullRegion : Bool
round284DeepHHDelegatedToRound235NullRegion = true

round284NovelRegionIsParabolicCriticalCone : Bool
round284NovelRegionIsParabolicCriticalCone = true

round284ComparableLocalizationAloneSufficient : Bool
round284ComparableLocalizationAloneSufficient = false

round284StrictRelativeCriticalConeCovarianceIsBackwardTarget : Bool
round284StrictRelativeCriticalConeCovarianceIsBackwardTarget = true

round284PhysicalCriticalConeRelativeCovarianceClosed : Bool
round284PhysicalCriticalConeRelativeCovarianceClosed = false

round284PackageAClosed : Bool
round284PackageAClosed = false

round284ClayPromotion : Bool
round284ClayPromotion = false

round284ComparableLocalizationAloneSufficientIsFalse :
  round284ComparableLocalizationAloneSufficient ≡ false
round284ComparableLocalizationAloneSufficientIsFalse = refl

round284PhysicalCriticalConeRelativeCovarianceClosedIsFalse :
  round284PhysicalCriticalConeRelativeCovarianceClosed ≡ false
round284PhysicalCriticalConeRelativeCovarianceClosedIsFalse = refl
