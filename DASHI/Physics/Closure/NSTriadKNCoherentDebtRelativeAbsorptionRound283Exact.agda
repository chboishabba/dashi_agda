module DASHI.Physics.Closure.NSTriadKNCoherentDebtRelativeAbsorptionRound283Exact where

------------------------------------------------------------------------
-- ROUND283 / WEAKER BIDI CONSUMER: RELATIVE COHERENT-DEBT ABSORPTION
--
-- Round220 gives
--
--   Q <= 36 E D + D_Gram,
--
-- where Q is the complete quadratic companion mass and D_Gram is the signed
-- coherent Gram debt.  Round222 asked for an independently time-integrable
-- upper majorant of D_Gram.  That is sufficient but stronger than necessary.
--
-- A weaker pointwise theorem is enough:
--
--   D_Gram <= theta * Q + C * E D,       0 <= theta < 1.
--
-- Then
--
--   Q <= (36 + C) E D + theta Q,
--
-- and strict relative absorption yields a pure E*D companion bound.  This is
-- a better backward target for the parabolic critical cone because coherent
-- same-output covariance may remain comparable to Q; it only has to consume
-- strictly less than the whole output mass after the ED-paid part is removed.
--
-- The finite rational algebra below avoids pretending that the physical
-- theta/C estimate is already known.  A producer supplies the relative debt
-- inequality and an explicit absorption multiplier K satisfying
--
--   1 + theta*K <= K.
--
-- This division-free certificate is equivalent to K >= 1/(1-theta) when
-- theta<1, but requires no inverse/positivity machinery here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Agda.Builtin.List using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (subst)

thirtySix : ℚ
thirtySix = 36

record RelativeCoherentDebtPayment : Set where
  constructor relative-coherent-debt-payment
  field
    companionMass energyDissipation coherentDebt : ℚ
    theta extraED absorptionMultiplier : ℚ

    companionMassNN : 0ℚ ≤ companionMass
    energyDissipationNN : 0ℚ ≤ energyDissipation
    thetaNN : 0ℚ ≤ theta
    extraEDNN : 0ℚ ≤ extraED
    absorptionMultiplierNN : 0ℚ ≤ absorptionMultiplier

    baseCompanionLedger :
      companionMass ≤ thirtySix * energyDissipation + coherentDebt

    relativeDebtBound :
      coherentDebt ≤ theta * companionMass + extraED * energyDissipation

    -- Division-free strict absorption certificate.
    absorptionCertificate :
      1ℚ + theta * absorptionMultiplier ≤ absorptionMultiplier

open RelativeCoherentDebtPayment public

baseCoefficient : RelativeCoherentDebtPayment → ℚ
baseCoefficient P = thirtySix + extraED P

absorbedCoefficient : RelativeCoherentDebtPayment → ℚ
absorbedCoefficient P = absorptionMultiplier P * baseCoefficient P

relativeDebtGivesSelfReferentialBound :
  (P : RelativeCoherentDebtPayment) →
  companionMass P
  ≤ baseCoefficient P * energyDissipation P
      + theta P * companionMass P
relativeDebtGivesSelfReferentialBound P =
  let
    step :
      thirtySix * energyDissipation P + coherentDebt P
      ≤ thirtySix * energyDissipation P
          + (theta P * companionMass P + extraED P * energyDissipation P)
    step = ℚP.+-monoʳ-≤
      (thirtySix * energyDissipation P)
      (relativeDebtBound P)

    rearrange :
      thirtySix * energyDissipation P
        + (theta P * companionMass P + extraED P * energyDissipation P)
      ≡ baseCoefficient P * energyDissipation P
          + theta P * companionMass P
    rearrange = solve
      (energyDissipation P ∷ theta P ∷ companionMass P ∷ extraED P ∷ [])
  in
  ℚP.≤-trans (baseCompanionLedger P)
    (subst
      (λ upper →
        thirtySix * energyDissipation P + coherentDebt P ≤ upper)
      rearrange step)

-- The final absorption step is exposed as the weakest ordered-field receipt.
-- It is standard scalar algebra once `absorptionCertificate` is available;
-- keeping it explicit avoids overclaiming an untested stdlib cancellation path.
record RelativeAbsorptionClosure (P : RelativeCoherentDebtPayment) : Set where
  field
    absorbedBound :
      companionMass P
      ≤ absorbedCoefficient P * energyDissipation P

open RelativeAbsorptionClosure public

relativeAbsorptionClosesCompanion :
  (P : RelativeCoherentDebtPayment) →
  RelativeAbsorptionClosure P →
  companionMass P ≤ absorbedCoefficient P * energyDissipation P
relativeAbsorptionClosesCompanion P A = absorbedBound A

round283RelativeDebtTargetWeakerThanIndependentIntegratedMajorant : Bool
round283RelativeDebtTargetWeakerThanIndependentIntegratedMajorant = true

round283AllowsCriticalCoreCovarianceProportionalToCompanion : Bool
round283AllowsCriticalCoreCovarianceProportionalToCompanion = true

round283RequiresStrictAbsorbableCoefficient : Bool
round283RequiresStrictAbsorbableCoefficient = true

round283PhysicalRelativeCoherentDebtEstimateClosed : Bool
round283PhysicalRelativeCoherentDebtEstimateClosed = false

round283OrderedFieldAbsorptionCompilerClosed : Bool
round283OrderedFieldAbsorptionCompilerClosed = false

round283PackageAClosed : Bool
round283PackageAClosed = false

round283ClayPromotion : Bool
round283ClayPromotion = false

round283PhysicalRelativeCoherentDebtEstimateClosedIsFalse :
  round283PhysicalRelativeCoherentDebtEstimateClosed ≡ false
round283PhysicalRelativeCoherentDebtEstimateClosedIsFalse = refl
