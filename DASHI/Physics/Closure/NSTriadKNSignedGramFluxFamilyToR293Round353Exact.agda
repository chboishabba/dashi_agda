module DASHI.Physics.Closure.NSTriadKNSignedGramFluxFamilyToR293Round353Exact where

------------------------------------------------------------------------
-- ROUND353 / BIDI: FAMILY OF R303 FLUX PAYMENTS -> THE OLD R293 CONSUMER
--
-- R303 pays one signed Gram integral at a particular cutoff/time endpoint.
-- R293 intentionally asks for a time-indexed upper bound uniform in cutoff.
-- The missing adapter is therefore not another positivity theorem.  It is:
--
--   * one R303 payment for every (N,T);
--   * a same-object equality identifying that payment's signed integral with
--     R293's `integrateTo gramDebt N T`;
--   * one cutoff-uniform upper envelope for the R303 paid bounds.
--
-- With those receipts the old signed-integrated consumer is inhabited directly.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNSignedGramFluxPaymentRound303Exact as R303
import DASHI.Physics.Closure.NSTriadKNSignedIntegratedGramConsumerRound293Exact as R293

record SignedGramFluxFamilyInputs
    {ℓC ℓT : Level}
    (Cutoff : Set ℓC)
    (Time : Set ℓT) : Set (ℓC ⊔ ℓT) where
  field
    companionMass : Cutoff → Time → ℚ
    energyDissipation : Cutoff → Time → ℚ
    gramDebt : Cutoff → Time → ℚ

    integrateTo : (Cutoff → Time → ℚ) → Cutoff → Time → ℚ

    integrationMonotone :
      (left right : Cutoff → Time → ℚ) →
      ((N : Cutoff) → (t : Time) → left N t ≤ right N t) →
      (N : Cutoff) → (T : Time) →
      integrateTo left N T ≤ integrateTo right N T

    integrationAdditive :
      (left right : Cutoff → Time → ℚ) →
      (N : Cutoff) → (T : Time) →
      integrateTo (λ cutoff time → left cutoff time + right cutoff time) N T
      ≡ integrateTo left N T + integrateTo right N T

    pointwiseCompanionLedger :
      (N : Cutoff) → (t : Time) →
      companionMass N t
      ≤ R293.thirtySix * energyDissipation N t + gramDebt N t

    scaledEnergyIntegralUpperBound : Time → ℚ
    integratedScaledEnergyBound :
      (N : Cutoff) → (T : Time) →
      integrateTo
        (λ cutoff time → R293.thirtySix * energyDissipation cutoff time)
        N T
      ≤ scaledEnergyIntegralUpperBound T

    gramFluxPayment : Cutoff → Time → R303.SignedGramFluxPayment

    gramFluxIsSameIntegratedDebt :
      (N : Cutoff) → (T : Time) →
      R303.signedGramIntegral (gramFluxPayment N T)
      ≡ integrateTo gramDebt N T

    signedGramIntegralUpperBound : Time → ℚ

    gramFluxPaidUniformlyInCutoff :
      (N : Cutoff) → (T : Time) →
      R303.signedGramUpperBound (gramFluxPayment N T)
      ≤ signedGramIntegralUpperBound T

open SignedGramFluxFamilyInputs public

signedGramFluxFamilyToR293 :
  ∀ {ℓC ℓT : Level}
    {Cutoff : Set ℓC}
    {Time : Set ℓT} →
  SignedGramFluxFamilyInputs Cutoff Time →
  R293.SignedIntegratedGramPayment Cutoff Time
signedGramFluxFamilyToR293 I = record
  { companionMass = companionMass I
  ; energyDissipation = energyDissipation I
  ; gramDebt = gramDebt I
  ; integrateTo = integrateTo I
  ; integrationMonotone = integrationMonotone I
  ; integrationAdditive = integrationAdditive I
  ; pointwiseCompanionLedger = pointwiseCompanionLedger I
  ; scaledEnergyIntegralUpperBound = scaledEnergyIntegralUpperBound I
  ; signedGramIntegralUpperBound = signedGramIntegralUpperBound I
  ; integratedScaledEnergyBound = integratedScaledEnergyBound I
  ; integratedSignedGramDebtBound = integratedGramBound
  }
  where
  integratedGramBound :
    ∀ N T →
    integrateTo I (gramDebt I) N T
    ≤ signedGramIntegralUpperBound I T
  integratedGramBound N T =
    subst
      (λ left → left ≤ signedGramIntegralUpperBound I T)
      (gramFluxIsSameIntegratedDebt I N T)
      (ℚP.≤-trans
        (R303.signedGramIntegralPaid (gramFluxPayment I N T))
        (gramFluxPaidUniformlyInCutoff I N T))

round353R303PaymentsRemainSigned : Bool
round353R303PaymentsRemainSigned = true

round353SameObjectIntegratedDebtReceiptExplicit : Bool
round353SameObjectIntegratedDebtReceiptExplicit = true

round353CutoffUniformizationExplicit : Bool
round353CutoffUniformizationExplicit = true

round353PointwisePositiveGramMajorantIntroduced : Bool
round353PointwisePositiveGramMajorantIntroduced = false

round353R293AdapterClosed : Bool
round353R293AdapterClosed = true

round353PackageAClosed : Bool
round353PackageAClosed = false

round353ClayPromotion : Bool
round353ClayPromotion = false

round353R293AdapterClosedIsTrue : round353R293AdapterClosed ≡ true
round353R293AdapterClosedIsTrue = refl

round353PointwisePositiveGramMajorantIntroducedIsFalse :
  round353PointwisePositiveGramMajorantIntroduced ≡ false
round353PointwisePositiveGramMajorantIntroducedIsFalse = refl

round353PackageAClosedIsFalse : round353PackageAClosed ≡ false
round353PackageAClosedIsFalse = refl

round353ClayPromotionIsFalse : round353ClayPromotion ≡ false
round353ClayPromotionIsFalse = refl
