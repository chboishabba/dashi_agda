module DASHI.Physics.Closure.NSTriadKNSignedIntegratedGramConsumerRound293Exact where

------------------------------------------------------------------------
-- ROUND293 / BIDI CORRECTION: INTEGRATE THE SIGNED GRAM DEBT BEFORE MAJORIZING
--
-- R220 gives pointwise
--
--   Q(t) <= 36 E(t)D(t) + D_Gram(t).
--
-- R222 introduced a sufficient pointwise nonnegative majorant R_coh with
-- D_Gram <= R_coh and bounded integral.  That is stronger than the actual
-- downstream requirement when the forward producer is a temporal flux.
--
-- If integration is monotone and additive, integrate R220 first:
--
--   integral Q
--     <= integral(36 ED) + integral D_Gram.
--
-- Thus it is enough to bound the SIGNED integral of D_Gram from above.  A
-- flux/telescope identity can use endpoint cancellation without replacing its
-- derivative by an absolute value or positive part.
--
-- The routine scalar step converting a G2 bound on integral(ED) into the
-- scaled bound on integral(36 ED) is deliberately left with the energy
-- producer.  This consumer asks for exactly the two integrated contributions
-- it uses and nothing more.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

thirtySix : ℚ
thirtySix = 36

record SignedIntegratedGramPayment
    {ℓC ℓT : Level}
    (Cutoff : Set ℓC) (Time : Set ℓT) : Set (ℓC ⊔ ℓT) where
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
      ≤ thirtySix * energyDissipation N t + gramDebt N t

    scaledEnergyIntegralUpperBound : Time → ℚ
    signedGramIntegralUpperBound : Time → ℚ

    integratedScaledEnergyBound :
      (N : Cutoff) → (T : Time) →
      integrateTo
        (λ cutoff time → thirtySix * energyDissipation cutoff time)
        N T
      ≤ scaledEnergyIntegralUpperBound T

    integratedSignedGramDebtBound :
      (N : Cutoff) → (T : Time) →
      integrateTo gramDebt N T
      ≤ signedGramIntegralUpperBound T

open SignedIntegratedGramPayment public

combinedIntegratedBound :
  ∀ {ℓC ℓT} {Cutoff : Set ℓC} {Time : Set ℓT} →
  SignedIntegratedGramPayment Cutoff Time → Time → ℚ
combinedIntegratedBound P T =
  scaledEnergyIntegralUpperBound P T + signedGramIntegralUpperBound P T

signedIntegratedGramClosesCompanionBudget :
  ∀ {ℓC ℓT} {Cutoff : Set ℓC} {Time : Set ℓT}
    (P : SignedIntegratedGramPayment Cutoff Time)
    (N : Cutoff) (T : Time) →
  integrateTo P (companionMass P) N T
  ≤ combinedIntegratedBound P T
signedIntegratedGramClosesCompanionBudget P N T =
  let
    first :
      integrateTo P (companionMass P) N T
      ≤ integrateTo P
          (λ cutoff time →
            thirtySix * energyDissipation P cutoff time
            + gramDebt P cutoff time) N T
    first = integrationMonotone P
      (companionMass P)
      (λ cutoff time →
        thirtySix * energyDissipation P cutoff time + gramDebt P cutoff time)
      (pointwiseCompanionLedger P) N T

    split :
      integrateTo P
        (λ cutoff time →
          thirtySix * energyDissipation P cutoff time + gramDebt P cutoff time)
        N T
      ≡
      integrateTo P
        (λ cutoff time → thirtySix * energyDissipation P cutoff time) N T
      + integrateTo P (gramDebt P) N T
    split = integrationAdditive P
      (λ cutoff time → thirtySix * energyDissipation P cutoff time)
      (gramDebt P) N T

    middle :
      integrateTo P (companionMass P) N T
      ≤
      integrateTo P
        (λ cutoff time → thirtySix * energyDissipation P cutoff time) N T
      + integrateTo P (gramDebt P) N T
    middle = subst
      (λ upper → integrateTo P (companionMass P) N T ≤ upper)
      split first

    paid = ℚP.+-mono-≤
      (integratedScaledEnergyBound P N T)
      (integratedSignedGramDebtBound P N T)
  in
  ℚP.≤-trans middle paid

round293R222PointwiseMajorantStillSufficient : Bool
round293R222PointwiseMajorantStillSufficient = true

round293PointwiseNonnegativeGramMajorantRequired : Bool
round293PointwiseNonnegativeGramMajorantRequired = false

round293SignedIntegratedGramUpperBoundIsEnough : Bool
round293SignedIntegratedGramUpperBoundIsEnough = true

round293NaturalConsumerForWeightedFlux : Bool
round293NaturalConsumerForWeightedFlux = true

round293PhysicalSignedIntegratedGramBudgetClosed : Bool
round293PhysicalSignedIntegratedGramBudgetClosed = false

round293PackageAClosed : Bool
round293PackageAClosed = false

round293ClayPromotion : Bool
round293ClayPromotion = false

round293SignedIntegratedGramUpperBoundIsEnoughIsTrue :
  round293SignedIntegratedGramUpperBoundIsEnough ≡ true
round293SignedIntegratedGramUpperBoundIsEnoughIsTrue = refl
