module DASHI.Physics.Closure.NSTriadKNSignedIntegratedGramConsumerRound293Exact where

------------------------------------------------------------------------
-- ROUND293 / BIDI CORRECTION: INTEGRATE THE SIGNED GRAM DEBT BEFORE MAJORIZING
--
-- R220 gives pointwise
--
--   Q(t) <= 36 E(t)D(t) + D_Gram(t).
--
-- R222 introduced a sufficient pointwise nonnegative majorant R_coh with
-- D_Gram <= R_coh and bounded integral.  That is well suited to absolute
-- estimates, but it is stronger than the actual downstream requirement when
-- the forward producer is a temporal flux/telescope.
--
-- If integration is monotone and additive, one may instead integrate R220
-- directly:
--
--   integral Q
--     <= 36 integral(ED) + integral D_Gram.
--
-- Thus Package-A only needs a cutoff-uniform UPPER bound on the SIGNED
-- integral of D_Gram.  A representation
--
--   D_Gram = -dF/dt + R
--
-- can then use endpoint cancellation without replacing dF/dt by its positive
-- part or absolute value.
--
-- This file freezes that weaker backward consumer.  R222 remains a valid
-- sufficient route; Round293 is the natural consumer for the R290 weighted
-- Gram flux.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

thirtySix : ℚ
thirtySix = 36

record SignedIntegratedGramPayment {ℓC ℓT : _}
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

    integrationScaleThirtySix :
      (value : Cutoff → Time → ℚ) →
      (N : Cutoff) → (T : Time) →
      integrateTo (λ cutoff time → thirtySix * value cutoff time) N T
      ≡ thirtySix * integrateTo value N T

    pointwiseCompanionLedger :
      (N : Cutoff) → (t : Time) →
      companionMass N t
      ≤ thirtySix * energyDissipation N t + gramDebt N t

    energyDissipationIntegralBound : Time → ℚ
    gramDebtSignedIntegralUpperBound : Time → ℚ

    integratedEnergyDissipationBound :
      (N : Cutoff) → (T : Time) →
      integrateTo energyDissipation N T
      ≤ energyDissipationIntegralBound T

    integratedSignedGramDebtBound :
      (N : Cutoff) → (T : Time) →
      integrateTo gramDebt N T
      ≤ gramDebtSignedIntegralUpperBound T

open SignedIntegratedGramPayment public

combinedIntegratedBound :
  ∀ {ℓC ℓT} {Cutoff : Set ℓC} {Time : Set ℓT} →
  SignedIntegratedGramPayment Cutoff Time → Time → ℚ
combinedIntegratedBound P T =
  thirtySix * energyDissipationIntegralBound P T
  + gramDebtSignedIntegralUpperBound P T

signedIntegratedGramClosesCompanionBudget :
  ∀ {ℓC ℓT} {Cutoff : Set ℓC} {Time : Set ℓT}
    (P : SignedIntegratedGramPayment Cutoff Time)
    (N : Cutoff) (T : Time) →
  integrateTo P (companionMass P) N T
  ≤ combinedIntegratedBound P T
signedIntegratedGramClosesCompanionBudget P N T =
  let
    pointwise = pointwiseCompanionLedger P

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
      pointwise N T

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

    scale :
      integrateTo P
        (λ cutoff time → thirtySix * energyDissipation P cutoff time) N T
      ≡ thirtySix * integrateTo P (energyDissipation P) N T
    scale = integrationScaleThirtySix P (energyDissipation P) N T

    middle :
      integrateTo P (companionMass P) N T
      ≤ thirtySix * integrateTo P (energyDissipation P) N T
          + integrateTo P (gramDebt P) N T
    middle = subst
      (λ upper → integrateTo P (companionMass P) N T ≤ upper)
      (trans split (congLeft scale)) first
      where
      congLeft :
        ∀ {a b c : ℚ} → a ≡ b → a + c ≡ b + c
      congLeft refl = refl

    paid = ℚP.+-mono-≤
      (scaleThirtySixMonotone
        (integratedEnergyDissipationBound P N T))
      (integratedSignedGramDebtBound P N T)
  in
  ℚP.≤-trans middle paid
  where
  scaleThirtySixMonotone : ∀ {a b : ℚ} → a ≤ b → thirtySix * a ≤ thirtySix * b
  scaleThirtySixMonotone ab =
    ℚP.*-monoˡ-≤-nonNeg thirtySix ab

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
