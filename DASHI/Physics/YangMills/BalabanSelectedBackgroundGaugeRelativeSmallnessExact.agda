module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeRelativeSmallnessExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Package the verified Round-42 relative perturbation estimate with its exact
-- strict margin:
--
--   theta = 31/64,
--   slack = 33/64,
--   theta + slack = 1,
--   slack > 0.
--
-- Thus the literal selected-background perturbation is strictly form-small
-- relative to the flat regularized gauge form.  This is the strongest honest
-- interpretation of the roadmap name
-- `selectedBackgroundBasedGaugePerturbationSmall` currently available.
-- It is NOT yet the exponentially weighted operator-norm estimate
-- ||G_0 E_A||_mu < 1; the latter still requires a weighted/local kernel bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _<_; Positive; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeRelativeFormExact as Relative

relativePerturbationSlack : ℚ
relativePerturbationSlack = + 33 / 64

relativePerturbationCoefficientPlusSlackExact :
  Relative.relativePerturbationCoefficient + relativePerturbationSlack ≡ 1ℚ
relativePerturbationCoefficientPlusSlackExact = ℚRing.solve []

relativePerturbationSlackPositive : 0ℚ < relativePerturbationSlack
relativePerturbationSlackPositive =
  let
    instance
      slackPositive : Positive relativePerturbationSlack
      slackPositive = ℚP.normalize-pos 33 64
  in
  ℚP.positive⁻¹ relativePerturbationSlack

relativePerturbationCoefficientBelowOne :
  Relative.relativePerturbationCoefficient < 1ℚ
relativePerturbationCoefficientBelowOne =
  let
    instance
      slackPositive : Positive relativePerturbationSlack
      slackPositive = ℚP.normalize-pos 33 64
  in
  ℚP.positiveDifferenceImpliesLess
    (substDifference relativePerturbationCoefficientPlusSlackExact)
  where
  substDifference :
    Relative.relativePerturbationCoefficient + relativePerturbationSlack ≡ 1ℚ →
    1ℚ - Relative.relativePerturbationCoefficient ≡ relativePerturbationSlack
  substDifference equality =
    let
      algebra :
        1ℚ - Relative.relativePerturbationCoefficient
        ≡ (Relative.relativePerturbationCoefficient + relativePerturbationSlack)
            - Relative.relativePerturbationCoefficient
      algebra =
        Relation.Binary.PropositionalEquality.cong
          (λ total → total - Relative.relativePerturbationCoefficient)
          (Relation.Binary.PropositionalEquality.sym equality)
    in
    Relation.Binary.PropositionalEquality.trans algebra (ℚRing.solve [])

record SelectedBackgroundRelativeFormSmall
    (background : Physical.RationalSU2Background4) : Set where
  field
    formBound : ∀ multiplier →
      Relative.GaugePerturbationRelativeFormBound background multiplier
    coefficientBelowOne :
      Relative.relativePerturbationCoefficient < 1ℚ
    exactSlack :
      Relative.relativePerturbationCoefficient + relativePerturbationSlack ≡ 1ℚ
    slackPositive : 0ℚ < relativePerturbationSlack

open SelectedBackgroundRelativeFormSmall public

selectedBackgroundBasedGaugePerturbationSmall :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  SelectedBackgroundRelativeFormSmall background
selectedBackgroundBasedGaugePerturbationSmall background radius = record
  { formBound = Relative.selectedBackgroundGaugePerturbationRelativeFormBound
      background radius
  ; coefficientBelowOne = relativePerturbationCoefficientBelowOne
  ; exactSlack = relativePerturbationCoefficientPlusSlackExact
  ; slackPositive = relativePerturbationSlackPositive
  }

selectedBackgroundRelativeFormSmallnessLevel : ProofLevel
selectedBackgroundRelativeFormSmallnessLevel = machineChecked

weightedGreenContractionStillRequiredLevel : ProofLevel
weightedGreenContractionStillRequiredLevel = conditional
