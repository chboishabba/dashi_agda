module DASHI.Physics.Closure.NSPeriodicLerayBiotSavartNormReduction where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact Pythagorean reduction of the two official operator estimates.
--
-- Leray:
--   ||v||² = ||Πv||² + ||(I-Π)v||².
--
-- Biot-Savart:
--   ||ω||² = ||curl^{-1}ω||_{Ḣ¹}² + ||longitudinal ω||².
--
-- Nonnegativity of the complementary square proves contractivity.  For a
-- divergence-free vorticity the longitudinal term is zero, so the second
-- identity specializes to an isometry.  No cutoff-dependent constant enters
-- this reduction.
------------------------------------------------------------------------

summandBelowSum :
  (A : AbsorptionArithmetic) →
  ∀ a remainder →
  _≤_ A (zero A) remainder →
  _≤_ A a (_+_ A a remainder)
summandBelowSum A a remainder remainderNonnegative =
  subst
    (λ left → _≤_ A left (_+_ A a remainder))
    (addZeroLeft A a)
    (subst
      (λ right → _≤_ A (_+_ A (zero A) a) right)
      (addCommutative A remainder a)
      (additionMonotoneRight A remainderNonnegative))

record PythagoreanOperatorBoundInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    inputNormSquared outputNormSquared complementNormSquared : Scalar A

    complementNonnegative :
      _≤_ A (zero A) complementNormSquared

    pythagoreanSplit :
      inputNormSquared ≡
      _+_ A outputNormSquared complementNormSquared

open PythagoreanOperatorBoundInputs public

pythagoreanOperatorIsContractive :
  ∀ {A : AbsorptionArithmetic} →
  (P : PythagoreanOperatorBoundInputs A) →
  _≤_ A (outputNormSquared P) (inputNormSquared P)
pythagoreanOperatorIsContractive {A = A} P =
  subst
    (λ upper → _≤_ A (outputNormSquared P) upper)
    (sym (pythagoreanSplit P))
    (summandBelowSum A
      (outputNormSquared P)
      (complementNormSquared P)
      (complementNonnegative P))

record PeriodicLerayBiotSavartNormInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    lerayInputNormSquared lerayOutputNormSquared
      lerayLongitudinalNormSquared : Scalar A

    vorticityNormSquared biotSavartHomogeneousH1Squared
      vorticityLongitudinalNormSquared : Scalar A

    lerayLongitudinalNonnegative :
      _≤_ A (zero A) lerayLongitudinalNormSquared

    vorticityLongitudinalNonnegative :
      _≤_ A (zero A) vorticityLongitudinalNormSquared

    lerayPythagoreanIdentity :
      lerayInputNormSquared ≡
      _+_ A lerayOutputNormSquared lerayLongitudinalNormSquared

    biotSavartCrossProductIdentity :
      vorticityNormSquared ≡
      _+_ A
        biotSavartHomogeneousH1Squared
        vorticityLongitudinalNormSquared

open PeriodicLerayBiotSavartNormInputs public

lerayPythagoreanInputs :
  ∀ {A : AbsorptionArithmetic} →
  PeriodicLerayBiotSavartNormInputs A →
  PythagoreanOperatorBoundInputs A
lerayPythagoreanInputs L = record
  { inputNormSquared = lerayInputNormSquared L
  ; outputNormSquared = lerayOutputNormSquared L
  ; complementNormSquared = lerayLongitudinalNormSquared L
  ; complementNonnegative = lerayLongitudinalNonnegative L
  ; pythagoreanSplit = lerayPythagoreanIdentity L
  }

biotSavartPythagoreanInputs :
  ∀ {A : AbsorptionArithmetic} →
  PeriodicLerayBiotSavartNormInputs A →
  PythagoreanOperatorBoundInputs A
biotSavartPythagoreanInputs L = record
  { inputNormSquared = vorticityNormSquared L
  ; outputNormSquared = biotSavartHomogeneousH1Squared L
  ; complementNormSquared = vorticityLongitudinalNormSquared L
  ; complementNonnegative = vorticityLongitudinalNonnegative L
  ; pythagoreanSplit = biotSavartCrossProductIdentity L
  }

periodicLerayProjectionContractive :
  ∀ {A : AbsorptionArithmetic} →
  (L : PeriodicLerayBiotSavartNormInputs A) →
  _≤_ A (lerayOutputNormSquared L) (lerayInputNormSquared L)
periodicLerayProjectionContractive L =
  pythagoreanOperatorIsContractive (lerayPythagoreanInputs L)

periodicBiotSavartHomogeneousH1Bounded :
  ∀ {A : AbsorptionArithmetic} →
  (L : PeriodicLerayBiotSavartNormInputs A) →
  _≤_ A
    (biotSavartHomogeneousH1Squared L)
    (vorticityNormSquared L)
periodicBiotSavartHomogeneousH1Bounded L =
  pythagoreanOperatorIsContractive (biotSavartPythagoreanInputs L)

record TransverseBiotSavartInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    vorticityNormSquared biotSavartHomogeneousH1Squared : Scalar A

    transverseCrossProductIsometry :
      vorticityNormSquared ≡ biotSavartHomogeneousH1Squared

open TransverseBiotSavartInputs public

transverseBiotSavartHomogeneousH1Isometry :
  ∀ {A : AbsorptionArithmetic} →
  (T : TransverseBiotSavartInputs A) →
  biotSavartHomogeneousH1Squared T ≡ vorticityNormSquared T
transverseBiotSavartHomogeneousH1Isometry T =
  sym (transverseCrossProductIsometry T)

------------------------------------------------------------------------
-- Status: both norm inequalities are reduced to exact Pythagorean identities.
-- The concrete real-carrier leaf is now the modewise Euclidean identity and
-- its finite/cutoff-uniform sum, not a free operator-bound assumption.
------------------------------------------------------------------------

lerayBiotSavartNormReductionLevel : ProofLevel
lerayBiotSavartNormReductionLevel = machineChecked
