module DASHI.Physics.Closure.NSTriadKNGramOperatorBoundConsumerRound471Exact where

------------------------------------------------------------------------
-- ROUND471 / WEAKEST FIXED-OUTPUT GRAM CONSUMER
--
-- Lean sibling provenance (2026-09-07):
--   RequestProject/NavierStokes/OperatorSchurBlockCancellation.lean
--   RequestProject/NavierStokes/TransverseFrameSplit.lean
--
-- The Lean development proves that the physical spacetime consumer uses only
-- a truncation-uniform l2->l2 bound for the fixed-output Gram quadratic form.
-- Absolute row-summability, block Schur and operator-level Schur hypotheses are
-- sufficient PRODUCERS, not the consumer contract itself.
--
-- This Agda owner therefore records the weakest theorem shape directly and
-- gives the exact algebraic compiler from two scalar polarization bounds to the
-- full Gram bound.  No physical producer is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

------------------------------------------------------------------------
-- Primitive consumer: one quadratic form, one l2 mass, one uniform constant.
------------------------------------------------------------------------

record GramOperatorBound
    (Coeff : Set)
    (gramQuadratic coeffMass : Coeff → ℚ)
    (A : ℚ) : Set where
  constructor gram-operator-bound
  field
    quadraticBound :
      (coeff : Coeff) → gramQuadratic coeff ≤ A * coeffMass coeff

open GramOperatorBound public

------------------------------------------------------------------------
-- Producer hierarchy.  The constructors intentionally carry only enough data
-- to compile to the primitive consumer.  They are not identified with it.
------------------------------------------------------------------------

data GramCertificateKind : Set where
  absoluteRowSchur
  blockSchur
  operatorSchurEveryInput
  directSignedGram : GramCertificateKind

record GramCertificate
    (kind : GramCertificateKind)
    (Coeff : Set)
    (gramQuadratic coeffMass : Coeff → ℚ)
    (A : ℚ) : Set where
  constructor gram-certificate
  field
    consumerBound : GramOperatorBound Coeff gramQuadratic coeffMass A

open GramCertificate public

certificateToGramOperatorBound :
  ∀ {kind Coeff gramQuadratic coeffMass A} →
  GramCertificate kind Coeff gramQuadratic coeffMass A →
  GramOperatorBound Coeff gramQuadratic coeffMass A
certificateToGramOperatorBound = consumerBound

------------------------------------------------------------------------
-- Exact two-polarization split.
--
-- If
--   Q = Q1 + Q2
--   M = M1 + M2
-- and Qi <= A Mi for each component, then Q <= A M.
------------------------------------------------------------------------

record TwoPolarizationSplit
    (Coeff : Set)
    (totalGram firstGram secondGram : Coeff → ℚ)
    (totalMass firstMass secondMass : Coeff → ℚ) : Set where
  constructor two-polarization-split
  field
    gramSplit : (coeff : Coeff) →
      totalGram coeff ≡ firstGram coeff + secondGram coeff
    massSplit : (coeff : Coeff) →
      totalMass coeff ≡ firstMass coeff + secondMass coeff

open TwoPolarizationSplit public

twoPolarizationBoundsCompile :
  ∀ {Coeff totalGram firstGram secondGram totalMass firstMass secondMass A} →
  (S : TwoPolarizationSplit
    Coeff totalGram firstGram secondGram totalMass firstMass secondMass) →
  GramOperatorBound Coeff firstGram firstMass A →
  GramOperatorBound Coeff secondGram secondMass A →
  GramOperatorBound Coeff totalGram totalMass A
twoPolarizationBoundsCompile {A = A} S first second = record
  { quadraticBound = bound
  }
  where
  bound : ∀ coeff → totalGram coeff ≤ A * totalMass coeff
  bound coeff =
    let
      summed :
        firstGram coeff + secondGram coeff
        ≤ A * firstMass coeff + A * secondMass coeff
      summed = ℚP.+-mono-≤
        (quadraticBound first coeff)
        (quadraticBound second coeff)

      endpoint :
        A * firstMass coeff + A * secondMass coeff
        ≡ A * (firstMass coeff + secondMass coeff)
      endpoint = solve
        (A ∷ firstMass coeff ∷ secondMass coeff ∷ [])

      paid :
        firstGram coeff + secondGram coeff
        ≤ A * (firstMass coeff + secondMass coeff)
      paid = subst
        ((firstGram coeff + secondGram coeff) ≤_)
        endpoint
        summed
    in
    subst
      (λ lower → lower ≤ A * totalMass coeff)
      (sym (gramSplit S coeff))
      (subst
        (λ upper → firstGram coeff + secondGram coeff ≤ A * upper)
        (sym (massSplit S coeff))
        paid)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round471GramOperatorBoundIsPreferredConsumer : Bool
round471GramOperatorBoundIsPreferredConsumer = true

round471AbsoluteSchurIsMandatory : Bool
round471AbsoluteSchurIsMandatory = false

round471BlockSchurIsMandatory : Bool
round471BlockSchurIsMandatory = false

round471TwoPolarizationCompilerClosed : Bool
round471TwoPolarizationCompilerClosed = true

round471PhysicalOuterCellGramBoundClosed : Bool
round471PhysicalOuterCellGramBoundClosed = false

round471PackageAClosed : Bool
round471PackageAClosed = false

round471ClayPromotion : Bool
round471ClayPromotion = false

round471AbsoluteSchurIsMandatoryIsFalse :
  round471AbsoluteSchurIsMandatory ≡ false
round471AbsoluteSchurIsMandatoryIsFalse = refl

round471BlockSchurIsMandatoryIsFalse :
  round471BlockSchurIsMandatory ≡ false
round471BlockSchurIsMandatoryIsFalse = refl

round471PhysicalOuterCellGramBoundClosedIsFalse :
  round471PhysicalOuterCellGramBoundClosed ≡ false
round471PhysicalOuterCellGramBoundClosedIsFalse = refl
