module DASHI.Mathematics.Automorphic.MellinSplitFunctionalEquationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Toshitsune Miyake,
-- "Modular Forms".
-- DOI: 10.1007/3-540-29593-3.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms".
-- DOI: 10.1007/978-0-387-27226-9.
--
-- Jean-Pierre Serre,
-- "A Course in Arithmetic".
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- DASHI CONTRIBUTION
--
-- Isolate and prove the algebraic heart of the Mellin-transform functional
-- equation.  If a completed transform is split into lower and upper pieces,
-- and modular change of variables exchanges those pieces under s |-> k-s
-- with root number epsilon, then the completed transform satisfies the
-- corresponding functional equation.
--
-- Integral convergence, contour changes, Gamma factors and the derivation of
-- the two substitution identities from an actual modular form remain explicit
-- realization obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

symmetry : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
symmetry refl = refl

transitivity : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transitivity refl second = second

congruence₂ : ∀ {A B C : Set} (f : A → B → C)
  {x x' : A} {y y' : B} → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
congruence₂ f refl refl = refl

record MellinSplitData : Set₁ where
  field
    Parameter : Set
    reflectParameter : Parameter → Parameter
    reflectionInvolutive : ∀ s →
      reflectParameter (reflectParameter s) ≡ s

    epsilon : ℚ
    lowerPiece : Parameter → ℚ
    upperPiece : Parameter → ℚ

    lowerSubstitution : ∀ s →
      lowerPiece s
      ≡ epsilon * upperPiece (reflectParameter s)
    upperSubstitution : ∀ s →
      upperPiece s
      ≡ epsilon * lowerPiece (reflectParameter s)

open MellinSplitData public

completedTransform :
  (data : MellinSplitData) → Parameter data → ℚ
completedTransform data s = lowerPiece data s + upperPiece data s

mellinSplitFunctionalEquation :
  ∀ data s →
  completedTransform data s
  ≡ epsilon data * completedTransform data (reflectParameter data s)
mellinSplitFunctionalEquation data s =
  transitivity
    (congruence₂ _+_
      (lowerSubstitution data s)
      (upperSubstitution data s))
    (solve
      (epsilon data
      ∷ lowerPiece data (reflectParameter data s)
      ∷ upperPiece data (reflectParameter data s)
      ∷ []))

record ModularMellinRealizationBoundary
    (data : MellinSplitData) : Set₁ where
  field
    ModularFormCarrier : Set
    selectedForm : ModularFormCarrier
    weight : ℚ
    modularTransformationLaw : Set
    lowerPieceIsIntegralFromZeroToOne : Set
    upperPieceIsIntegralFromOneToInfinity : Set
    convergenceAtZero : Set
    convergenceAtInfinity : Set
    changeOfVariablesJustifiesLowerSubstitution : Set
    changeOfVariablesJustifiesUpperSubstitution : Set
    gammaCompletionAgreement : Set

------------------------------------------------------------------------
-- A concrete reflection-symmetric rational toy, proving the algebraic route
-- is inhabited without pretending the toy polynomial is an automorphic
-- L-function.
------------------------------------------------------------------------

oneMinus : ℚ → ℚ
oneMinus s = 1ℚ - s

symmetricPolynomial : ℚ → ℚ
symmetricPolynomial s = s * (1ℚ - s)

symmetricPolynomialReflection : ∀ s →
  symmetricPolynomial s ≡ symmetricPolynomial (oneMinus s)
symmetricPolynomialReflection s = solve (s ∷ [])

rationalReflectionInvolutive : ∀ s → oneMinus (oneMinus s) ≡ s
rationalReflectionInvolutive s = solve (s ∷ [])

symmetricToyMellinSplit : MellinSplitData
symmetricToyMellinSplit = record
  { Parameter = ℚ
  ; reflectParameter = oneMinus
  ; reflectionInvolutive = rationalReflectionInvolutive
  ; epsilon = 1ℚ
  ; lowerPiece = symmetricPolynomial
  ; upperPiece = symmetricPolynomial
  ; lowerSubstitution = λ s →
      transitivity
        (symmetricPolynomialReflection s)
        (symmetry (solve (symmetricPolynomial (oneMinus s) ∷ [])))
  ; upperSubstitution = λ s →
      transitivity
        (symmetricPolynomialReflection s)
        (symmetry (solve (symmetricPolynomial (oneMinus s) ∷ [])))
  }

symmetricToyFunctionalEquation : ∀ s →
  completedTransform symmetricToyMellinSplit s
  ≡ completedTransform symmetricToyMellinSplit (oneMinus s)
symmetricToyFunctionalEquation s =
  transitivity
    (mellinSplitFunctionalEquation symmetricToyMellinSplit s)
    (solve (completedTransform symmetricToyMellinSplit (oneMinus s) ∷ []))
