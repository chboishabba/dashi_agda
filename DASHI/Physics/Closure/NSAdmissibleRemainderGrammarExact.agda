module DASHI.Physics.Closure.NSAdmissibleRemainderGrammarExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. Thomas Beale; Tosio Kato; Andrew Majda,
-- "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations", Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01212349.
--
-- James Serrin,
-- "On the Interior Regularity of Weak Solutions of the Navier--Stokes
-- Equations", Archive for Rational Mechanics and Analysis 9 (1962),
-- 187--195. DOI: 10.1007/BF00253344.
--
-- DASHI CONTRIBUTION
--
-- Make the anti-circularity condition structural.  An admissible owner
-- remainder can contain only initial-data constants, integrals already known
-- to be finite, lower-order controlled terms, absorbed dissipation, and finite
-- sums of these.  There is deliberately no constructor for the target
-- critical supremum, an uncontrolled BKM integral, or an uncontrolled Serrin
-- norm.  Consequently every consumer eliminates the grammar using only the
-- four permitted handlers.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_)

data AdmissibleRemainder : Set where
  initialDataConstant : ℚ → AdmissibleRemainder
  knownTimeIntegral : ℚ → AdmissibleRemainder
  lowerOrderControlled : ℚ → AdmissibleRemainder
  absorbedDissipation : ℚ → AdmissibleRemainder
  _⊕_ : AdmissibleRemainder → AdmissibleRemainder → AdmissibleRemainder

infixr 6 _⊕_

data ForbiddenCircularDependency : Set where
  targetCriticalSupremum : ForbiddenCircularDependency
  uncontrolledBKMIntegral : ForbiddenCircularDependency
  uncontrolledSerrinNorm : ForbiddenCircularDependency

evaluateRemainder : AdmissibleRemainder → ℚ
evaluateRemainder (initialDataConstant value) = value
evaluateRemainder (knownTimeIntegral value) = value
evaluateRemainder (lowerOrderControlled value) = value
evaluateRemainder (absorbedDissipation value) = value
evaluateRemainder (left ⊕ right) =
  evaluateRemainder left + evaluateRemainder right

foldAdmissibleRemainder :
  ∀ {A : Set} →
  (initialHandler knownIntegralHandler lowerOrderHandler
    dissipationHandler : ℚ → A) →
  (combine : A → A → A) →
  AdmissibleRemainder → A
foldAdmissibleRemainder initialHandler knownIntegralHandler
    lowerOrderHandler dissipationHandler combine
    (initialDataConstant value) = initialHandler value
foldAdmissibleRemainder initialHandler knownIntegralHandler
    lowerOrderHandler dissipationHandler combine
    (knownTimeIntegral value) = knownIntegralHandler value
foldAdmissibleRemainder initialHandler knownIntegralHandler
    lowerOrderHandler dissipationHandler combine
    (lowerOrderControlled value) = lowerOrderHandler value
foldAdmissibleRemainder initialHandler knownIntegralHandler
    lowerOrderHandler dissipationHandler combine
    (absorbedDissipation value) = dissipationHandler value
foldAdmissibleRemainder initialHandler knownIntegralHandler
    lowerOrderHandler dissipationHandler combine (left ⊕ right) =
  combine
    (foldAdmissibleRemainder initialHandler knownIntegralHandler
      lowerOrderHandler dissipationHandler combine left)
    (foldAdmissibleRemainder initialHandler knownIntegralHandler
      lowerOrderHandler dissipationHandler combine right)

admissibleRemainderEvaluationIsCanonical :
  ∀ remainder →
  foldAdmissibleRemainder
    initialDataConstantValue knownTimeIntegralValue
    lowerOrderControlledValue absorbedDissipationValue
    _+_ remainder
  ≡ evaluateRemainder remainder
admissibleRemainderEvaluationIsCanonical
    (initialDataConstant value) = Agda.Builtin.Equality.refl
admissibleRemainderEvaluationIsCanonical
    (knownTimeIntegral value) = Agda.Builtin.Equality.refl
admissibleRemainderEvaluationIsCanonical
    (lowerOrderControlled value) = Agda.Builtin.Equality.refl
admissibleRemainderEvaluationIsCanonical
    (absorbedDissipation value) = Agda.Builtin.Equality.refl
admissibleRemainderEvaluationIsCanonical (left ⊕ right)
  rewrite admissibleRemainderEvaluationIsCanonical left
        | admissibleRemainderEvaluationIsCanonical right =
  Agda.Builtin.Equality.refl
  where
  initialDataConstantValue : ℚ → ℚ
  initialDataConstantValue value = value
  knownTimeIntegralValue : ℚ → ℚ
  knownTimeIntegralValue value = value
  lowerOrderControlledValue : ℚ → ℚ
  lowerOrderControlledValue value = value
  absorbedDissipationValue : ℚ → ℚ
  absorbedDissipationValue value = value
