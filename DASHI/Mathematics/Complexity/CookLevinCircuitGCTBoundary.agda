module DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Stephen A. Cook,
-- "The complexity of theorem-proving procedures".
-- DOI: 10.1145/800157.805047.
--
-- Ketan D. Mulmuley and Milind Sohoni,
-- "Geometric Complexity Theory I: An Approach to the P vs. NP and Related
-- Problems", SIAM Journal on Computing 31 (2001), 496--526.
-- DOI: 10.1137/S009753970038715X.
--
-- DASHI CONTRIBUTION
--
-- Supply a concrete Boolean-formula evaluator with an exact excluded-middle
-- tautology, then type the Cook--Levin simulation, circuit-family and GCT
-- obstruction boundaries.  A group invariant with unequal values is proved to
-- separate witnessed orbits by reusing the exact Klein orbit theorem.
--
-- No Cook--Levin tableau construction, SAT NP-completeness proof, super-
-- polynomial circuit lower bound, orbit-closure equation or VP/VNP separation
-- is imported by citation.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Symmetry.KleinGroupActionInvariantExact as K

data BooleanFormula : Set where
  variable : Nat → BooleanFormula
  constant : Bool → BooleanFormula
  negate : BooleanFormula → BooleanFormula
  conjunction disjunction : BooleanFormula → BooleanFormula → BooleanFormula

notBool : Bool → Bool
notBool true = false
notBool false = true

andBool : Bool → Bool → Bool
andBool true right = right
andBool false right = false

orBool : Bool → Bool → Bool
orBool true right = true
orBool false right = right

Assignment : Set
Assignment = Nat → Bool

evaluate : BooleanFormula → Assignment → Bool
evaluate (variable index) assignment = assignment index
evaluate (constant value) assignment = value
evaluate (negate formula) assignment = notBool (evaluate formula assignment)
evaluate (conjunction left right) assignment =
  andBool (evaluate left assignment) (evaluate right assignment)
evaluate (disjunction left right) assignment =
  orBool (evaluate left assignment) (evaluate right assignment)

excludedMiddleFormula : BooleanFormula
excludedMiddleFormula =
  disjunction (variable zero) (negate (variable zero))

excludedMiddleFormulaIsTautology : ∀ assignment →
  evaluate excludedMiddleFormula assignment ≡ true
excludedMiddleFormulaIsTautology assignment with assignment zero
... | true = refl
... | false = refl

record Satisfiable (formula : BooleanFormula) : Set where
  constructor satisfyingAssignment
  field
    assignment : Assignment
    evaluatesTrue : evaluate formula assignment ≡ true

excludedMiddleFormulaIsSatisfiable : Satisfiable excludedMiddleFormula
excludedMiddleFormulaIsSatisfiable =
  satisfyingAssignment (λ index → false) refl

record CookLevinSimulation
    {Word : Set}
    (cost : PR.PolynomialCostModel Word) : Setω where
  field
    sourceLanguage : PR.Language Word
    sourceInNP : PR.InNP cost sourceLanguage
    encodeAsFormula : Word → BooleanFormula
    encodingPolynomialTime : Set
    tableauSizePolynomial : Set
    acceptingComputationIffSatisfiable : ∀ word →
      PR.Iff
        (PR.accepts sourceLanguage word)
        (Satisfiable (encodeAsFormula word))

record BooleanCircuitFamily : Set₁ where
  field
    Input : Set
    Circuit : Set
    evaluateCircuit : Circuit → Input → Bool
    circuitForSize : Nat → Circuit
    circuitSize : Circuit → Nat
    inputLength : Input → Nat
    polynomialSizeBound : Set
    computesLanguage : Input → Set
    circuitCorrect : Set

record CircuitLowerBound (family : BooleanCircuitFamily) : Set₁ where
  field
    hardInputFamily : Nat → BooleanCircuitFamily.Input family
    lowerBound : Nat → Nat
    everyCorrectCircuitLarge : Set
    lowerBoundSuperPolynomial : Set

invariantInequalitySeparatesWitnessedOrbits :
  ∀ action observable →
  K.Invariant action observable →
  ∀ {left right} →
  (observable right ≡ observable left → ⊥) →
  K.SameOrbit action left right → ⊥
invariantInequalitySeparatesWitnessedOrbits
    action observable invariant valuesDiffer sameOrbit =
  valuesDiffer
    (K.invariantOnOrbit action observable invariant sameOrbit)

record GeometricComplexityObstruction : Set₁ where
  field
    action : K.GroupAction
    easyPoint hardPoint : K.X action
    invariantPolynomial : K.X action → ℚ
    invariantUnderAction : K.Invariant action invariantPolynomial
    valuesDiffer :
      invariantPolynomial hardPoint ≡ invariantPolynomial easyPoint → ⊥

open GeometricComplexityObstruction public

gctObstructionSeparatesWitnessedOrbits :
  ∀ obstruction →
  K.SameOrbit (action obstruction)
    (easyPoint obstruction) (hardPoint obstruction) → ⊥
gctObstructionSeparatesWitnessedOrbits obstruction =
  invariantInequalitySeparatesWitnessedOrbits
    (action obstruction)
    (invariantPolynomial obstruction)
    (invariantUnderAction obstruction)
    (valuesDiffer obstruction)

record OrbitClosureGCTBoundary : Set₁ where
  field
    obstruction : GeometricComplexityObstruction
    OrbitClosureMembership :
      K.X (action obstruction) → K.X (action obstruction) → Set
    witnessedOrbitImpliesClosureMembership : Set
    invariantExtendsContinuouslyToClosure : Set
    closureSeparation : Set
    representationMultiplicityObstruction : Set
    occurrenceObstructionSufficient : Set
    multiplicityObstructionSufficient : Set

data ComplexityProblem : Set where
  classicalPVersusNP : ComplexityProblem
  algebraicVPVersusVNP : ComplexityProblem

classicalAndAlgebraicProblemsAreDistinct :
  classicalPVersusNP ≡ algebraicVPVersusVNP → ⊥
classicalAndAlgebraicProblemsAreDistinct ()
