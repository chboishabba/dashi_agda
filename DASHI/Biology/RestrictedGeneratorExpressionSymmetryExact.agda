module DASHI.Biology.RestrictedGeneratorExpressionSymmetryExact where

------------------------------------------------------------------------
-- REPOSITORY-ORIGINAL FINITE FORMALISM
--
-- Formalize the "only 1", "only 2", "only 3" and mixed 1/2/3 variants at
-- the level of primitive generators and construction trees.  The evaluated
-- value is kept distinct from the syntax and construction history.  A
-- multi-digit surface numeral is therefore neither automatically forbidden
-- nor automatically admitted as a primitive.
--
-- No external theorem is imported and no DOI is assigned to this module.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_; _*_)

data ExpressionTree : Set where
  leaf : ExpressionTree
  add : ExpressionTree → ExpressionTree → ExpressionTree
  multiply : ExpressionTree → ExpressionTree → ExpressionTree

evaluateAt : Nat → ExpressionTree → Nat
evaluateAt atom leaf = atom
evaluateAt atom (add left right) =
  evaluateAt atom left + evaluateAt atom right
evaluateAt atom (multiply left right) =
  evaluateAt atom left * evaluateAt atom right

oneSector : ExpressionTree → Nat
oneSector = evaluateAt 1

twoSector : ExpressionTree → Nat
twoSector = evaluateAt 2

threeSector : ExpressionTree → Nat
threeSector = evaluateAt 3

sharedSquareSkeleton : ExpressionTree
sharedSquareSkeleton = multiply leaf leaf

sharedSquareAtOne : oneSector sharedSquareSkeleton ≡ 1
sharedSquareAtOne = refl

sharedSquareAtTwo : twoSector sharedSquareSkeleton ≡ 4
sharedSquareAtTwo = refl

sharedSquareAtThree : threeSector sharedSquareSkeleton ≡ 9
sharedSquareAtThree = refl

data Digit123 : Set where
  digit1 : Digit123
  digit2 : Digit123
  digit3 : Digit123

digitValue : Digit123 → Nat
digitValue digit1 = 1
digitValue digit2 = 2
digitValue digit3 = 3

data MixedExpression : Set where
  mixedLeaf : Digit123 → MixedExpression
  mixedAdd : MixedExpression → MixedExpression → MixedExpression
  mixedMultiply : MixedExpression → MixedExpression → MixedExpression

mixedEvaluate : MixedExpression → Nat
mixedEvaluate (mixedLeaf digit) = digitValue digit
mixedEvaluate (mixedAdd left right) =
  mixedEvaluate left + mixedEvaluate right
mixedEvaluate (mixedMultiply left right) =
  mixedEvaluate left * mixedEvaluate right

cyclicDigit : Digit123 → Digit123
cyclicDigit digit1 = digit2
cyclicDigit digit2 = digit3
cyclicDigit digit3 = digit1

cyclicSyntaxAction : MixedExpression → MixedExpression
cyclicSyntaxAction (mixedLeaf digit) = mixedLeaf (cyclicDigit digit)
cyclicSyntaxAction (mixedAdd left right) =
  mixedAdd (cyclicSyntaxAction left) (cyclicSyntaxAction right)
cyclicSyntaxAction (mixedMultiply left right) =
  mixedMultiply (cyclicSyntaxAction left) (cyclicSyntaxAction right)

cyclicDigitThirdPower :
  ∀ digit → cyclicDigit (cyclicDigit (cyclicDigit digit)) ≡ digit
cyclicDigitThirdPower digit1 = refl
cyclicDigitThirdPower digit2 = refl
cyclicDigitThirdPower digit3 = refl

record ExpressionPresentation : Set where
  constructor expressionPresentation
  field
    surfaceCost : Nat
    treeCost : Nat
    constructionTraceCost : Nat
    evaluatedValue : Nat

record RestrictedExpressionBoundary : Set where
  constructor restrictedExpressionBoundary
  field
    sameValueImpliesSameConstruction : Set
    sameValueDoesNotImplySameConstruction :
      sameValueImpliesSameConstruction → Set

    syntaxPermutationPreservesEveryEvaluation : Set
    syntaxPermutationDoesNotPreserveEveryEvaluation :
      syntaxPermutationPreservesEveryEvaluation → Set

canonicalRestrictedExpressionBoundary : RestrictedExpressionBoundary
canonicalRestrictedExpressionBoundary =
  restrictedExpressionBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
