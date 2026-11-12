module DASHI.Physics.YangMills.BalabanLiteralIntervalCommutativeSumExact where

-- Exact conditional SEMANTIC rewriting for the ACTUAL literal recursive
-- diagram evaluator, not raw DiagramExpression syntax rewriting.
-- The existing RationalIntervalArithmetic provides operations but no
-- algebraic laws. These are made explicit as backend obligations.
-- In particular interval endpoints with proof-containing ordered fields
-- cannot be equated merely because rational endpoints coincide.
--
-- No claim the selected literal Wilson/ghost/Haar expressions are
-- generator invariant: those source-specific premises remain independent.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval

record IntervalAdditionLaws
  (arithmetic : Eval.RationalIntervalArithmetic) : Set₁ where
  field
    commutative : (x y : Eval.RationalInterval) →
      Eval.addInterval arithmetic x y ≡ Eval.addInterval arithmetic y x
    associative : (x y z : Eval.RationalInterval) →
      Eval.addInterval arithmetic (Eval.addInterval arithmetic x y) z
      ≡ Eval.addInterval arithmetic x (Eval.addInterval arithmetic y z)
open IntervalAdditionLaws public

record IntervalMultiplicationLaws
  (arithmetic : Eval.RationalIntervalArithmetic) : Set₁ where
  field
    commutative : (x y : Eval.RationalInterval) →
      Eval.multiplyInterval arithmetic x y ≡
      Eval.multiplyInterval arithmetic y x
    associative : (x y z : Eval.RationalInterval) →
      Eval.multiplyInterval arithmetic
        (Eval.multiplyInterval arithmetic x y) z
      ≡ Eval.multiplyInterval arithmetic x
        (Eval.multiplyInterval arithmetic y z)
open IntervalMultiplicationLaws public

-- The following lemmas instantiate the ACTUAL source expression
-- constructors against the ACTUAL recursive evaluator.
addSyntaxCommutesSemantically :
  (arithmetic : Eval.RationalIntervalArithmetic)
  (environment : Eval.BoxTrigEnvironment) →
  IntervalAdditionLaws arithmetic →
  (left right : Eval.DiagramExpression) →
  Eval.evaluateExpression arithmetic environment (Eval.add left right)
  ≡ Eval.evaluateExpression arithmetic environment (Eval.add right left)
addSyntaxCommutesSemantically arithmetic environment laws left right =
  commutative laws
    (Eval.evaluateExpression arithmetic environment left)
    (Eval.evaluateExpression arithmetic environment right)

addSyntaxAssociatesSemantically :
  (arithmetic : Eval.RationalIntervalArithmetic)
  (environment : Eval.BoxTrigEnvironment) →
  IntervalAdditionLaws arithmetic →
  (a b c : Eval.DiagramExpression) →
  Eval.evaluateExpression arithmetic environment
    (Eval.add (Eval.add a b) c)
  ≡ Eval.evaluateExpression arithmetic environment
    (Eval.add a (Eval.add b c))
addSyntaxAssociatesSemantically arithmetic environment laws a b c =
  associative laws
    (Eval.evaluateExpression arithmetic environment a)
    (Eval.evaluateExpression arithmetic environment b)
    (Eval.evaluateExpression arithmetic environment c)

multiplySyntaxCommutesSemantically :
  (arithmetic : Eval.RationalIntervalArithmetic)
  (environment : Eval.BoxTrigEnvironment) →
  IntervalMultiplicationLaws arithmetic →
  (left right : Eval.DiagramExpression) →
  Eval.evaluateExpression arithmetic environment (Eval.multiply left right)
  ≡ Eval.evaluateExpression arithmetic environment (Eval.multiply right left)
multiplySyntaxCommutesSemantically arithmetic environment laws left right =
  commutative laws
    (Eval.evaluateExpression arithmetic environment left)
    (Eval.evaluateExpression arithmetic environment right)

multiplySyntaxAssociatesSemantically :
  (arithmetic : Eval.RationalIntervalArithmetic)
  (environment : Eval.BoxTrigEnvironment) →
  IntervalMultiplicationLaws arithmetic →
  (a b c : Eval.DiagramExpression) →
  Eval.evaluateExpression arithmetic environment
    (Eval.multiply (Eval.multiply a b) c)
  ≡ Eval.evaluateExpression arithmetic environment
    (Eval.multiply a (Eval.multiply b c))
multiplySyntaxAssociatesSemantically arithmetic environment laws a b c =
  associative laws
    (Eval.evaluateExpression arithmetic environment a)
    (Eval.evaluateExpression arithmetic environment b)
    (Eval.evaluateExpression arithmetic environment c)

-- Commutativity alone is insufficient for a swap within a RIGHT-NESTED
-- list sum; the constructive proof uses associativity twice.
swapTwoInsideSum :
  (arithmetic : Eval.RationalIntervalArithmetic) →
  IntervalAdditionLaws arithmetic →
  (x y tail : Eval.RationalInterval) →
  Eval.addInterval arithmetic x (Eval.addInterval arithmetic y tail)
    ≡ Eval.addInterval arithmetic y (Eval.addInterval arithmetic x tail)
swapTwoInsideSum arithmetic laws x y tail =
  trans
    (sym (associative laws x y tail))
    (trans
      (cong (λ v → Eval.addInterval arithmetic v tail)
            (commutative laws x y))
      (associative laws y x tail))

-- Sum evaluation is a fold through the existing literal AST, with
-- the true recursive arithmetic and constant-zero leaf unchanged.
sumEvalCons :
  (arithmetic : Eval.RationalIntervalArithmetic)
  (environment : Eval.BoxTrigEnvironment)
  (x : Eval.DiagramExpression)
  (xs : List Eval.DiagramExpression) →
  Eval.evaluateExpression arithmetic environment
    (Eval.sumExpressions (x ∷ xs))
  ≡ Eval.addInterval arithmetic
      (Eval.evaluateExpression arithmetic environment x)
      (Eval.evaluateExpression arithmetic environment
        (Eval.sumExpressions xs))
sumEvalCons arithmetic environment x xs = refl

-- Any head-adjacent swap in the *actual* source sumExpressions syntax
-- preserves evaluation, despite two unequal raw syntax trees.
headSwapPreservesOriginalSumEvaluation :
  (arithmetic : Eval.RationalIntervalArithmetic)
  (environment : Eval.BoxTrigEnvironment) →
  IntervalAdditionLaws arithmetic →
  (x y : Eval.DiagramExpression)
  (tail : List Eval.DiagramExpression) →
  Eval.evaluateExpression arithmetic environment
    (Eval.sumExpressions (x ∷ y ∷ tail))
  ≡ Eval.evaluateExpression arithmetic environment
    (Eval.sumExpressions (y ∷ x ∷ tail))
headSwapPreservesOriginalSumEvaluation arithmetic environment laws
  x y tail =
  swapTwoInsideSum arithmetic laws
    (Eval.evaluateExpression arithmetic environment x)
    (Eval.evaluateExpression arithmetic environment y)
    (Eval.evaluateExpression arithmetic environment
      (Eval.sumExpressions tail))

-- Four explicit original diagram terms in source-preserved order.
-- We prove each of the 3 adjacent-term permutations (S4 generators)
-- without claiming the physical B4 swaps merely permute these terms.
diagramSumSwap01 :
  (arithmetic : Eval.RationalIntervalArithmetic)
  (environment : Eval.BoxTrigEnvironment) →
  IntervalAdditionLaws arithmetic →
  (a b c d : Eval.DiagramExpression) →
  Eval.evaluateExpression arithmetic environment
    (Eval.sumExpressions (a ∷ b ∷ c ∷ d ∷ []))
  ≡ Eval.evaluateExpression arithmetic environment
    (Eval.sumExpressions (b ∷ a ∷ c ∷ d ∷ []))
diagramSumSwap01 arithmetic environment laws a b c d =
  headSwapPreservesOriginalSumEvaluation arithmetic environment laws
    a b (c ∷ d ∷ [])

diagramSumSwap12 :
  (arithmetic : Eval.RationalIntervalArithmetic)
  (environment : Eval.BoxTrigEnvironment) →
  IntervalAdditionLaws arithmetic →
  (a b c d : Eval.DiagramExpression) →
  Eval.evaluateExpression arithmetic environment
    (Eval.sumExpressions (a ∷ b ∷ c ∷ d ∷ []))
  ≡ Eval.evaluateExpression arithmetic environment
    (Eval.sumExpressions (a ∷ c ∷ b ∷ d ∷ []))
diagramSumSwap12 arithmetic environment laws a b c d =
  cong (Eval.addInterval arithmetic
          (Eval.evaluateExpression arithmetic environment a))
    (headSwapPreservesOriginalSumEvaluation arithmetic environment
      laws b c (d ∷ []))

diagramSumSwap23 :
  (arithmetic : Eval.RationalIntervalArithmetic)
  (environment : Eval.BoxTrigEnvironment) →
  IntervalAdditionLaws arithmetic →
  (a b c d : Eval.DiagramExpression) →
  Eval.evaluateExpression arithmetic environment
    (Eval.sumExpressions (a ∷ b ∷ c ∷ d ∷ []))
  ≡ Eval.evaluateExpression arithmetic environment
    (Eval.sumExpressions (a ∷ b ∷ d ∷ c ∷ []))
diagramSumSwap23 arithmetic environment laws a b c d =
  cong (Eval.addInterval arithmetic
          (Eval.evaluateExpression arithmetic environment a))
    (cong (Eval.addInterval arithmetic
            (Eval.evaluateExpression arithmetic environment b))
      (headSwapPreservesOriginalSumEvaluation arithmetic environment
        laws c d []))

-- The exact EXISTING four-diagram source is covered, with no toy terms.
originalCombinedKernelSwapsBubbleTadpole :
  (arithmetic : Eval.RationalIntervalArithmetic)
  (environment : Eval.BoxTrigEnvironment) →
  IntervalAdditionLaws arithmetic →
  (source : Eval.LiteralDiagramExpressions) →
  Eval.evaluateExpression arithmetic environment
    (Eval.combinedKernelExpression source)
  ≡ Eval.evaluateExpression arithmetic environment
    (Eval.sumExpressions
      (Eval.gaugeTadpole source ∷ Eval.gaugeBubble source ∷
       Eval.ghostLoop source ∷ Eval.haarLoop source ∷ []))
originalCombinedKernelSwapsBubbleTadpole arithmetic environment
  laws source =
  diagramSumSwap01 arithmetic environment laws
    (Eval.gaugeBubble source) (Eval.gaugeTadpole source)
    (Eval.ghostLoop source) (Eval.haarLoop source)

-- LIMITS:
-- * This is a source-specific diagram-SUM permutation result, NOT
--   full seven-generator momentum-covariance of the literal scalar.
-- * The concrete backend must prove BOTH laws. The abstract
--   RationalIntervalArithmetic record by itself does NOT contain them.
-- * Ordered/proof-containing interval records may require endpoint
--   equivalence or construction with canonical order proofs.
-- * No associativity is assumed for arbitrary rounded/opaque enclosures.
