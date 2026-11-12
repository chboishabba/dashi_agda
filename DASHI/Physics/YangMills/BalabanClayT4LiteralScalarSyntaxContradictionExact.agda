module DASHI.Physics.YangMills.BalabanClayT4LiteralScalarSyntaxContradictionExact where

-- Exact source API obstruction (original 2026-11-12 signature):
-- LiteralScalarIntegrandExpression requires simultaneously
--
--  scalarIntegrand ≡ divide numerator denominator
--  scalarIntegrand ≡ add continuumSingular regularIntegrand
--
-- for the FREE inductive DiagramExpression grammar. These are
-- DISTINCT constructors. NO inhabitant can satisfy both equations.
-- This is why constructing the four Wilson/ghost/Haar physical
-- literal scalar simply by "filling the existing record" is impossible.
-- This proof witnesses the obstruction directly in the ORIGINAL AST.
--
-- Fix needed: replace the second propositional SYNTACTIC equality
-- with equality of SOURCE-FAITHFUL PHYSICAL SEMANTIC INTERPRETATIONS.
-- Neither equality of arbitrary intervals nor a Set=⊤ placeholder is
-- a valid replacement for true physical scalar-point equality.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval

divideConstructorDistinctFromAdd :
  ∀ {numerator denominator singular regular} →
  Eval.divide numerator denominator ≡ Eval.add singular regular →
  ⊥
divideConstructorDistinctFromAdd ()

literalScalarRecordUninhabitableBeforeSemanticRepair :
  ∀ {expressions ward} →
  Eval.LiteralScalarIntegrandExpression expressions ward →
  ⊥
literalScalarRecordUninhabitableBeforeSemanticRepair source =
  divideConstructorDistinctFromAdd
    (trans
      (sym (Eval.scalarIntegrandDefinition source))
      (Eval.singularRegularSplitExact source))

-- This theorem must be REMOVED or moved to a historical snapshot when
-- LiteralScalarIntegrandExpression is repaired to carry true semantic
-- equality instead of contradictory AST constructor equality.
