module DASHI.Physics.YangMills.BalabanClayT4LiteralScalarSyntaxContradictionExact where

-- Permanent negative control for the UNSOUND ORIGINAL source API SHAPE:
-- a single free inductive DiagramExpression cannot propositionally equal
-- both (divide numerator denominator) and (add singular regular).
--
-- The ORIGINAL LiteralScalarIntegrandExpression record was repaired in
-- BalabanClayT4LiteralOneLoopBoxEvaluatorExact to use explicitly selected
-- source-pointwise scalar semantics rather than impossible AST equality.
-- This file preserves the countertheorem without importing the old,
-- now-fixed record interface, so the repaired project can compile.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval

divideConstructorDistinctFromAdd :
  ∀ {numerator denominator singular regular} →
  Eval.divide numerator denominator ≡ Eval.add singular regular →
  ⊥
divideConstructorDistinctFromAdd ()

formerLiteralScalarSyntaxRequirementsAreInconsistent :
  ∀ {numerator denominator scalarIntegrand singular regular} →
  scalarIntegrand ≡ Eval.divide numerator denominator →
  scalarIntegrand ≡ Eval.add singular regular →
  ⊥
formerLiteralScalarSyntaxRequirementsAreInconsistent quotient split =
  divideConstructorDistinctFromAdd (trans (sym quotient) split)

-- This says nothing against the actual physical singular+regular identity.
-- That identity lives in sourcePointwiseSemantics and must be proved in
-- the selected physical Bishop/Fourier/diagrammatic model, with a truthful
-- same-source interpretation for all constructors.
