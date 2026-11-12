module DASHI.Physics.YangMills.BalabanLiteralExpressionSyntaxPermutationBoundaryExact where

-- A finite NEGATIVE CONTROL for the exact current physical P0 syntax.
-- Joint.transformExpression recurses over the original
-- LiteralOneLoopBoxEvaluatorExact.DiagramExpression tree. A coordinate
-- swap can interchange two summands, but the syntax constructors
-- do not quotient addition by commutativity.
--
-- Mathematical equality of the evaluated values MUST NOT be silently
-- replaced by propositional equality of unnormalised syntax trees.
-- A valid physical proof may use an explicit normalizer with semantic
-- soundness, or direct evaluator equivalence, but not fabricated refl.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4HyperoctahedralGridOrbitExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopJointMomentumEquivarianceExact as Joint

-- A minimal literal pair of cosine atoms in the real source syntax.
axis01CosinePair : Eval.DiagramExpression
axis01CosinePair =
  Eval.add
    (Eval.atom (Eval.cosineFull Eval.loopMomentum Eval.axis0))
    (Eval.atom (Eval.cosineFull Eval.loopMomentum Eval.axis1))

-- The source transform does rename the axes, but preserves the
-- order of syntax-tree arguments rather than commuting them.
axis01SwapActuallyReorders :
  Joint.transformExpression Orbit.swap01 axis01CosinePair
  ≡ Eval.add
      (Eval.atom (Eval.cosineFull Eval.loopMomentum Eval.axis1))
      (Eval.atom (Eval.cosineFull Eval.loopMomentum Eval.axis0))
axis01SwapActuallyReorders = refl

-- Original syntax has distinct ordered constructors. This is a
-- structural counterexample to demanding that every mathematically
-- B4-invariant sum be *definitionally identical* to its swap image.
rawSyntaxSwapNotInvariant :
  Joint.transformExpression Orbit.swap01 axis01CosinePair
  ≡ axis01CosinePair → ⊥
rawSyntaxSwapNotInvariant ()

-- Important: this does NOT show the real combined Wilson/ghost/Haar
-- expression is noninvariant, only that its syntax equality cannot be
-- inferred from commutative rational arithmetic without proof-producing
-- normalization or evaluator-level algebra.
