module DASHI.Physics.YangMills.BalabanClayT4RefinedWilsonSevenGeneratorExact where

-- Real seven-generator source-domain result: the *unshifted Wilson*
-- hat-momentum² rational interval from refined sine-square enclosures
-- is invariant at BOTH endpoints under all seven actual signed
-- permutations of the original 256-cell grid.
--
-- Does NOT assert the Wilson BUBBLE, FP GHOST or HAAR diagram is
-- invariant, and does not identify the external shifted-momentum
-- propagators with the unshifted one. The original physics is
-- strictly narrower than that unsupported assertion.
--
-- The equality is reduced to the already proved original source
-- Action.outerCountGeneratorInvariant, not a new permutation oracle.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _/_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4RefinedSineSquareRegularBoxesExact as Square

rankFloor : Nat → ℚ
rankFloor rank = Square.componentFloor * ((+ rank) / 1)

-- Exhaustively reduce the SAME source evaluator expression for each
-- generated Cell4. This is equality, not an order assumption.
sourceLowerIsRank :
  ∀ cell →
  Eval.lower (Square.sourceWilsonDenominatorBox cell)
    ≡ rankFloor (Geometry.outerCount cell)
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceLowerIsRank (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter) = refl

sourceUpperIsSixteen :
  ∀ cell →
  Eval.upper (Square.sourceWilsonDenominatorBox cell)
    ≡ (+ 16 / 1)
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.positiveOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveInner) = refl
sourceUpperIsSixteen (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter) = refl

-- The literal original source action preserves outer rank for flips 0-3
-- and adjacent swaps 01/12/23. The lower interval endpoint is an EXACT
-- rational function of this rank. So every generator preserves it.
sourceWilsonGeneratorLowerExact :
  ∀ g cell →
  Eval.lower (Square.sourceWilsonDenominatorBox cell)
    ≡ Eval.lower (Square.sourceWilsonDenominatorBox (Action.act g cell))
sourceWilsonGeneratorLowerExact g cell =
  trans (sourceLowerIsRank cell)
    (trans
      (cong rankFloor (sym (Action.outerCountGeneratorInvariant g cell)))
      (sym (sourceLowerIsRank (Action.act g cell))))

sourceWilsonGeneratorUpperExact :
  ∀ g cell →
  Eval.upper (Square.sourceWilsonDenominatorBox cell)
    ≡ Eval.upper (Square.sourceWilsonDenominatorBox (Action.act g cell))
sourceWilsonGeneratorUpperExact g cell =
  trans (sourceUpperIsSixteen cell)
    (sym (sourceUpperIsSixteen (Action.act g cell)))

-- These are SOURCE-WRITTEN generator certificates for the true Wilson
-- \\hat{k}² denominator box. They provide a specific genuine symmetry
-- leaf, but not the entire Wilson+ghost+Haar beta scalar source.
