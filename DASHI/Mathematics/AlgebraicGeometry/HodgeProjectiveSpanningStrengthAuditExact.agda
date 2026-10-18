module DASHI.Mathematics.AlgebraicGeometry.HodgeProjectiveSpanningStrengthAuditExact where

------------------------------------------------------------------------
-- STRENGTH AUDIT: universal projective spanning is already a full lift.
--
-- ProjectiveSpaceLiteralHyperplanePowerSpanning provides a literal cycle for
-- EVERY rational Hodge class at its codimension. If this premise is supplied
-- uniformly, it already closes PrimitiveAlgebraicLift.
--
-- Therefore it is not a genuinely weaker geometric projection mechanism
-- on arbitrary primitive classes. The missing geometric ingredient must
-- produce a partial class/cycle decomposition from weaker source data.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ; _,_)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge
import DASHI.Mathematics.AlgebraicGeometry.HodgeLiteralCycleClassMapBridgeExact as Literal
import DASHI.Mathematics.AlgebraicGeometry.HodgePrimitiveLefschetzClayReductionExact as Primitive
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceLiteralHodgeReopeningCompilerExact as Projective
import DASHI.Mathematics.AlgebraicGeometry.HodgeProjectiveKnownCycleResidualBridgeExact as Known

projectiveSpanningAlreadyGivesPrimitiveLift :
  ∀ {variety comparison hodge}
    {cycleMap : Literal.LiteralRationalCycleClassMap hodge}
    (isPrimitive : Primitive.PrimitivePredicate hodge) →
  ((codimension : Nat) →
    Projective.ProjectiveSpaceLiteralHyperplanePowerSpanning
      cycleMap codimension) →
  Primitive.PrimitiveAlgebraicLift
    (Literal.cycleClassBackground cycleMap)
    isPrimitive
projectiveSpanningAlreadyGivesPrimitiveLift
    isPrimitive
    spanning
    codimension
    primitive =
  Known.projectiveKnownCycle
    (spanning codimension)
    (Primitive.exactClass primitive)

------------------------------------------------------------------------
-- In particular, any claimed "projection" which requires spanning on ALL
-- primitive inputs has paid the whole primitive lift in its premise.
--
-- Genuine residual reduction must instead:
--
--  * produce a known literal cycle using weaker geometry;
--  * produce an exact residual on that same singular class;
--  * prove the residual lands in a restricted useful family, on every input.
------------------------------------------------------------------------
