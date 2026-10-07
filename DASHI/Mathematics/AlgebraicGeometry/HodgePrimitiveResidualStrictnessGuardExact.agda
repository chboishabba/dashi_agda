module DASHI.Mathematics.AlgebraicGeometry.HodgePrimitiveResidualStrictnessGuardExact where

------------------------------------------------------------------------
-- HODGE PRIMITIVE RESIDUAL STRICTNESS GUARD
--
-- The residual decomposition only shortens the primitive Clay theorem if the
-- residual family is genuinely smaller.  This file rules out the tautological
-- choice containing every primitive class.
------------------------------------------------------------------------

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge
import DASHI.Mathematics.AlgebraicGeometry.HodgePrimitiveLefschetzClayReductionExact as Primitive
import DASHI.Mathematics.AlgebraicGeometry.HodgePrimitiveAlgebraicResidualDecompositionExact as Residual

AllPrimitiveResidualFamily :
  ∀ {variety comparison hodge}
    (isPrimitive : Primitive.PrimitivePredicate hodge) →
  Residual.ResidualPrimitiveFamily isPrimitive
AllPrimitiveResidualFamily isPrimitive codimension primitive = ⊤

------------------------------------------------------------------------
-- Exact no-go: the unrestricted residual family can never carry the strictness
-- witness required by the same-object reduction.
------------------------------------------------------------------------

allPrimitiveResidualFamilyNotStrict :
  ∀ {variety comparison hodge}
    {isPrimitive : Primitive.PrimitivePredicate hodge} →
  Residual.StrictResidualPrimitiveFamily
      isPrimitive
      (AllPrimitiveResidualFamily isPrimitive) →
  ⊥
allPrimitiveResidualFamilyNotStrict strict =
  Residual.genuinelyExcluded strict tt

------------------------------------------------------------------------
-- MAX-CUT
--
-- A productive residual route must therefore construct a genuinely restricted
-- geometric family and prove BOTH:
--
--   1. every literal primitive rational Hodge class splits as
--        known algebraic cycle class + residual in that family;
--   2. every residual in that strict family has a literal algebraic lift.
--
-- Taking the residual family to be all primitive classes is now mechanically
-- rejected rather than merely discouraged in prose.
------------------------------------------------------------------------
