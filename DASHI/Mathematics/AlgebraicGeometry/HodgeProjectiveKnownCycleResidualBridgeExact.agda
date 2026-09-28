module DASHI.Mathematics.AlgebraicGeometry.HodgeProjectiveKnownCycleResidualBridgeExact where

------------------------------------------------------------------------
-- PROJECTIVE LITERAL CYCLE -> EXACT SINGULAR KNOWN-CYCLE RECEIPT
--
-- The literal projective reopening compiler proves equality in the (p,p)
-- Hodge piece.  Primitive residual reconstruction needs the exact singular
-- cycle-class equality on RationalHodgeClassExact.
--
-- The frozen SingularDeRhamComparison is an actual equivalence, so this owner
-- transports the projective representative back to singular cohomology.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge
import DASHI.Mathematics.AlgebraicGeometry.HodgeRationalClassIntersectionExact as Exact
import DASHI.Mathematics.AlgebraicGeometry.HodgeAlgebraicCycleClayCoreExact as Clay
import DASHI.Mathematics.AlgebraicGeometry.HodgeLiteralCycleClassMapBridgeExact as Literal
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceLiteralHodgeReopeningCompilerExact as Projective
import DASHI.Mathematics.AlgebraicGeometry.HodgePrimitiveAlgebraicResidualDecompositionExact as Residual
import DASHI.Mathematics.AlgebraicGeometry.HodgePrimitiveZeroResidualExact as Zero

------------------------------------------------------------------------
-- Exact singular receipt for a literal projective representative.
------------------------------------------------------------------------

projectiveLiteralRepresentativeHasExactSingularClass :
  ∀ {variety comparison hodge cycleMap codimension}
    (spanning :
      Projective.ProjectiveSpaceLiteralHyperplanePowerSpanning
        {variety = variety}
        {comparison = comparison}
        {hodge = hodge}
        cycleMap codimension)
    (exact :
      Exact.RationalHodgeClassExact
        hodge codimension) →
  let hodgeClass =
        Hodge.rationalHodgeClass
          (Exact.hodgeComponent exact)
      cycle =
        Projective.projectiveSpaceLiteralCycleRepresentative
          spanning
          hodgeClass
      background =
        Literal.cycleClassBackground cycleMap
  in
  Clay.singularCycleClass
      background
      codimension
      cycle
  ≡
  Exact.singularClass exact
projectiveLiteralRepresentativeHasExactSingularClass
    {comparison = comparison}
    {cycleMap = cycleMap}
    {codimension = codimension}
    spanning
    exact =
  trans
    (sym
      (Hodge.comparisonLeftInverse
        comparison
        (codimension + codimension)
        (Clay.singularCycleClass
          background
          codimension
          cycle)))
    (trans
      (cong
        (Hodge.deRhamToSingular
          comparison
          (codimension + codimension))
        deRhamClassesEqual)
      (Hodge.comparisonLeftInverse
        comparison
        (codimension + codimension)
        (Exact.singularClass exact)))
  where
    hodgeClass :
      Hodge.RationalHodgeClass hodge codimension
    hodgeClass =
      Hodge.rationalHodgeClass
        (Exact.hodgeComponent exact)

    cycle :
      Hodge.RationalAlgebraicCycle
        _ codimension
    cycle =
      Projective.projectiveSpaceLiteralCycleRepresentative
        spanning
        hodgeClass

    background :
      Clay.RationalAlgebraicCycleClassBackground hodge
    background =
      Literal.cycleClassBackground cycleMap

    cycleHodgeExact :
      Literal.literalHodgeCycleClass
          cycleMap codimension cycle
      ≡
      Exact.hodgeComponent exact
    cycleHodgeExact =
      Projective.projectiveSpaceLiteralCycleRepresentsClass
        spanning
        hodgeClass

    deRhamClassesEqual :
      Hodge.singularToDeRham
          comparison
          (codimension + codimension)
          (Clay.singularCycleClass
            background codimension cycle)
      ≡
      Hodge.singularToDeRham
          comparison
          (codimension + codimension)
          (Exact.singularClass exact)
    deRhamClassesEqual =
      trans
        (Clay.comparisonAgrees
          background
          codimension
          cycle)
        (trans
          (cong
            (Hodge.injectPiece hodge
              codimension codimension)
            cycleHodgeExact)
          (sym
            (Exact.rationalClassLandsInHodgePiece
              exact)))

------------------------------------------------------------------------
-- Literal addition background for primitive residual reconstruction.
------------------------------------------------------------------------

literalMapGivesPrimitiveCycleAdditionBackground :
  ∀ {variety comparison hodge}
    {cycleMap :
      Literal.LiteralRationalCycleClassMap hodge}
    (singularAdditivity :
      Literal.LiteralSingularCycleClassAdditivity
        cycleMap)
    (codimension : Nat) →
  Residual.PrimitiveCycleAdditionBackground
    (Literal.cycleClassBackground cycleMap)
    codimension
literalMapGivesPrimitiveCycleAdditionBackground
    singularAdditivity
    codimension =
  record
    { Residual.addCycle =
        Literal.addRationalAlgebraicCycle
    ; Residual.addCycleClass =
        Literal.additiveSingularClass
          singularAdditivity
          codimension
    }

------------------------------------------------------------------------
-- Known-cycle producer on exact rational classes.
------------------------------------------------------------------------

projectiveKnownCycle :
  ∀ {variety comparison hodge cycleMap codimension}
    (spanning :
      Projective.ProjectiveSpaceLiteralHyperplanePowerSpanning
        {variety = variety}
        {comparison = comparison}
        {hodge = hodge}
        cycleMap codimension)
    (exact :
      Exact.RationalHodgeClassExact
        hodge codimension) →
  Σ
    (Hodge.RationalAlgebraicCycle
      variety codimension)
    (λ cycle →
      Clay.singularCycleClass
          (Literal.cycleClassBackground cycleMap)
          codimension
          cycle
      ≡
      Exact.singularClass exact)
projectiveKnownCycle spanning exact =
  Projective.projectiveSpaceLiteralCycleRepresentative
    spanning
    (Hodge.rationalHodgeClass
      (Exact.hodgeComponent exact))
  ,
  projectiveLiteralRepresentativeHasExactSingularClass
    spanning
    exact

------------------------------------------------------------------------
-- Projective known-cycle -> literal zero residual.
------------------------------------------------------------------------

projectiveKnownCycleGivesZeroResidualSplit :
  ∀ {variety comparison hodge cycleMap codimension}
    {isPrimitive :
      Primitive.PrimitivePredicate hodge}
    (spanning :
      Projective.ProjectiveSpaceLiteralHyperplanePowerSpanning
        {variety = variety}
        {comparison = comparison}
        {hodge = hodge}
        cycleMap codimension)
    (zeroBackground :
      Zero.PrimitiveZeroResidualBackground
        isPrimitive codimension)
    (primitive :
      Primitive.PrimitiveRationalHodgeClassExact
        isPrimitive codimension) →
  Residual.PrimitiveAlgebraicResidualSplit
    {cycleBackground =
      Literal.cycleClassBackground cycleMap}
    (Zero.ZeroSingularPrimitiveResidualFamily isPrimitive)
    primitive
projectiveKnownCycleGivesZeroResidualSplit
    spanning
    zeroBackground
    primitive =
  Zero.knownCycleExactGivesZeroResidualSplit
    zeroBackground
    primitive
    (Projective.projectiveSpaceLiteralCycleRepresentative
      spanning
      (Hodge.rationalHodgeClass
        (Exact.hodgeComponent
          (Primitive.exactClass primitive))))
    (projectiveLiteralRepresentativeHasExactSingularClass
      spanning
      (Primitive.exactClass primitive))

------------------------------------------------------------------------
-- FRONTIER
--
-- Projective/hyperplane-generated exact rational classes now produce literal
-- knownCycle receipts on the SAME singular class carrier required by the
-- primitive residual split.
--
-- Remaining hard step:
--   for an arbitrary primitive alpha, choose such a known exact component beta
--   and an exact primitive residual rho with
--
--       cl(knownCycle beta) + [rho] = [alpha],
--
--   while proving rho lies in a genuinely strict residual family.
------------------------------------------------------------------------
