module DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceLiteralHodgeReopeningCompilerExact where

------------------------------------------------------------------------
-- PROJECTIVE-SPACE REOPENING ON THE LITERAL Clay CYCLE CARRIER
--
-- This is the universe-correct port of
-- ProjectiveSpaceHodgeReopeningCompilerExact.
--
-- It consumes LiteralRationalCycleClassMap, so the representative it returns
-- is literally RationalAlgebraicCycle variety p, not the older abstract
-- CycleClassMap.Cycle carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge
import DASHI.Mathematics.AlgebraicGeometry.HodgeLiteralCycleClassMapBridgeExact as Literal

record ProjectiveSpaceLiteralHyperplanePowerSpanning
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (cycleMap : Literal.LiteralRationalCycleClassMap hodge)
    (codimension : Nat) : Set₁ where
  field
    hyperplanePowerCycle :
      Hodge.RationalAlgebraicCycle
        variety codimension

    coefficientOf :
      Hodge.RationalHodgeClass hodge codimension →
      ℚ

    everyClassIsHyperplanePower :
      (hodgeClass :
        Hodge.RationalHodgeClass hodge codimension) →
      Hodge.hodgeClassValue hodgeClass
      ≡
      Hodge.scale
        (Hodge.HodgePiece hodge codimension codimension)
        (coefficientOf hodgeClass)
        (Literal.literalHodgeCycleClass
          cycleMap
          codimension
          hyperplanePowerCycle)

open ProjectiveSpaceLiteralHyperplanePowerSpanning public

projectiveSpaceLiteralCycleRepresentative :
  ∀ {variety comparison hodge cycleMap codimension} →
  ProjectiveSpaceLiteralHyperplanePowerSpanning
    {variety = variety}
    {comparison = comparison}
    {hodge = hodge}
    cycleMap codimension →
  Hodge.RationalHodgeClass hodge codimension →
  Hodge.RationalAlgebraicCycle
    variety codimension
projectiveSpaceLiteralCycleRepresentative
    {codimension = codimension}
    spanning
    hodgeClass =
  Literal.literalScaleCycle
    _
    codimension
    (coefficientOf spanning hodgeClass)
    (hyperplanePowerCycle spanning)

projectiveSpaceLiteralCycleRepresentsClass :
  ∀ {variety comparison hodge cycleMap codimension}
    (spanning :
      ProjectiveSpaceLiteralHyperplanePowerSpanning
        {variety = variety}
        {comparison = comparison}
        {hodge = hodge}
        cycleMap codimension)
    (hodgeClass :
      Hodge.RationalHodgeClass hodge codimension) →
  Literal.literalHodgeCycleClass
      cycleMap
      codimension
      (projectiveSpaceLiteralCycleRepresentative
        spanning
        hodgeClass)
  ≡
  Hodge.hodgeClassValue hodgeClass
projectiveSpaceLiteralCycleRepresentsClass
    {hodge = hodge}
    {cycleMap = cycleMap}
    {codimension = codimension}
    spanning
    hodgeClass =
  trans
    (Literal.homogeneousClass
      cycleMap
      codimension
      (coefficientOf spanning hodgeClass)
      (hyperplanePowerCycle spanning))
    (sym
      (everyClassIsHyperplanePower
        spanning
        hodgeClass))

------------------------------------------------------------------------
-- Local literal Hodge producer.
------------------------------------------------------------------------

record ProjectiveSpaceLiteralHodgeProducer
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (cycleMap : Literal.LiteralRationalCycleClassMap hodge)
    (codimension : Nat) : Set₁ where
  field
    representative :
      Hodge.RationalHodgeClass hodge codimension →
      Hodge.RationalAlgebraicCycle
        variety codimension

    represents :
      (hodgeClass :
        Hodge.RationalHodgeClass hodge codimension) →
      Literal.literalHodgeCycleClass
          cycleMap
          codimension
          (representative hodgeClass)
      ≡
      Hodge.hodgeClassValue hodgeClass

open ProjectiveSpaceLiteralHodgeProducer public

projectiveSpaceLiteralSpanningGivesProducer :
  ∀ {variety comparison hodge cycleMap codimension} →
  ProjectiveSpaceLiteralHyperplanePowerSpanning
    {variety = variety}
    {comparison = comparison}
    {hodge = hodge}
    cycleMap codimension →
  ProjectiveSpaceLiteralHodgeProducer
    cycleMap codimension
projectiveSpaceLiteralSpanningGivesProducer spanning =
  record
    { representative =
        projectiveSpaceLiteralCycleRepresentative spanning
    ; represents =
        projectiveSpaceLiteralCycleRepresentsClass spanning
    }

------------------------------------------------------------------------
-- FRONTIER
--
-- The projective/hyperplane reopening compiler now works on the exact literal
-- cycle carrier used by the frozen Clay owner.
--
-- Still application-supplied:
--   the geometric theorem that a particular primitive component is a rational
--   multiple of the chosen hyperplane-power cycle.
--
-- This result can now feed the knownCycle side of
-- HodgePrimitiveAlgebraicResidualDecompositionExact without a carrier change.
------------------------------------------------------------------------
