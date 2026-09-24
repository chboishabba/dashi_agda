module DASHI.Mathematics.AlgebraicGeometry.HodgeAlgebraicCycleClayCoreExact where

------------------------------------------------------------------------
-- HODGE CLAY CORE ON LITERAL RATIONAL ALGEBRAIC CYCLES
--
-- HodgeRationalClassIntersectionExact fixed the rationality side of the
-- conjecture.  One remaining type-level ambiguity was on the cycle side:
--
--   CycleClassMap.Cycle : Nat -> Set
--
-- was an arbitrary supplied carrier, even though the older Hodge module also
-- defined RationalAlgebraicCycle.
--
-- This owner removes that ambiguity.  The cycle-class maps below are defined
-- directly on:
--
--   RationalAlgebraicCycle variety codimension
--
-- so a Clay-core witness cannot be an unrelated abstract "Cycle".
--
-- The remaining supplied fields are established-background geometry:
-- singular and Hodge cycle-class constructions, their comparison, and the
-- linear laws they satisfy.  The ONLY conjectural field is the universal
-- algebraic representative for each exact rational Hodge class.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge
import DASHI.Mathematics.AlgebraicGeometry.HodgeRationalClassIntersectionExact as Exact

record RationalAlgebraicCycleClassBackground
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    (hodge : Hodge.HodgeDecomposition variety comparison) : Setω where
  field
    singularCycleClass :
      (codimension : Nat) →
      Hodge.RationalAlgebraicCycle variety codimension →
      Hodge.Carrier
        (Hodge.singularCohomology comparison (codimension + codimension))

    hodgeCycleClass :
      (codimension : Nat) →
      Hodge.RationalAlgebraicCycle variety codimension →
      Hodge.Carrier
        (Hodge.HodgePiece hodge codimension codimension)

    comparisonAgrees :
      (codimension : Nat) →
      (cycle : Hodge.RationalAlgebraicCycle variety codimension) →
      Hodge.singularToDeRham comparison
        (codimension + codimension)
        (singularCycleClass codimension cycle)
      ≡
      Hodge.injectPiece hodge
        codimension codimension
        (hodgeCycleClass codimension cycle)

open RationalAlgebraicCycleClassBackground public

------------------------------------------------------------------------
-- Literal local Clay core.
------------------------------------------------------------------------

record HodgeClayCoreAtCodimensionAlgebraicExact
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (cycleBackground : RationalAlgebraicCycleClassBackground hodge)
    (codimension : Nat) : Set₁ where
  field
    algebraicRepresentative :
      Exact.RationalHodgeClassExact hodge codimension →
      Hodge.RationalAlgebraicCycle variety codimension

    algebraicRepresentativeHasExactRationalClass :
      (alpha : Exact.RationalHodgeClassExact hodge codimension) →
      singularCycleClass cycleBackground codimension
        (algebraicRepresentative alpha)
      ≡ Exact.singularClass alpha

open HodgeClayCoreAtCodimensionAlgebraicExact public

------------------------------------------------------------------------
-- Same-object consequence in de Rham/Hodge cohomology.
------------------------------------------------------------------------

algebraicRepresentativeHasSameInjectedHodgeClass :
  ∀ {variety comparison hodge}
    {cycleBackground : RationalAlgebraicCycleClassBackground hodge}
    {codimension : Nat} →
  (core :
    HodgeClayCoreAtCodimensionAlgebraicExact
      cycleBackground codimension) →
  (alpha : Exact.RationalHodgeClassExact hodge codimension) →
  Hodge.injectPiece hodge codimension codimension
    (hodgeCycleClass cycleBackground codimension
      (algebraicRepresentative core alpha))
  ≡
  Hodge.injectPiece hodge codimension codimension
    (Exact.hodgeComponent alpha)
algebraicRepresentativeHasSameInjectedHodgeClass
    {comparison = comparison}
    {cycleBackground = cycleBackground}
    {codimension = codimension}
    core alpha =
  trans
    (sym
      (comparisonAgrees
        cycleBackground codimension
        (algebraicRepresentative core alpha)))
    (trans
      (cong
        (Hodge.singularToDeRham comparison
          (codimension + codimension))
        (algebraicRepresentativeHasExactRationalClass core alpha))
      (Exact.rationalClassLandsInHodgePiece alpha))

------------------------------------------------------------------------
-- Universal Clay surface over all supplied literal background objects.
--
-- This does NOT assert that the abstract background records are themselves
-- fully library-bound.  It says exactly what the novel theorem must prove once
-- those established objects are instantiated.
------------------------------------------------------------------------

record HodgeEstablishedBackgroundAt
    (variety : Hodge.SmoothProjectiveComplexVariety) : Setω where
  field
    comparison : Hodge.SingularDeRhamComparison variety
    hodge : Hodge.HodgeDecomposition variety comparison
    cycleClass :
      RationalAlgebraicCycleClassBackground hodge

open HodgeEstablishedBackgroundAt public

HodgeClayCoreForBackground :
  ∀ {variety} →
  HodgeEstablishedBackgroundAt variety →
  Set₁
HodgeClayCoreForBackground background =
  (codimension : Nat) →
  HodgeClayCoreAtCodimensionAlgebraicExact
    (cycleClass background) codimension

------------------------------------------------------------------------
-- Freeze boundary.
------------------------------------------------------------------------

record HodgeClayFreezeBoundary : Set where
  constructor hodge-clay-freeze-boundary
  field
    rationalIntersectionTypedExactly : Bool
    algebraicCycleCarrierTypedLiterally : Bool
    cycleComparisonStillBackground : Bool
    universalAlgebraicReopeningProved : Bool

canonicalHodgeClayFreezeBoundary : HodgeClayFreezeBoundary
canonicalHodgeClayFreezeBoundary =
  hodge-clay-freeze-boundary
    true
    true
    true
    false
