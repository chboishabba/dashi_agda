module DASHI.Mathematics.AlgebraicGeometry.HodgeRationalClassIntersectionExact where

------------------------------------------------------------------------
-- EXACT RATIONAL-HODGE-CLASS INTERSECTION
--
-- The older HodgeDecompositionCycleClassExact carrier records an element of
-- the (p,p) Hodge piece.  That is not, by itself, the rationality condition in
-- the classical Hodge conjecture.
--
-- Here rationality is witnessed on the SAME cohomology object:
--
--   alpha_Q : H^(2p)(X,Q)
--      | singular/de Rham comparison
--      v
--   alpha_dR = injection(alpha_(p,p)).
--
-- Algebraic cycles are likewise given a rational singular-cohomology class
-- whose comparison agrees with the existing Hodge-piece cycle class.
--
-- The Clay-facing local obligation is then exactly:
-- every such rational Hodge class has an algebraic cycle whose RATIONAL
-- singular cycle class equals alpha_Q.
--
-- No algebraic representative is manufactured here.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge

record RationalHodgeClassExact
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    (hodge : Hodge.HodgeDecomposition variety comparison)
    (codimension : Nat) : Set₁ where
  constructor rational-hodge-class-exact
  field
    singularClass :
      Hodge.Carrier
        (Hodge.singularCohomology comparison (codimension + codimension))

    hodgeComponent :
      Hodge.Carrier
        (Hodge.HodgePiece hodge codimension codimension)

    rationalClassLandsInHodgePiece :
      Hodge.singularToDeRham comparison
        (codimension + codimension)
        singularClass
      ≡
      Hodge.injectPiece hodge
        codimension codimension
        hodgeComponent

open RationalHodgeClassExact public

record RationalCycleClassComparison
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (cycleMap : Hodge.CycleClassMap variety comparison hodge) : Setω where
  field
    singularCycleClass :
      (codimension : Nat) →
      Hodge.Cycle cycleMap codimension →
      Hodge.Carrier
        (Hodge.singularCohomology comparison (codimension + codimension))

    comparisonAgreesWithHodgeCycleClass :
      (codimension : Nat) →
      (cycle : Hodge.Cycle cycleMap codimension) →
      Hodge.singularToDeRham comparison
        (codimension + codimension)
        (singularCycleClass codimension cycle)
      ≡
      Hodge.injectPiece hodge
        codimension codimension
        (Hodge.cycleClass cycleMap codimension cycle)

open RationalCycleClassComparison public

record HodgeClayCoreAtCodimensionExact
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (cycleMap : Hodge.CycleClassMap variety comparison hodge)
    (rationalCycleClass : RationalCycleClassComparison cycleMap)
    (codimension : Nat) : Set₁ where
  field
    everyRationalHodgeClassHasAlgebraicCycle :
      RationalHodgeClassExact hodge codimension →
      Hodge.Cycle cycleMap codimension

    cycleRepresentsRationalSingularClass :
      (alpha : RationalHodgeClassExact hodge codimension) →
      singularCycleClass rationalCycleClass codimension
        (everyRationalHodgeClassHasAlgebraicCycle alpha)
      ≡ singularClass alpha

open HodgeClayCoreAtCodimensionExact public

------------------------------------------------------------------------
-- Same-object consequence: a core witness represents the same de Rham class.
------------------------------------------------------------------------

coreRepresentativeHasSameInjectedHodgeClass :
  ∀ {variety comparison hodge}
    {cycleMap : Hodge.CycleClassMap variety comparison hodge}
    {rationalCycleClass : RationalCycleClassComparison cycleMap}
    {codimension : Nat} →
  (core :
    HodgeClayCoreAtCodimensionExact
      cycleMap rationalCycleClass codimension) →
  (alpha : RationalHodgeClassExact hodge codimension) →
  Hodge.injectPiece hodge codimension codimension
    (Hodge.cycleClass cycleMap codimension
      (everyRationalHodgeClassHasAlgebraicCycle core alpha))
  ≡
  Hodge.injectPiece hodge codimension codimension
    (hodgeComponent alpha)
coreRepresentativeHasSameInjectedHodgeClass
    {comparison = comparison}
    {cycleMap = cycleMap}
    {rationalCycleClass = rationalCycleClass}
    {codimension = codimension}
    core alpha =
  trans
    (sym
      (comparisonAgreesWithHodgeCycleClass
        rationalCycleClass codimension
        (everyRationalHodgeClassHasAlgebraicCycle core alpha)))
    (trans
      (cong
        (Hodge.singularToDeRham comparison
          (codimension + codimension))
        (cycleRepresentsRationalSingularClass core alpha))
      (rationalClassLandsInHodgePiece alpha))

------------------------------------------------------------------------
-- Explicit boundary: the exact carrier needs BOTH sides of the intersection.
------------------------------------------------------------------------

record RationalHodgeClassIntersectionData
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    (hodge : Hodge.HodgeDecomposition variety comparison)
    (codimension : Nat) : Set₁ where
  field
    rationalSource :
      Hodge.Carrier
        (Hodge.singularCohomology comparison (codimension + codimension))
    ppComponent :
      Hodge.Carrier (Hodge.HodgePiece hodge codimension codimension)
    sameDeRhamClass :
      Hodge.singularToDeRham comparison
        (codimension + codimension)
        rationalSource
      ≡
      Hodge.injectPiece hodge codimension codimension ppComponent

intersectionDataToExactRationalHodgeClass :
  ∀ {variety comparison hodge codimension} →
  RationalHodgeClassIntersectionData hodge codimension →
  RationalHodgeClassExact hodge codimension
intersectionDataToExactRationalHodgeClass data =
  rational-hodge-class-exact
    (RationalHodgeClassIntersectionData.rationalSource data)
    (RationalHodgeClassIntersectionData.ppComponent data)
    (RationalHodgeClassIntersectionData.sameDeRhamClass data)
