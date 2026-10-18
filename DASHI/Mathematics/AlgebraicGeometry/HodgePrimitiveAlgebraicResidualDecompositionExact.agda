module DASHI.Mathematics.AlgebraicGeometry.HodgePrimitiveAlgebraicResidualDecompositionExact where

------------------------------------------------------------------------
-- HODGE PRIMITIVE ALGEBRAIC / RESIDUAL DECOMPOSITION
--
-- The primitive Clay cut asks for an algebraic representative of every exact
-- rational primitive class.  This owner refines that target:
--
--   primitive class
--      = known literal algebraic cycle class
--      + residual primitive class.
--
-- The decomposition is SAME-OBJECT on rational singular cohomology.  No
-- subtraction is invented: the current RationalVectorSpace interface exposes
-- additive-inverse laws only propositionally, not an executable negation.
--
-- A restricted residual family may therefore be attacked instead of the whole
-- primitive carrier.  If every primitive admits such a split and every
-- residual in that family is algebraically liftable, the original
-- PrimitiveAlgebraicLift follows by literal cycle addition.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge
import DASHI.Mathematics.AlgebraicGeometry.HodgeRationalClassIntersectionExact as Exact
import DASHI.Mathematics.AlgebraicGeometry.HodgeAlgebraicCycleClayCoreExact as Clay
import DASHI.Mathematics.AlgebraicGeometry.HodgePrimitiveLefschetzClayReductionExact as Primitive

------------------------------------------------------------------------
-- Minimal literal cycle-addition background at one codimension.
------------------------------------------------------------------------

record PrimitiveCycleAdditionBackground
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (cycleBackground : Clay.RationalAlgebraicCycleClassBackground hodge)
    (codimension : Nat) : Set₁ where
  field
    addCycle :
      Hodge.RationalAlgebraicCycle variety codimension →
      Hodge.RationalAlgebraicCycle variety codimension →
      Hodge.RationalAlgebraicCycle variety codimension

    addCycleClass :
      (left right :
        Hodge.RationalAlgebraicCycle variety codimension) →
      Clay.singularCycleClass
          cycleBackground codimension
          (addCycle left right)
      ≡
      Hodge.add
        (Hodge.singularCohomology comparison
          (codimension + codimension))
        (Clay.singularCycleClass
          cycleBackground codimension left)
        (Clay.singularCycleClass
          cycleBackground codimension right)

open PrimitiveCycleAdditionBackground public

------------------------------------------------------------------------
-- Restricted residual family.
------------------------------------------------------------------------

ResidualPrimitiveFamily :
  ∀ {variety comparison hodge}
    (isPrimitive : Primitive.PrimitivePredicate hodge) →
  Set₁
ResidualPrimitiveFamily isPrimitive =
  (codimension : Nat) →
  Primitive.PrimitiveRationalHodgeClassExact
    isPrimitive codimension →
  Set

------------------------------------------------------------------------
-- Same-object split of ONE primitive class.
------------------------------------------------------------------------

record PrimitiveAlgebraicResidualSplit
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    {cycleBackground : Clay.RationalAlgebraicCycleClassBackground hodge}
    {isPrimitive : Primitive.PrimitivePredicate hodge}
    (residualFamily : ResidualPrimitiveFamily isPrimitive)
    {codimension : Nat}
    (primitive :
      Primitive.PrimitiveRationalHodgeClassExact
        isPrimitive codimension) : Set₁ where
  constructor primitive-algebraic-residual-split
  field
    knownCycle :
      Hodge.RationalAlgebraicCycle
        variety codimension

    residualPrimitive :
      Primitive.PrimitiveRationalHodgeClassExact
        isPrimitive codimension

    residualRestricted :
      residualFamily codimension residualPrimitive

    sameObjectDecomposition :
      Hodge.add
        (Hodge.singularCohomology comparison
          (codimension + codimension))
        (Clay.singularCycleClass
          cycleBackground codimension knownCycle)
        (Exact.singularClass
          (Primitive.exactClass residualPrimitive))
      ≡
      Exact.singularClass
        (Primitive.exactClass primitive)

open PrimitiveAlgebraicResidualSplit public

------------------------------------------------------------------------
-- Universal decomposition producer, but into a restricted residual family.
------------------------------------------------------------------------

PrimitiveAlgebraicResidualDecomposition :
  ∀ {variety comparison hodge}
    (cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge)
    (isPrimitive : Primitive.PrimitivePredicate hodge)
    (residualFamily : ResidualPrimitiveFamily isPrimitive) →
  Set₁
PrimitiveAlgebraicResidualDecomposition
    cycleBackground
    isPrimitive
    residualFamily =
  (codimension : Nat) →
  (primitive :
    Primitive.PrimitiveRationalHodgeClassExact
      isPrimitive codimension) →
  PrimitiveAlgebraicResidualSplit
    {cycleBackground = cycleBackground}
    residualFamily
    primitive

------------------------------------------------------------------------
-- Only the restricted residuals now need a cycle producer.
------------------------------------------------------------------------

RestrictedResidualAlgebraicLift :
  ∀ {variety comparison hodge}
    (cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge)
    (isPrimitive : Primitive.PrimitivePredicate hodge)
    (residualFamily : ResidualPrimitiveFamily isPrimitive) →
  Set₁
RestrictedResidualAlgebraicLift
    {variety = variety}
    cycleBackground
    isPrimitive
    residualFamily =
  (codimension : Nat) →
  (residual :
    Primitive.PrimitiveRationalHodgeClassExact
      isPrimitive codimension) →
  residualFamily codimension residual →
  Σ
    (Hodge.RationalAlgebraicCycle
      variety codimension)
    (λ cycle →
      Clay.singularCycleClass
          cycleBackground codimension cycle
      ≡
      Exact.singularClass
        (Primitive.exactClass residual))

------------------------------------------------------------------------
-- Reconstruction theorem.
------------------------------------------------------------------------

residualLiftReconstructsPrimitive :
  ∀ {variety comparison hodge}
    {cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge}
    {isPrimitive : Primitive.PrimitivePredicate hodge}
    {residualFamily : ResidualPrimitiveFamily isPrimitive}
    {codimension : Nat}
    (addition :
      PrimitiveCycleAdditionBackground
        cycleBackground codimension)
    {primitive :
      Primitive.PrimitiveRationalHodgeClassExact
        isPrimitive codimension}
    (split :
      PrimitiveAlgebraicResidualSplit
        {cycleBackground = cycleBackground}
        residualFamily
        primitive)
    (residualLift :
      RestrictedResidualAlgebraicLift
        cycleBackground
        isPrimitive
        residualFamily) →
  Σ
    (Hodge.RationalAlgebraicCycle
      variety codimension)
    (λ cycle →
      Clay.singularCycleClass
          cycleBackground codimension cycle
      ≡
      Exact.singularClass
        (Primitive.exactClass primitive))
residualLiftReconstructsPrimitive
    {comparison = comparison}
    {codimension = codimension}
    addition
    split
    residualLift =
  addCycle addition
    (knownCycle split)
    residualCycle
  ,
  trans
    (addCycleClass addition
      (knownCycle split)
      residualCycle)
    (trans
      (cong
        (λ residualClass →
          Hodge.add
            (Hodge.singularCohomology comparison
              (codimension + codimension))
            (Clay.singularCycleClass
              _ codimension
              (knownCycle split))
            residualClass)
        residualClassExact)
      (sameObjectDecomposition split))
  where
    liftedResidual =
      residualLift
        codimension
        (residualPrimitive split)
        (residualRestricted split)

    residualCycle :
      Hodge.RationalAlgebraicCycle
        _ codimension
    residualCycle =
      proj₁ liftedResidual

    residualClassExact :
      Clay.singularCycleClass
          _ codimension residualCycle
      ≡
      Exact.singularClass
        (Primitive.exactClass
          (residualPrimitive split))
    residualClassExact =
      proj₂ liftedResidual

restrictedResidualLiftGivesPrimitiveLift :
  ∀ {variety comparison hodge}
    {cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge}
    {isPrimitive : Primitive.PrimitivePredicate hodge}
    (residualFamily : ResidualPrimitiveFamily isPrimitive) →
  ((codimension : Nat) →
    PrimitiveCycleAdditionBackground
      cycleBackground codimension) →
  PrimitiveAlgebraicResidualDecomposition
    cycleBackground
    isPrimitive
    residualFamily →
  RestrictedResidualAlgebraicLift
    cycleBackground
    isPrimitive
    residualFamily →
  Primitive.PrimitiveAlgebraicLift
    cycleBackground
    isPrimitive
restrictedResidualLiftGivesPrimitiveLift
    residualFamily
    additions
    decompose
    lift
    codimension
    primitive =
  residualLiftReconstructsPrimitive
    (additions codimension)
    (decompose codimension primitive)
    lift

------------------------------------------------------------------------
-- Strictness witness.
--
-- This does not manufacture a strict residual family.  It records the exact
-- evidence needed before claiming the decomposition has genuinely shrunk the
-- theorem-search carrier rather than merely renamed PrimitiveAlgebraicLift.
------------------------------------------------------------------------

record StrictResidualPrimitiveFamily
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (isPrimitive : Primitive.PrimitivePredicate hodge)
    (residualFamily : ResidualPrimitiveFamily isPrimitive) : Set₁ where
  field
    excludedCodimension : Nat
    excludedPrimitive :
      Primitive.PrimitiveRationalHodgeClassExact
        isPrimitive excludedCodimension
    genuinelyExcluded :
      residualFamily
        excludedCodimension
        excludedPrimitive →
      ⊥

open StrictResidualPrimitiveFamily public

------------------------------------------------------------------------
-- FRONTIER
--
-- This is a real same-object reduction only once instantiated with:
--
--   * literal known algebraic cycles;
--   * exact class + residual = original primitive equations;
--   * a residualFamily with an actual strictness witness.
--
-- The remaining Hodge search is therefore sharper:
--
--   find an in-repo algebraic constructor that produces the knownCycle part
--   AND proves the residual lands in a genuinely smaller geometric family.
--
-- No such strict universal decomposition is asserted here.
------------------------------------------------------------------------
