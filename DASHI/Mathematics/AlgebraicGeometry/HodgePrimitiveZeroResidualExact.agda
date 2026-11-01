module DASHI.Mathematics.AlgebraicGeometry.HodgePrimitiveZeroResidualExact where

------------------------------------------------------------------------
-- HODGE PRIMITIVE ZERO-RESIDUAL SPECIALIZATION
--
-- The generic primitive residual decomposition is useful only when a known
-- algebraic component actually shrinks the residual family.
--
-- This owner isolates the strongest solved special case:
--
--   if a literal algebraic cycle already represents the exact primitive class,
--   then the remaining primitive residual can be chosen to be the literal zero
--   class.
--
-- The current RationalVectorSpace API records additive identity / zero
-- compatibility only as proposition-valued background fields, so we DO NOT
-- silently use unexposed linear laws.  Instead the exact zero class, its
-- primitivity, comparison-to-zero, and x + 0 = x law are supplied explicitly
-- as established linear background.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge
import DASHI.Mathematics.AlgebraicGeometry.HodgeRationalClassIntersectionExact as Exact
import DASHI.Mathematics.AlgebraicGeometry.HodgeAlgebraicCycleClayCoreExact as Clay
import DASHI.Mathematics.AlgebraicGeometry.HodgePrimitiveLefschetzClayReductionExact as Primitive
import DASHI.Mathematics.AlgebraicGeometry.HodgePrimitiveAlgebraicResidualDecompositionExact as Residual

------------------------------------------------------------------------
-- Explicit zero-linear background at one primitive codimension.
------------------------------------------------------------------------

record PrimitiveZeroResidualBackground
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (isPrimitive : Primitive.PrimitivePredicate hodge)
    (codimension : Nat) : Set₁ where
  field
    zeroExact :
      Exact.RationalHodgeClassExact
        hodge codimension

    zeroSingularClass :
      Exact.singularClass zeroExact
      ≡
      Hodge.zero
        (Hodge.singularCohomology comparison
          (codimension + codimension))

    zeroIsPrimitive :
      isPrimitive codimension zeroExact

    addZeroRightExact :
      (class :
        Hodge.Carrier
          (Hodge.singularCohomology comparison
            (codimension + codimension))) →
      Hodge.add
        (Hodge.singularCohomology comparison
          (codimension + codimension))
        class
        (Hodge.zero
          (Hodge.singularCohomology comparison
            (codimension + codimension)))
      ≡
      class

open PrimitiveZeroResidualBackground public

zeroPrimitive :
  ∀ {variety comparison hodge}
    {isPrimitive : Primitive.PrimitivePredicate hodge}
    {codimension : Nat} →
  PrimitiveZeroResidualBackground
    isPrimitive codimension →
  Primitive.PrimitiveRationalHodgeClassExact
    isPrimitive codimension
zeroPrimitive background =
  Primitive.primitive-rational-hodge-class-exact
    (zeroExact background)
    (zeroIsPrimitive background)

------------------------------------------------------------------------
-- Canonical strict candidate family: primitive classes with zero singular
-- class.
------------------------------------------------------------------------

ZeroSingularPrimitiveResidualFamily :
  ∀ {variety comparison hodge}
    (isPrimitive : Primitive.PrimitivePredicate hodge) →
  Residual.ResidualPrimitiveFamily isPrimitive
ZeroSingularPrimitiveResidualFamily
    {comparison = comparison}
    isPrimitive
    codimension
    primitive =
  Exact.singularClass
      (Primitive.exactClass primitive)
  ≡
  Hodge.zero
    (Hodge.singularCohomology comparison
      (codimension + codimension))

------------------------------------------------------------------------
-- If knownCycle already represents primitive exactly, the residual is zero.
------------------------------------------------------------------------

knownCycleExactGivesZeroResidualSplit :
  ∀ {variety comparison hodge}
    {cycleBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge}
    {isPrimitive : Primitive.PrimitivePredicate hodge}
    {codimension : Nat}
    (zeroBackground :
      PrimitiveZeroResidualBackground
        isPrimitive codimension)
    (primitive :
      Primitive.PrimitiveRationalHodgeClassExact
        isPrimitive codimension)
    (knownCycle :
      Hodge.RationalAlgebraicCycle
        variety codimension) →
  Clay.singularCycleClass
      cycleBackground codimension knownCycle
  ≡
  Exact.singularClass
    (Primitive.exactClass primitive) →
  Residual.PrimitiveAlgebraicResidualSplit
    {cycleBackground = cycleBackground}
    (ZeroSingularPrimitiveResidualFamily isPrimitive)
    primitive
knownCycleExactGivesZeroResidualSplit
    {comparison = comparison}
    {cycleBackground = cycleBackground}
    {codimension = codimension}
    zeroBackground
    primitive
    knownCycle
    knownCycleExact =
  Residual.primitive-algebraic-residual-split
    knownCycle
    (zeroPrimitive zeroBackground)
    (zeroSingularClass zeroBackground)
    sameObject
  where
    singularSpace :
      Hodge.RationalVectorSpace
    singularSpace =
      Hodge.singularCohomology comparison
        (codimension + codimension)

    sameObject :
      Hodge.add
        singularSpace
        (Clay.singularCycleClass
          cycleBackground codimension knownCycle)
        (Exact.singularClass
          (Primitive.exactClass
            (zeroPrimitive zeroBackground)))
      ≡
      Exact.singularClass
        (Primitive.exactClass primitive)
    sameObject =
      trans
        (cong
          (Hodge.add singularSpace
            (Clay.singularCycleClass
              cycleBackground codimension knownCycle))
          (zeroSingularClass zeroBackground))
        (trans
          (addZeroRightExact
            zeroBackground
            (Clay.singularCycleClass
              cycleBackground codimension knownCycle))
          knownCycleExact)

------------------------------------------------------------------------
-- Non-vacuity of the zero-residual family.
--
-- One nonzero primitive class is enough to prove this family is genuinely
-- smaller than the whole primitive carrier.
------------------------------------------------------------------------

zeroResidualFamilyIsStrictOfNonzeroPrimitive :
  ∀ {variety comparison hodge}
    {isPrimitive : Primitive.PrimitivePredicate hodge}
    (codimension : Nat)
    (primitive :
      Primitive.PrimitiveRationalHodgeClassExact
        isPrimitive codimension) →
  (Exact.singularClass
      (Primitive.exactClass primitive)
    ≡
    Hodge.zero
      (Hodge.singularCohomology comparison
        (codimension + codimension)) →
    ⊥) →
  Residual.StrictResidualPrimitiveFamily
    isPrimitive
    (ZeroSingularPrimitiveResidualFamily isPrimitive)
zeroResidualFamilyIsStrictOfNonzeroPrimitive
    codimension
    primitive
    nonzero =
  record
    { Residual.excludedCodimension =
        codimension
    ; Residual.excludedPrimitive =
        primitive
    ; Residual.genuinelyExcluded =
        nonzero
    }

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The projective/hyperplane donor can now feed the residual programme in the
-- strongest possible way on every primitive class it already represents:
--
--   exact known cycle
--       ->
--   residual = literal zero primitive.
--
-- Thus those classes require no further residual algebraicity theorem.
--
-- The universal Hodge wall is now genuinely geometric:
-- find a SAME-OBJECT algebraic component for arbitrary primitive alpha such
-- that the remainder lands in a strict family (zero is the solved endpoint).
--
-- No subtraction operation, primitive projector, or universal decomposition is
-- manufactured here.
------------------------------------------------------------------------
