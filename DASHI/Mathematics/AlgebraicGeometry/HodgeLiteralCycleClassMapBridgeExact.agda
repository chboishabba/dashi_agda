module DASHI.Mathematics.AlgebraicGeometry.HodgeLiteralCycleClassMapBridgeExact where

------------------------------------------------------------------------
-- LITERAL RationalAlgebraicCycle -> legacy CycleClassMap bridge
--
-- The older projective-space / hyperplane reopening compilers consume
-- Hodge.CycleClassMap, whose Cycle carrier is abstract.
--
-- The frozen Clay owner instead insists on the literal carrier
--
--   RationalAlgebraicCycle variety codimension.
--
-- This module builds the literal cycle algebra structurally and shows that,
-- once the hodgeCycleClass map is supplied with its ordinary linearity laws,
-- it induces a legacy CycleClassMap whose Cycle carrier is definitionally the
-- frozen literal carrier.
--
-- No Hodge-conjecture theorem is imported by this bridge.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Rational.Base using (ℚ; _*_)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge
import DASHI.Mathematics.AlgebraicGeometry.HodgeAlgebraicCycleClayCoreExact as Clay

------------------------------------------------------------------------
-- Literal cycle algebra.
------------------------------------------------------------------------

zeroRationalAlgebraicCycle :
  ∀ {variety : Hodge.SmoothProjectiveComplexVariety}
    {codimension : Nat} →
  Hodge.RationalAlgebraicCycle variety codimension
zeroRationalAlgebraicCycle =
  record
    { Hodge.CycleGenerator = ⊥
    ; Hodge.coefficient = λ ()
    ; Hodge.finiteSupport = ⊤
    ; Hodge.algebraicSubvarietyWitness = λ ()
    }

addRationalAlgebraicCycle :
  ∀ {variety : Hodge.SmoothProjectiveComplexVariety}
    {codimension : Nat} →
  Hodge.RationalAlgebraicCycle variety codimension →
  Hodge.RationalAlgebraicCycle variety codimension →
  Hodge.RationalAlgebraicCycle variety codimension
addRationalAlgebraicCycle left right =
  record
    { Hodge.CycleGenerator =
        Hodge.CycleGenerator left
        ⊎
        Hodge.CycleGenerator right
    ; Hodge.coefficient = λ where
        (inj₁ generator) →
          Hodge.coefficient left generator
        (inj₂ generator) →
          Hodge.coefficient right generator
    ; Hodge.finiteSupport =
        Hodge.finiteSupport left
        ×
        Hodge.finiteSupport right
    ; Hodge.algebraicSubvarietyWitness = λ where
        (inj₁ generator) →
          Hodge.algebraicSubvarietyWitness left generator
        (inj₂ generator) →
          Hodge.algebraicSubvarietyWitness right generator
    }

scaleRationalAlgebraicCycle :
  ∀ {variety : Hodge.SmoothProjectiveComplexVariety}
    {codimension : Nat} →
  ℚ →
  Hodge.RationalAlgebraicCycle variety codimension →
  Hodge.RationalAlgebraicCycle variety codimension
scaleRationalAlgebraicCycle scalar cycle =
  record
    { Hodge.CycleGenerator =
        Hodge.CycleGenerator cycle
    ; Hodge.coefficient =
        λ generator →
          scalar * Hodge.coefficient cycle generator
    ; Hodge.finiteSupport =
        Hodge.finiteSupport cycle
    ; Hodge.algebraicSubvarietyWitness =
        Hodge.algebraicSubvarietyWitness cycle
    }

------------------------------------------------------------------------
-- Missing ordinary class-linearity laws.
--
-- These are not algebraicity-of-all-Hodge-classes statements. They are the
-- homomorphism laws needed to expose the already-supplied hodgeCycleClass as a
-- legacy CycleClassMap on the SAME literal cycle carrier.
------------------------------------------------------------------------

record LiteralHodgeCycleClassLinearity
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (background :
      Clay.RationalAlgebraicCycleClassBackground hodge) : Setω where
  field
    zeroClass :
      (codimension : Nat) →
      Clay.hodgeCycleClass
          background codimension
          zeroRationalAlgebraicCycle
      ≡
      Hodge.zero
        (Hodge.HodgePiece hodge codimension codimension)

    additiveClass :
      (codimension : Nat) →
      (left right :
        Hodge.RationalAlgebraicCycle variety codimension) →
      Clay.hodgeCycleClass
          background codimension
          (addRationalAlgebraicCycle left right)
      ≡
      Hodge.add
        (Hodge.HodgePiece hodge codimension codimension)
        (Clay.hodgeCycleClass
          background codimension left)
        (Clay.hodgeCycleClass
          background codimension right)

    homogeneousClass :
      (codimension : Nat) →
      (scalar : ℚ) →
      (cycle :
        Hodge.RationalAlgebraicCycle variety codimension) →
      Clay.hodgeCycleClass
          background codimension
          (scaleRationalAlgebraicCycle scalar cycle)
      ≡
      Hodge.scale
        (Hodge.HodgePiece hodge codimension codimension)
        scalar
        (Clay.hodgeCycleClass
          background codimension cycle)

open LiteralHodgeCycleClassLinearity public

------------------------------------------------------------------------
-- Carrier-preserving legacy adapter.
------------------------------------------------------------------------

literalCycleClassMap :
  ∀ {variety comparison hodge}
    (background :
      Clay.RationalAlgebraicCycleClassBackground hodge) →
  LiteralHodgeCycleClassLinearity background →
  Hodge.CycleClassMap
    variety
    comparison
    hodge
literalCycleClassMap background linearity =
  record
    { Hodge.Cycle =
        λ codimension →
          Hodge.RationalAlgebraicCycle
            _ codimension
    ; Hodge.zeroCycle =
        λ codimension →
          zeroRationalAlgebraicCycle
    ; Hodge.addCycle =
        λ codimension →
          addRationalAlgebraicCycle
    ; Hodge.scaleCycle =
        λ codimension →
          scaleRationalAlgebraicCycle
    ; Hodge.cycleClass =
        Clay.hodgeCycleClass background
    ; Hodge.cycleClassZero =
        zeroClass linearity
    ; Hodge.cycleClassAdditive =
        additiveClass linearity
    ; Hodge.cycleClassHomogeneous =
        homogeneousClass linearity
    ; Hodge.geometricCycleConstruction =
        λ codimension → Set
    }

------------------------------------------------------------------------
-- Definitional carrier receipt.
------------------------------------------------------------------------

literalCycleClassMapCarrier :
  ∀ {variety comparison hodge}
    (background :
      Clay.RationalAlgebraicCycleClassBackground hodge)
    (linearity :
      LiteralHodgeCycleClassLinearity background)
    (codimension : Nat) →
  Hodge.Cycle
      (literalCycleClassMap background linearity)
      codimension
  ≡
  Hodge.RationalAlgebraicCycle
      variety codimension
literalCycleClassMapCarrier background linearity codimension =
  refl

literalCycleClassMapClassAgrees :
  ∀ {variety comparison hodge}
    (background :
      Clay.RationalAlgebraicCycleClassBackground hodge)
    (linearity :
      LiteralHodgeCycleClassLinearity background)
    (codimension : Nat)
    (cycle :
      Hodge.RationalAlgebraicCycle variety codimension) →
  Hodge.cycleClass
      (literalCycleClassMap background linearity)
      codimension
      cycle
  ≡
  Clay.hodgeCycleClass background codimension cycle
literalCycleClassMapClassAgrees
    background linearity codimension cycle =
  refl

------------------------------------------------------------------------
-- Singular-cycle addition background for the new primitive residual split.
--
-- The literal cycle operation is now fixed. Only its singular class-linearity
-- law remains established-background input.
------------------------------------------------------------------------

record LiteralSingularCycleClassAdditivity
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (background :
      Clay.RationalAlgebraicCycleClassBackground hodge) : Setω where
  field
    additiveSingularClass :
      (codimension : Nat) →
      (left right :
        Hodge.RationalAlgebraicCycle variety codimension) →
      Clay.singularCycleClass
          background codimension
          (addRationalAlgebraicCycle left right)
      ≡
      Hodge.add
        (Hodge.singularCohomology comparison
          (codimension + codimension))
        (Clay.singularCycleClass
          background codimension left)
        (Clay.singularCycleClass
          background codimension right)

open LiteralSingularCycleClassAdditivity public

------------------------------------------------------------------------
-- FRONTIER
--
-- Paid:
--   literal zero/add/scale on RationalAlgebraicCycle;
--   exact legacy CycleClassMap carrier adapter;
--   exact agreement with the frozen hodgeCycleClass.
--
-- Still required from established cycle-class theory:
--   ordinary zero/add/scale linearity of hodgeCycleClass;
--   singular additivity when using the primitive residual reconstruction.
--
-- Once those laws are instantiated, existing legacy projective/hyperplane
-- constructors operate on the SAME literal Clay cycle carrier.
------------------------------------------------------------------------
