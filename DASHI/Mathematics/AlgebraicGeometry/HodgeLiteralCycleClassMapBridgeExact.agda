module DASHI.Mathematics.AlgebraicGeometry.HodgeLiteralCycleClassMapBridgeExact where

------------------------------------------------------------------------
-- LITERAL RationalAlgebraicCycle MAP AND LEGACY UNIVERSE FIREWALL
--
-- The older projective-space / hyperplane reopening compilers consume
--
--   Hodge.CycleClassMap
--
-- whose field is fixed at:
--
--   Cycle : Nat -> Set.
--
-- The frozen Clay carrier is:
--
--   RationalAlgebraicCycle variety codimension : Set₁.
--
-- Therefore a literal carrier-preserving instance of the OLD CycleClassMap is
-- not universe-correct.  This owner pays the literal cycle algebra and defines
-- the universe-correct map that the legacy projective/hyperplane compilers must
-- be ported to (or the old CycleClassMap must be universe-lifted).
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)
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
-- Universe-correct literal cycle-class map.
------------------------------------------------------------------------

record LiteralRationalCycleClassMap
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    (hodge : Hodge.HodgeDecomposition variety comparison) : Setω where
  field
    cycleClassBackground :
      Clay.RationalAlgebraicCycleClassBackground hodge

    zeroClass :
      (codimension : Nat) →
      Clay.hodgeCycleClass
          cycleClassBackground codimension
          zeroRationalAlgebraicCycle
      ≡
      Hodge.zero
        (Hodge.HodgePiece hodge codimension codimension)

    additiveClass :
      (codimension : Nat) →
      (left right :
        Hodge.RationalAlgebraicCycle variety codimension) →
      Clay.hodgeCycleClass
          cycleClassBackground codimension
          (addRationalAlgebraicCycle left right)
      ≡
      Hodge.add
        (Hodge.HodgePiece hodge codimension codimension)
        (Clay.hodgeCycleClass
          cycleClassBackground codimension left)
        (Clay.hodgeCycleClass
          cycleClassBackground codimension right)

    homogeneousClass :
      (codimension : Nat) →
      (scalar : ℚ) →
      (cycle :
        Hodge.RationalAlgebraicCycle variety codimension) →
      Clay.hodgeCycleClass
          cycleClassBackground codimension
          (scaleRationalAlgebraicCycle scalar cycle)
      ≡
      Hodge.scale
        (Hodge.HodgePiece hodge codimension codimension)
        scalar
        (Clay.hodgeCycleClass
          cycleClassBackground codimension cycle)

open LiteralRationalCycleClassMap public

------------------------------------------------------------------------
-- Literal map operations are now fixed and carrier-preserving.
------------------------------------------------------------------------

literalZeroCycle :
  ∀ {variety comparison hodge}
    (map : LiteralRationalCycleClassMap hodge)
    (codimension : Nat) →
  Hodge.RationalAlgebraicCycle variety codimension
literalZeroCycle map codimension =
  zeroRationalAlgebraicCycle

literalAddCycle :
  ∀ {variety comparison hodge}
    (map : LiteralRationalCycleClassMap hodge)
    (codimension : Nat) →
  Hodge.RationalAlgebraicCycle variety codimension →
  Hodge.RationalAlgebraicCycle variety codimension →
  Hodge.RationalAlgebraicCycle variety codimension
literalAddCycle map codimension =
  addRationalAlgebraicCycle

literalScaleCycle :
  ∀ {variety comparison hodge}
    (map : LiteralRationalCycleClassMap hodge)
    (codimension : Nat) →
  ℚ →
  Hodge.RationalAlgebraicCycle variety codimension →
  Hodge.RationalAlgebraicCycle variety codimension
literalScaleCycle map codimension =
  scaleRationalAlgebraicCycle

literalHodgeCycleClass :
  ∀ {variety comparison hodge}
    (map : LiteralRationalCycleClassMap hodge)
    (codimension : Nat) →
  Hodge.RationalAlgebraicCycle variety codimension →
  Hodge.Carrier
    (Hodge.HodgePiece hodge codimension codimension)
literalHodgeCycleClass map =
  Clay.hodgeCycleClass
    (cycleClassBackground map)

------------------------------------------------------------------------
-- Singular-cycle addition bridge used by primitive residual reconstruction.
------------------------------------------------------------------------

record LiteralSingularCycleClassAdditivity
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (map : LiteralRationalCycleClassMap hodge) : Setω where
  field
    additiveSingularClass :
      (codimension : Nat) →
      (left right :
        Hodge.RationalAlgebraicCycle variety codimension) →
      Clay.singularCycleClass
          (cycleClassBackground map)
          codimension
          (addRationalAlgebraicCycle left right)
      ≡
      Hodge.add
        (Hodge.singularCohomology comparison
          (codimension + codimension))
        (Clay.singularCycleClass
          (cycleClassBackground map)
          codimension left)
        (Clay.singularCycleClass
          (cycleClassBackground map)
          codimension right)

open LiteralSingularCycleClassAdditivity public

------------------------------------------------------------------------
-- Exact reuse boundary.
------------------------------------------------------------------------

record LegacyLiteralCycleMapReuseBoundary : Set where
  constructor legacy-literal-cycle-map-reuse-boundary
  field
    literalCycleAlgebraPaid : ⊤
    literalSetOneCarrierPaid : ⊤
    legacyCycleCarrierLivesInSet : ⊤
    directCarrierPreservingLegacyInstancePaid : Set

canonicalLegacyLiteralCycleMapReuseBoundary :
  LegacyLiteralCycleMapReuseBoundary
canonicalLegacyLiteralCycleMapReuseBoundary =
  legacy-literal-cycle-map-reuse-boundary
    _
    _
    _
    ⊥

directLegacyCarrierReuseStillUnpaid :
  directCarrierPreservingLegacyInstancePaid
    canonicalLegacyLiteralCycleMapReuseBoundary →
  ⊥
directLegacyCarrierReuseStillUnpaid ()

------------------------------------------------------------------------
-- FRONTIER
--
-- The requested bridge exposed a precise API mismatch:
--
--   legacy CycleClassMap.Cycle : Nat -> Set
--   literal RationalAlgebraicCycle : Set₁.
--
-- So the safe next implementation is one of:
--
--   1. port the projective/hyperplane reopening compiler to
--      LiteralRationalCycleClassMap; or
--
--   2. universe-generalize the legacy CycleClassMap itself.
--
-- The literal cycle operations are now paid and can be reused by either route.
------------------------------------------------------------------------
