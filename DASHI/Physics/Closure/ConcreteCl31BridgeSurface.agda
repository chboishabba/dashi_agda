module DASHI.Physics.Closure.ConcreteCl31BridgeSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Algebra.Clifford.ConcreteCl31Basis as Cl31
import DASHI.Algebra.Clifford.UniversalProperty as CUP
import DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem as QCB

------------------------------------------------------------------------
-- Nontrivial Cl(3,1) bridge surface.
--
-- The existing `QuadraticToCliffordBridgeTheorem` owns the normalized
-- quadratic, bilinear form, abstract Clifford relation, and universal
-- factorization seam. `ConcreteCl31Basis` now supplies an actual sixteen-blade
-- basis with generator squares and anticommutation. This record keeps the two
-- owners connected without claiming that the current unit-carrier
-- presentation has already been replaced by a full linear multivector
-- algebra.

record ConcreteCl31BridgeSurface : Setω where
  field
    abstractQuadraticBridge : QCB.QuadraticToCliffordBridgeTheorem
    concreteBasis : Cl31.ConcreteCl31Basis

    basisDimension : Nat
    basisDimensionIs16 : basisDimension ≡ 16

    timeGenerator : Cl31.Generator
    spaceGenerator1 : Cl31.Generator
    spaceGenerator2 : Cl31.Generator
    spaceGenerator3 : Cl31.Generator

    timeGeneratorIsE0 : timeGenerator ≡ Cl31.e0
    spaceGenerator1IsE1 : spaceGenerator1 ≡ Cl31.e1
    spaceGenerator2IsE2 : spaceGenerator2 ≡ Cl31.e2
    spaceGenerator3IsE3 : spaceGenerator3 ≡ Cl31.e3

    timeSquareNegative :
      Cl31.genMul timeGenerator (Cl31.bladeOf timeGenerator)
      ≡ (Cl31.minus , Cl31.one)

    space1SquarePositive :
      Cl31.genMul spaceGenerator1 (Cl31.bladeOf spaceGenerator1)
      ≡ (Cl31.plus , Cl31.one)

    space2SquarePositive :
      Cl31.genMul spaceGenerator2 (Cl31.bladeOf spaceGenerator2)
      ≡ (Cl31.plus , Cl31.one)

    space3SquarePositive :
      Cl31.genMul spaceGenerator3 (Cl31.bladeOf spaceGenerator3)
      ≡ (Cl31.plus , Cl31.one)

    linearExtensionBoundary :
      Cl31.ConcreteCl31LinearExtensionBoundary

open ConcreteCl31BridgeSurface public

------------------------------------------------------------------------
-- Constructor: the basis/signature part is now canonical; the remaining
-- argument is exactly the honest linear-extension/universal-property seam.

concreteCl31BridgeFromLinearExtension :
  Cl31.ConcreteCl31LinearExtensionBoundary →
  ConcreteCl31BridgeSurface
concreteCl31BridgeFromLinearExtension extension =
  record
    { abstractQuadraticBridge = QCB.canonicalQuadraticToCliffordBridgeTheorem
    ; concreteBasis = Cl31.canonicalConcreteCl31Basis
    ; basisDimension = Cl31.bladeCount
    ; basisDimensionIs16 = refl
    ; timeGenerator = Cl31.e0
    ; spaceGenerator1 = Cl31.e1
    ; spaceGenerator2 = Cl31.e2
    ; spaceGenerator3 = Cl31.e3
    ; timeGeneratorIsE0 = refl
    ; spaceGenerator1IsE1 = refl
    ; spaceGenerator2IsE2 = refl
    ; spaceGenerator3IsE3 = refl
    ; timeSquareNegative = Cl31.generatorSquare Cl31.e0
    ; space1SquarePositive = Cl31.generatorSquare Cl31.e1
    ; space2SquarePositive = Cl31.generatorSquare Cl31.e2
    ; space3SquarePositive = Cl31.generatorSquare Cl31.e3
    ; linearExtensionBoundary = extension
    }

------------------------------------------------------------------------
-- Exact next theorem family.

record ConcreteCl31UniversalAdapter
  (surface : ConcreteCl31BridgeSurface) : Setω where
  field
    cliffordData : CUP.CliffordData
    cliffordAxioms : CUP.CliffordAxioms cliffordData
    universalProperty : CUP.CliffordUP cliffordData
    basisEmbedsNontrivially : Set
    multiplicationAgreesWithBasisAction : Set
    abstractGatePresentation : Set
