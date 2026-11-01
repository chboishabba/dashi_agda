module DASHI.Foundations.CantorCylinderMassExact where

------------------------------------------------------------------------
-- FINITE CANTOR CYLINDER MASS AT ARBITRARY DEPTH
--
-- The earlier Cantor consumer reference fixes a depth-three 27/8 example.
-- Here we add the depth-parametric combinatorial measure spine.
--
-- A polar cylinder at depth d is assigned dyadic mass 1 / 2^d.  Rather than
-- importing rational/measure theory, numerator and denominator are retained
-- separately.  Refinement doubles the denominator and replaces one parent by
-- two children, each with numerator one.  Hence parent mass equals the sum of
-- its child masses after passage to the common child denominator.
--
-- At every finite depth, the number of polar cylinders is exactly 2^d, equal
-- to the common denominator.  Therefore the normalized layer has total mass
-- one in this dyadic representation.  This is a finite cylinder premeasure
-- certificate, not the classical extension theorem for the limiting Cantor
-- measure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Biology.TernaryCantorWheelDiffusionExact as Cantor
import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper

powTwo : Nat → Nat
powTwo = Hyper.powNat 2

record DyadicCylinderMass (depth : Nat) : Set where
  constructor dyadicCylinderMass
  field
    numerator : Nat
    denominator : Nat
    numeratorIsOne : numerator ≡ 1
    denominatorIsPowTwo : denominator ≡ powTwo depth

open DyadicCylinderMass public

canonicalCylinderMass : (depth : Nat) → DyadicCylinderMass depth
canonicalCylinderMass depth = dyadicCylinderMass 1 (powTwo depth) refl refl

childDenominatorDoubles :
  (depth : Nat) →
  denominator (canonicalCylinderMass (suc depth))
  ≡ 2 * denominator (canonicalCylinderMass depth)
childDenominatorDoubles depth = refl

------------------------------------------------------------------------
-- Parent/children consistency at the common child denominator.
------------------------------------------------------------------------

record BinaryCylinderSplit (depth : Nat) : Set where
  constructor binaryCylinderSplit
  field
    parent : DyadicCylinderMass depth
    leftChild rightChild : DyadicCylinderMass (suc depth)
    commonChildDenominator :
      denominator leftChild ≡ denominator rightChild
    parentDenominatorScalesToChildren :
      denominator leftChild ≡ 2 * denominator parent
    parentNumeratorAtChildScale : Nat
    childNumeratorSum : Nat
    parentNumeratorAtChildScaleIsTwo : parentNumeratorAtChildScale ≡ 2
    childNumeratorSumIsTwo : childNumeratorSum ≡ 2

open BinaryCylinderSplit public

canonicalBinarySplit : (depth : Nat) → BinaryCylinderSplit depth
canonicalBinarySplit depth =
  binaryCylinderSplit
    (canonicalCylinderMass depth)
    (canonicalCylinderMass (suc depth))
    (canonicalCylinderMass (suc depth))
    refl
    refl
    2
    2
    refl
    refl

parentMassEqualsChildrenAtCommonScale :
  (depth : Nat) →
  parentNumeratorAtChildScale (canonicalBinarySplit depth)
  ≡ childNumeratorSum (canonicalBinarySplit depth)
parentMassEqualsChildrenAtCommonScale depth = refl

------------------------------------------------------------------------
-- Whole-layer normalization.
--
-- With one numerator unit on every polar cylinder, total numerator is the
-- cylinder count 2^d; the common denominator is also 2^d.
------------------------------------------------------------------------

record PolarLayerUnitMass (depth : Nat) : Set where
  constructor polarLayerUnitMass
  field
    cylinderCount : Nat
    commonDenominator : Nat
    totalNumerator : Nat
    cylinderCountIsPolarCount :
      cylinderCount ≡ Cantor.polarAddressCount depth
    commonDenominatorIsPowTwo : commonDenominator ≡ powTwo depth
    totalNumeratorIsCylinderCount : totalNumerator ≡ cylinderCount
    normalizedUnitExact : totalNumerator ≡ commonDenominator

open PolarLayerUnitMass public

polarLayerHasUnitMass : (depth : Nat) → PolarLayerUnitMass depth
polarLayerHasUnitMass depth =
  polarLayerUnitMass
    (Cantor.polarAddressCount depth)
    (powTwo depth)
    (Cantor.polarAddressCount depth)
    refl
    refl
    refl
    refl

polarDepthThreeStillEight :
  cylinderCount (polarLayerHasUnitMass 3) ≡ 8
polarDepthThreeStillEight = refl

ternaryAmbientDepthThreeStillTwentySeven :
  Cantor.ternaryAddressCount 3 ≡ 27
ternaryAmbientDepthThreeStillTwentySeven = refl

------------------------------------------------------------------------
-- Boundary: finite unit normalization is not world truth and is not yet the
-- sigma-additive limiting measure theorem.  The latter requires a measure
-- extension layer beyond this finite combinatorial certificate.
------------------------------------------------------------------------
