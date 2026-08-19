module DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Andrew Majda.
-- Title: "The Beltrami spectrum for incompressible fluid flows".
-- Communications in Mathematical Physics 115 (1988), 435--456.
-- DOI: 10.1007/BF01218021.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND93 / EXACT FAVOURABLE ENDPOINT
--
-- The Round92 helical programme must recover the exact Beltrami endpoint:
-- if omega = alpha u on one physical fibre, then u x omega vanishes exactly.
-- This module proves that statement directly on the repository Complex3
-- carrier.  No norm estimate, turbulence statistic, or regularity claim is
-- imported.  The result is pure commutative-field algebra and is useful as a
-- falsification test for every later favourable/adverse cost decomposition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive

complex3Cross :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
complex3Cross a b =
  C3.complex3
    (C3.complexSubtract
      (C3.complexMultiply (C3.y a) (C3.z b))
      (C3.complexMultiply (C3.z a) (C3.y b)))
    (C3.complexSubtract
      (C3.complexMultiply (C3.z a) (C3.x b))
      (C3.complexMultiply (C3.x a) (C3.z b)))
    (C3.complexSubtract
      (C3.complexMultiply (C3.x a) (C3.y b))
      (C3.complexMultiply (C3.y a) (C3.x b)))

pullScalarThroughProduct :
  ∀ {r} {F : C3.RealField r}
    (a scalar b : C3.Complex F) →
  C3.complexMultiply a (C3.complexMultiply scalar b)
  ≡ C3.complexMultiply scalar (C3.complexMultiply a b)
pullScalarThroughProduct a scalar b =
  trans
    (sym (Algebra.complexMultiplyAssociative a scalar b))
    (trans
      (cong
        (λ left → C3.complexMultiply left b)
        (Algebra.complexMultiplyCommutative a scalar))
      (Algebra.complexMultiplyAssociative scalar a b))

scaledCrossCoordinateZero :
  ∀ {r} {F : C3.RealField r}
    (a b scalar : C3.Complex F) →
  C3.complexSubtract
    (C3.complexMultiply a (C3.complexMultiply scalar b))
    (C3.complexMultiply b (C3.complexMultiply scalar a))
  ≡ C3.complexZero F
scaledCrossCoordinateZero a b scalar =
  let
    leftMeaning :
      C3.complexMultiply a (C3.complexMultiply scalar b)
      ≡ C3.complexMultiply scalar (C3.complexMultiply a b)
    leftMeaning = pullScalarThroughProduct a scalar b

    rightMeaning :
      C3.complexMultiply b (C3.complexMultiply scalar a)
      ≡ C3.complexMultiply scalar (C3.complexMultiply a b)
    rightMeaning =
      trans
        (pullScalarThroughProduct b scalar a)
        (cong
          (C3.complexMultiply scalar)
          (Algebra.complexMultiplyCommutative b a))
  in
  trans
    (cong
      (λ left →
        C3.complexSubtract left
          (C3.complexMultiply b (C3.complexMultiply scalar a)))
      leftMeaning)
    (trans
      (cong
        (C3.complexSubtract
          (C3.complexMultiply scalar (C3.complexMultiply a b)))
        rightMeaning)
      (Additive.complexSubtractSelf
        (C3.complexMultiply scalar (C3.complexMultiply a b))))

crossWithScaledSelfZero :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (value : C3.Complex3 F) →
  complex3Cross value (C3.complex3Scale scalar value)
  ≡ C3.complex3Zero F
crossWithScaledSelfZero scalar (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (scaledCrossCoordinateZero vy vz scalar)
    (scaledCrossCoordinateZero vz vx scalar)
    (scaledCrossCoordinateZero vx vy scalar)

record BeltramiFibre
    {r} {F : C3.RealField r} : Set r where
  constructor beltrami-fibre
  field
    velocity vorticity : C3.Complex3 F
    eigenvalue : C3.Complex F
    vorticityIsScaledVelocity :
      vorticity ≡ C3.complex3Scale eigenvalue velocity

open BeltramiFibre public

beltramiRotationalNonlinearityZero :
  ∀ {r} {F : C3.RealField r}
    (B : BeltramiFibre {F = F}) →
  complex3Cross (velocity B) (vorticity B)
  ≡ C3.complex3Zero F
beltramiRotationalNonlinearityZero B =
  trans
    (cong (complex3Cross (velocity B))
      (vorticityIsScaledVelocity B))
    (crossWithScaledSelfZero (eigenvalue B) (velocity B))

round93ExactBeltramiCrossSuppressionClosed : Bool
round93ExactBeltramiCrossSuppressionClosed = true

round93ExactBeltramiCrossSuppressionClosedIsTrue :
  round93ExactBeltramiCrossSuppressionClosed ≡ true
round93ExactBeltramiCrossSuppressionClosedIsTrue = refl
