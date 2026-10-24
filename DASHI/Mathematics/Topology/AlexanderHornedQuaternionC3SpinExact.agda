module DASHI.Mathematics.Topology.AlexanderHornedQuaternionC3SpinExact where

------------------------------------------------------------------------
-- ACTUAL QUATERNIONIC ROTOR FOR THE SAME AMBIENT C3 MAP
--
-- Sources:
--   Hamilton's quaternion multiplication; binary tetrahedral/Hurwitz
--   24-unit group; standard Spin(3) -> SO(3) conjugation.
--
-- Existing exact DASHI proof donors (not independently reinvented):
--   Physics.YangMills.BalabanP33RationalQuaternionCoreExact
--   Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact
--   Mathematics.Topology.QuaternionHopfUnitOrbitExact
--   Algebra.FiniteQuaternionDoubleCover (Q8 -> V4, NOT this C3).
--
-- Choose q=(1+i+j+k)/2. Quaternion multiplication yields
--     q^3=-1, q^6=1, and q (xi+yj+zk) q^-1 = zi+xj+yk.
-- Its conjugation is exactly the *existing* spatial
--     rotateXYZ(x,y,z) = (z,x,y).
-- The alternative lift -q has order THREE, since (-q)^3=1.
-- Thus it is FALSE to say every lift of the SO(3) 120deg
-- rotation has order six; the two lifts have orders 6 and 3.
--
-- This is an explicit SAME-MAP rational-coordinate comparison,
-- NOT a lift of a torsion loop from the wild exterior fundamental
-- group G, and not a construction of Spin(3) covering topology.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; -½; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionCoreExact as Q
import DASHI.Mathematics.Topology.AlexanderHornedC3AmbientRotationExact as Ambient

rotor : Q.RationalQuaternion
rotor = Q.quat ½ ½ ½ ½

rotorInverse : Q.RationalQuaternion
rotorInverse = Q.quat ½ -½ -½ -½

negativeRotor : Q.RationalQuaternion
negativeRotor = Q.negQ rotor

pure : Ambient.Triple ℚ → Q.RationalQuaternion
pure (Ambient.xyz x y z) = Q.quat 0ℚ x y z

conjugatePure : Ambient.Triple ℚ → Q.RationalQuaternion
conjugatePure xyz = Q._*q_
  (Q._*q_ rotor (pure xyz)) rotorInverse

rotorCubedIsCentralMinusOne :
  Q._*q_ (Q._*q_ rotor rotor) rotor ≡ Q.negQ Q.oneQ
rotorCubedIsCentralMinusOne =
  Q.quaternionExt
    ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀

negativeRotorCubedIsOne :
  Q._*q_ (Q._*q_ negativeRotor negativeRotor) negativeRotor
    ≡ Q.oneQ
negativeRotorCubedIsOne =
  Q.quaternionExt
    ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀

rotorRightInverse :
  Q._*q_ rotor rotorInverse ≡ Q.oneQ
rotorRightInverse =
  Q.quaternionExt
    ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀

rotorLeftInverse :
  Q._*q_ rotorInverse rotor ≡ Q.oneQ
rotorLeftInverse =
  Q.quaternionExt
    ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀

-- This is the full arbitrary-coordinate equality, stronger than
-- three individual axis checks and explicitly tied to the SAME
-- ambient C3 rotation already used in the geometric construction.
conjugationMatchesExistingAmbientRotation :
  ∀ (x y z : ℚ) →
  conjugatePure (Ambient.xyz x y z)
    ≡ pure (Ambient.rotateXYZ (Ambient.xyz x y z))
conjugationMatchesExistingAmbientRotation x y z =
  Q.quaternionExt
    (ℚRing.solve-∀ x y z)
    (ℚRing.solve-∀ x y z)
    (ℚRing.solve-∀ x y z)
    (ℚRing.solve-∀ x y z)

-- The signed lifts q,-q induce the same spatial automorphism.
negativeRotorHasSameConjugation :
  ∀ (x y z : ℚ) →
  Q._*q_ (Q._*q_ negativeRotor (pure (Ambient.xyz x y z)))
    (Q.negQ rotorInverse)
    ≡ pure (Ambient.rotateXYZ (Ambient.xyz x y z))
negativeRotorHasSameConjugation x y z =
  Q.quaternionExt
    (ℚRing.solve-∀ x y z)
    (ℚRing.solve-∀ x y z)
    (ℚRing.solve-∀ x y z)
    (ℚRing.solve-∀ x y z)

-- Hypercomplex rotor action is not an element of pi1(exterior).
-- The no-order-three-in-G result uses the independent injective
-- free-group tower, not an SO(3) or Spin(3) calculation.
