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
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD
import DASHI.Mathematics.Topology.QuaternionHopfUnitOrbitExact as Hopf
import DASHI.Algebra.FiniteQuaternionDoubleCover as Q8

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

------------------------------------------------------------------------
-- Reuse an ACTUAL EXISTING unit-quaternion/Hopf group-action consumer.
-- The right-action on a quaternion pair is NOT the conjugation
-- rotation above: these are two distinct actions of the same
-- quaternion element, and we do not identify their fibres.
------------------------------------------------------------------------

rotorHasUnitNorm : CD.quaternionNormSq rotor ≡ 1ℚ
rotorHasUnitNorm = ℚRing.solve-∀

selectedRotorIsExistingUnitQuaternion : Hopf.UnitQuaternion
selectedRotorIsExistingUnitQuaternion =
  Hopf.unitQuaternion rotor rotorHasUnitNorm

selectedRotorPreservesExistingHopfQuaternion :
  ∀ pair →
  Hopf.pairHopfQuaternion (Hopf.rightMultiplyPair pair rotor)
    ≡ Hopf.pairHopfQuaternion pair
selectedRotorPreservesExistingHopfQuaternion pair =
  Hopf.hopfQuaternionRightUnitInvariant pair rotor rotorHasUnitNorm

selectedRotorPreservesExistingHopfScalar :
  ∀ pair →
  Hopf.pairHopfScalar (Hopf.rightMultiplyPair pair rotor)
    ≡ Hopf.pairHopfScalar pair
selectedRotorPreservesExistingHopfScalar pair =
  Hopf.hopfScalarRightUnitInvariant pair rotor rotorHasUnitNorm

------------------------------------------------------------------------
-- An explicit same-carrier bridge to the existing FINITE quaternion
-- double-cover owner Q8 -> V4.  Our rotor belongs to the larger
-- Hurwitz/binary-tetrahedral group, not to Q8 itself; conjugation by
-- it normalizes Q8 and cyclically permutes i,j,k.  Q8 alone cannot
-- contain this 120-degree rotor.  This distinction is essential.
------------------------------------------------------------------------

basisAsQuaternion : Q8.QuaternionBasis → Q.RationalQuaternion
basisAsQuaternion Q8.basisOne = Q.oneQ
basisAsQuaternion Q8.basisI = Q.quat 0ℚ 1ℚ 0ℚ 0ℚ
basisAsQuaternion Q8.basisJ = Q.quat 0ℚ 0ℚ 1ℚ 0ℚ
basisAsQuaternion Q8.basisK = Q.quat 0ℚ 0ℚ 0ℚ 1ℚ

cycleQuaternionBasis : Q8.QuaternionBasis → Q8.QuaternionBasis
cycleQuaternionBasis Q8.basisOne = Q8.basisOne
cycleQuaternionBasis Q8.basisI = Q8.basisJ
cycleQuaternionBasis Q8.basisJ = Q8.basisK
cycleQuaternionBasis Q8.basisK = Q8.basisI

rotorConjugatesActualQ8Basis :
  (b : Q8.QuaternionBasis) →
  Q._*q_ (Q._*q_ rotor (basisAsQuaternion b)) rotorInverse
    ≡ basisAsQuaternion (cycleQuaternionBasis b)
rotorConjugatesActualQ8Basis Q8.basisOne =
  Q.quaternionExt
    ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀
rotorConjugatesActualQ8Basis Q8.basisI =
  Q.quaternionExt
    ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀
rotorConjugatesActualQ8Basis Q8.basisJ =
  Q.quaternionExt
    ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀
rotorConjugatesActualQ8Basis Q8.basisK =
  Q.quaternionExt
    ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀

cycleV4 : Q8.V4Rotation → Q8.V4Rotation
cycleV4 Q8.identityRotation = Q8.identityRotation
cycleV4 Q8.halfTurnX = Q8.halfTurnY
cycleV4 Q8.halfTurnY = Q8.halfTurnZ
cycleV4 Q8.halfTurnZ = Q8.halfTurnX

cycleBasisDescendsToExistingV4Rotation :
  (b : Q8.QuaternionBasis) →
  Q8.basisRotation (cycleQuaternionBasis b)
    ≡ cycleV4 (Q8.basisRotation b)
cycleBasisDescendsToExistingV4Rotation Q8.basisOne = refl
cycleBasisDescendsToExistingV4Rotation Q8.basisI = refl
cycleBasisDescendsToExistingV4Rotation Q8.basisJ = refl
cycleBasisDescendsToExistingV4Rotation Q8.basisK = refl

cycleV4Cubed : ∀ x →
  cycleV4 (cycleV4 (cycleV4 x)) ≡ x
cycleV4Cubed Q8.identityRotation = refl
cycleV4Cubed Q8.halfTurnX = refl
cycleV4Cubed Q8.halfTurnY = refl
cycleV4Cubed Q8.halfTurnZ = refl

-- To identify this tetrahedral C3 with the *particular* A5
-- 3-cycle used in a 180-coordinate VOA, one still needs the
-- explicit A4 -> A5 permutation embedding and axis transport.
