module DASHI.Mathematics.Topology.AlexanderHornedSpin360720Exact where

------------------------------------------------------------------------
-- 360-DEGREE SPATIAL IDENTITY VERSUS 720-DEGREE SPINOR RETURN
--
-- Classical owner: Spin(3) = SU(2) -> SO(3), a 2:1 double cover
-- with central kernel {+1,-1}; spin-half U(theta+2pi)=-U(theta)
-- and U(theta+4pi)=U(theta).
--
-- PRIOR DASHI ACTUAL PROOF OWNERS (not recreated):
-- * Algebra.FiniteQuaternionDoubleCover : Q8 -> V4, strict
--   kernel {+1,-1}, exact finite multiplication.
-- * Foundations.SU2SO3IrrepDimensionExact : only even
--   SU2 highest weights descend to SO3, spin-half excluded.
-- * Mathematics.Topology.AlexanderHornedQuaternionC3SpinExact :
--   literal q=(1+i+j+k)/2, q^3=-1, (-q)^3=+1, and
--   conjugation matches the EXACT horn ambient C3 rotation.
-- * Mathematics.Topology.AlexanderHornedC3AmbientRotationExact :
--   exact 120-degree coordinate permutation.
--
-- NEW CONNECTION:
-- the SAME central -1 in the Q8 cover models the endpoint of a
-- lift of the continuous 2pi rotational loop, and (-1)^2=+1
-- models the 4pi return. We prove the strict finite statements
-- and reuse the already built 120-degree quaternion proof.
--
-- STATUS FIREWALL: A central element of finite Q8 is not an
-- actual path in continuous SU2; its interpretation as the
-- endpoint of the 2pi lift requires the continuous cover theorem.
-- No loop of SO3 is identified with pi1 of the horn exterior.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Algebra.FiniteQuaternionDoubleCover as Q8
import DASHI.Foundations.SU2SO3IrrepDimensionExact as SpinDim
import DASHI.Mathematics.Topology.AlexanderHornedQuaternionC3SpinExact as HornSpin
import DASHI.Mathematics.Topology.AlexanderHornedC3AmbientRotationExact as Ambient
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionCoreExact as Q

-- The finite Q8 -> V4 model already knows that +1 and -1 are
-- the TWO different lifts of the identity spatial rotation.
spinAtZero : Q8.Q8
spinAtZero = Q8.plusOne

spinAt360 : Q8.Q8
spinAt360 = Q8.minusOne

spinAt720 : Q8.Q8
spinAt720 = Q8.q8Multiply spinAt360 spinAt360

spatialRotationAt360IsIdentity :
  Q8.rho spinAt360 ≡ Q8.identityRotation
spatialRotationAt360IsIdentity = refl

spatialRotationAt720IsIdentity :
  Q8.rho spinAt720 ≡ Q8.identityRotation
spatialRotationAt720IsIdentity = refl

spinAt360IsNotSpinIdentity : spinAt360 ≡ spinAtZero → ⊥
spinAt360IsNotSpinIdentity eq = Q8.plusMinusDistinct (sym eq)

spinAt720ReturnsToIdentity : spinAt720 ≡ spinAtZero
spinAt720ReturnsToIdentity = refl

-- Two 180deg lifts also produce the central minus sign, even
-- though two 180deg spatial rotations are the identity.
spin180AboutX : Q8.Q8
spin180AboutX = Q8.plusI

twoSpin180TurnsGiveSpin360Sign :
  Q8.q8Multiply spin180AboutX spin180AboutX ≡ spinAt360
twoSpin180TurnsGiveSpin360Sign = refl

twoSpatial180TurnsGiveIdentity :
  Q8.rotationMultiply
    (Q8.rho spin180AboutX) (Q8.rho spin180AboutX)
    ≡ Q8.identityRotation
twoSpatial180TurnsGiveIdentity = refl

-- The EXISTING spin-half highest-weight representation does NOT
-- descend along the SO3 quotient. Exactly this central sign
-- obstructs the descent.
spinHalfDoesNotDescendToSO3 :
  SpinDim.EvenHighestWeight 1 → ⊥
spinHalfDoesNotDescendToSO3 =
  SpinDim.spinorHighestWeightOneDoesNotDescend

-- Horn ambient 120deg spatial rotation: three turns are spatial
-- identity; the SAME chosen quaternion rotor accumulates -1.
hornSpatialThreeTurnsIdentity :
  ∀ {A : Set} (xyz : Ambient.Triple A) →
  Ambient.rotateXYZ
    (Ambient.rotateXYZ (Ambient.rotateXYZ xyz)) ≡ xyz
hornSpatialThreeTurnsIdentity =
  Ambient.rotateXYZCubed

horn120SpinThreeTurnsAreCentralMinusOne :
  Q._*q_ (Q._*q_ HornSpin.rotor HornSpin.rotor)
    HornSpin.rotor ≡ Q.negQ Q.oneQ
horn120SpinThreeTurnsAreCentralMinusOne =
  HornSpin.rotorCubedIsCentralMinusOne

horn120OtherSignedLiftHasOrderThree :
  Q._*q_
    (Q._*q_ HornSpin.negativeRotor HornSpin.negativeRotor)
    HornSpin.negativeRotor ≡ Q.oneQ
horn120OtherSignedLiftHasOrderThree =
  HornSpin.negativeRotorCubedIsOne

-- The *continuous path* from 0 through 120, 240, 360deg
-- selects the q lift and reaches -1. Choosing -q for the SAME
-- final 120deg spatial rotation is a different lift endpoint;
-- its threefold product is +1. The order of a lift is not
-- determined solely by the order of its image.
