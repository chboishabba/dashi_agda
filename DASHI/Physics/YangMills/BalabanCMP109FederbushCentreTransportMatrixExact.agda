module DASHI.Physics.YangMills.BalabanCMP109FederbushCentreTransportMatrixExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Remove the last semantic/matrix ambiguity in the Federbush centre transport.
-- The physical centre transport is
--
--   T(U,V) = Ad_{U V^-1}.
--
-- On the literal {X,Y,Z} Lie carrier its matrix is defined by applying that
-- adjoint action to the three pure-imaginary quaternion basis vectors and
-- reading the corresponding imaginary coordinate.  Thus every matrix entry is
-- definitionally tied to the same quaternion transport used in equation (0.11),
-- not merely to a matrix with the same dimensions or norm bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreTransportPhysicalExact as Transport

basisQuaternion : Physical.LieCoordinate3 → Q.RationalQuaternion
basisQuaternion Physical.coordinateX = Q.quat 0ℚ 1ℚ 0ℚ 0ℚ
basisQuaternion Physical.coordinateY = Q.quat 0ℚ 0ℚ 1ℚ 0ℚ
basisQuaternion Physical.coordinateZ = Q.quat 0ℚ 0ℚ 0ℚ 1ℚ

imaginaryCoordinate : Physical.LieCoordinate3 → Q.RationalQuaternion → ℚ
imaginaryCoordinate Physical.coordinateX value = Q.q1 value
imaginaryCoordinate Physical.coordinateY value = Q.q2 value
imaginaryCoordinate Physical.coordinateZ value = Q.q3 value

centreTransportMatrix :
  Q.RationalQuaternion → Q.RationalQuaternion → Jacobian.Lie3Matrix
centreTransportMatrix input centre row column =
  imaginaryCoordinate row
    (Transport.centreTransportAction input centre (basisQuaternion column))

centreTransportMatrixEntryIsPhysicalAdjoint : ∀ input centre row column →
  centreTransportMatrix input centre row column
  ≡ imaginaryCoordinate row
      (Transport.centreTransportAction input centre (basisQuaternion column))
centreTransportMatrixEntryIsPhysicalAdjoint input centre row column = refl

lieVectorQuaternion : Jacobian.Lie3Vector → Q.RationalQuaternion
lieVectorQuaternion vector =
  Q.quat 0ℚ
    (vector Physical.coordinateX)
    (vector Physical.coordinateY)
    (vector Physical.coordinateZ)

matrixActionCoordinateExact : ∀ input centre vector row →
  Jacobian.matrixApply (centreTransportMatrix input centre) vector row
  ≡ imaginaryCoordinate row
      (Transport.centreTransportAction input centre (lieVectorQuaternion vector))
matrixActionCoordinateExact
    (Q.quat u0 u1 u2 u3)
    (Q.quat v0 v1 v2 v3)
    vector Physical.coordinateX =
  ℚRing.solve-∀
    u0 u1 u2 u3 v0 v1 v2 v3
    (vector Physical.coordinateX)
    (vector Physical.coordinateY)
    (vector Physical.coordinateZ)
matrixActionCoordinateExact
    (Q.quat u0 u1 u2 u3)
    (Q.quat v0 v1 v2 v3)
    vector Physical.coordinateY =
  ℚRing.solve-∀
    u0 u1 u2 u3 v0 v1 v2 v3
    (vector Physical.coordinateX)
    (vector Physical.coordinateY)
    (vector Physical.coordinateZ)
matrixActionCoordinateExact
    (Q.quat u0 u1 u2 u3)
    (Q.quat v0 v1 v2 v3)
    vector Physical.coordinateZ =
  ℚRing.solve-∀
    u0 u1 u2 u3 v0 v1 v2 v3
    (vector Physical.coordinateX)
    (vector Physical.coordinateY)
    (vector Physical.coordinateZ)

centreTransportMatrixDifferenceEntryExact :
  ∀ u v u' v' row column →
  centreTransportMatrix u v row column
    - centreTransportMatrix u' v' row column
  ≡ imaginaryCoordinate row
      (DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact._-q_
        (Transport.centreTransportAction u v (basisQuaternion column))
        (Transport.centreTransportAction u' v' (basisQuaternion column)))
centreTransportMatrixDifferenceEntryExact
    (Q.quat u0 u1 u2 u3)
    (Q.quat v0 v1 v2 v3)
    (Q.quat p0 p1 p2 p3)
    (Q.quat q0 q1 q2 q3)
    Physical.coordinateX column =
  ℚRing.solve-∀
    u0 u1 u2 u3 v0 v1 v2 v3 p0 p1 p2 p3 q0 q1 q2 q3
centreTransportMatrixDifferenceEntryExact
    (Q.quat u0 u1 u2 u3)
    (Q.quat v0 v1 v2 v3)
    (Q.quat p0 p1 p2 p3)
    (Q.quat q0 q1 q2 q3)
    Physical.coordinateY column =
  ℚRing.solve-∀
    u0 u1 u2 u3 v0 v1 v2 v3 p0 p1 p2 p3 q0 q1 q2 q3
centreTransportMatrixDifferenceEntryExact
    (Q.quat u0 u1 u2 u3)
    (Q.quat v0 v1 v2 v3)
    (Q.quat p0 p1 p2 p3)
    (Q.quat q0 q1 q2 q3)
    Physical.coordinateZ column =
  ℚRing.solve-∀
    u0 u1 u2 u3 v0 v1 v2 v3 p0 p1 p2 p3 q0 q1 q2 q3
  where
  open import Data.Rational.Base using (_-_)

cmp109FederbushCentreTransportMatrixIdentificationLevel : ProofLevel
cmp109FederbushCentreTransportMatrixIdentificationLevel = machineChecked

cmp109FederbushCentreTransportMatrixActionLevel : ProofLevel
cmp109FederbushCentreTransportMatrixActionLevel = machineChecked
