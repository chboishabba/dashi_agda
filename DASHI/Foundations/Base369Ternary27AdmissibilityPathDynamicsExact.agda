module DASHI.Foundations.Base369Ternary27AdmissibilityPathDynamicsExact where

------------------------------------------------------------------------
-- PATH-INDEXED ADMISSIBLE OPERATOR CONES
--
-- The exact interaction-base path controls which fibre operators are admitted.
-- A native path can therefore gain or lose transport generators without any
-- claim that this finite admission calculus is a physical gauge connection.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27StratumStabiliserFibreAdmissibilityExact as Sector
import DASHI.Foundations.Base369Ternary27StabiliserOperatorHolonomyExact as Operator
import DASHI.Foundations.Base369Ternary27OperatorOrbitQuotientExact as Orbit

------------------------------------------------------------------------
-- 1. A literal native two-edge base path.
--
-- (+,-,0) -> (+,0,0) -> (0,0,0)
-- trivial       S2          S3
------------------------------------------------------------------------

record BasePath3 : Set where
  constructor base-path3
  field
    b0 b1 b2 : Geometry.Ternary27Point
    step01 : Geometry.HypervoxelAdjacent b0 b1
    step12 : Geometry.HypervoxelAdjacent b1 b2
open BasePath3 public

canonicalAdmissionPath : BasePath3
canonicalAdmissionPath =
  base-path3
    Sector.oppositeSignEdge
    Operator.positiveXFace
    Geometry.origin
    Operator.oppositeEdgeToFaceAdjacent
    (Geometry.adjacentX Geometry.posToZero)

------------------------------------------------------------------------
-- 2. The operator/orbit language grows along this finite path.
------------------------------------------------------------------------

path0OrbitLanguage :
  Orbit.orbitLanguageAtBase (b0 canonicalAdmissionPath) ≡
  Orbit.identityOnlyOrbit
path0OrbitLanguage = refl

path1OrbitLanguage :
  Orbit.orbitLanguageAtBase (b1 canonicalAdmissionPath) ≡
  Orbit.swapGeneratedOrbit
path1OrbitLanguage = refl

path2OrbitLanguage :
  Orbit.orbitLanguageAtBase (b2 canonicalAdmissionPath) ≡
  Orbit.swapRotateGeneratedOrbit
path2OrbitLanguage = refl

firstTransitionChangesCone :
  Orbit.orbitLanguageAtBase (b0 canonicalAdmissionPath) ≡
  Orbit.orbitLanguageAtBase (b1 canonicalAdmissionPath) → ⊥
firstTransitionChangesCone ()

secondTransitionChangesCone :
  Orbit.orbitLanguageAtBase (b1 canonicalAdmissionPath) ≡
  Orbit.orbitLanguageAtBase (b2 canonicalAdmissionPath) → ⊥
secondTransitionChangesCone ()

------------------------------------------------------------------------
-- 3. Generator gain is proof-relevant.
------------------------------------------------------------------------

swapUnavailableAtPath0 :
  Operator.OperatorAdmitted
    (b0 canonicalAdmissionPath)
    Operator.swapXYOperator → ⊥
swapUnavailableAtPath0 = Operator.oppositeSignEdgeSwapNotAdmitted

swapAvailableAtPath1 :
  Operator.OperatorAdmitted
    (b1 canonicalAdmissionPath)
    Operator.swapXYOperator
swapAvailableAtPath1 = Operator.positiveXFaceSwapAdmitted

rotateUnavailableAtPath1 :
  Operator.OperatorAdmitted
    (b1 canonicalAdmissionPath)
    Operator.rotateXYZOperator → ⊥
rotateUnavailableAtPath1 ()

rotateAvailableAtPath2 :
  Operator.OperatorAdmitted
    (b2 canonicalAdmissionPath)
    Operator.rotateXYZOperator
rotateAvailableAtPath2 = Operator.admitRotateAtS3 refl

------------------------------------------------------------------------
-- 4. The noncommuting swap/rotate pair becomes jointly admissible only at the
--    final S3 point of this specimen path.
------------------------------------------------------------------------

finalHolonomyPair :
  Operator.AdmissibleHolonomyPair (b2 canonicalAdmissionPath)
finalHolonomyPair =
  Operator.admissible-holonomy-pair
    Operator.swapXYOperator
    Operator.rotateXYZOperator
    (Operator.admitSwapAtS3 refl)
    (Operator.admitRotateAtS3 refl)

middleCannotAdmitCanonicalHolonomyPair :
  Operator.AdmissibleHolonomyPair (b1 canonicalAdmissionPath) →
  (λ pair →
    Operator.first pair ≡ Operator.swapXYOperator →
    Operator.second pair ≡ Operator.rotateXYZOperator →
    ⊥)
middleCannotAdmitCanonicalHolonomyPair pair refl refl =
  rotateUnavailableAtPath1 (Operator.secondAdmitted pair)

------------------------------------------------------------------------
-- 5. Boundary.
------------------------------------------------------------------------

record AdmissibilityPathDynamicsBoundary : Set where
  constructor admissibility-path-dynamics-boundary
  field
    operatorConeIsBaseIndexed : Bool
    nativePathMayGainGenerators : Bool
    nativePathMayChangeOrbitLanguage : Bool
    admissibleHolonomyLanguageMayChangeAlongPath : Bool
    allBasePointsHaveSameOperatorCone : Bool
    pathAdmissionIsPhysicalGaugeConnection : Bool
    gainOfGeneratorProvesCurvature : Bool

canonicalAdmissibilityPathDynamicsBoundary : AdmissibilityPathDynamicsBoundary
canonicalAdmissibilityPathDynamicsBoundary =
  admissibility-path-dynamics-boundary
    true true true true false false false
