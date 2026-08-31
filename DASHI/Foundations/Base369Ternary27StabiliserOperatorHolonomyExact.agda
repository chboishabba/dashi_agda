module DASHI.Foundations.Base369Ternary27StabiliserOperatorHolonomyExact where

------------------------------------------------------------------------
-- STABILISER-QUALIFIED FIBRE OPERATORS / HOLONOMY LANGUAGE
--
-- Cross-pollinates the exact-base -> stabiliser -> fibre-sector owner into an
-- operator-bearing layer.  The coordinate-permutation stabiliser of the exact
-- interaction base controls which appraisal-fibre permutation generators are
-- admitted.  This is a finite DASHI admissibility convention, not a theorem
-- that physical gauge transport is determined by these stabilisers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Stratification
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as Symmetry
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Foundations.Base369Ternary27StratumStabiliserFibreAdmissibilityExact as Sector

------------------------------------------------------------------------
-- 1. Operator language on one appraisal cube.
------------------------------------------------------------------------

data FibreOperator : Set where
  identityOperator
  swapXYOperator
  rotateXYZOperator
  : FibreOperator

applyOperator : FibreOperator -> Geometry.Ternary27Point -> Geometry.Ternary27Point
applyOperator identityOperator p = p
applyOperator swapXYOperator p = Spectral.swapXY p
applyOperator rotateXYZOperator p = Spectral.rotateXYZ p

------------------------------------------------------------------------
-- 2. Admission is proof-relevant and exact-base dependent.
--
-- full S3 : identity, swap, 3-cycle
-- pair S2 : identity, swap
-- trivial : identity only
------------------------------------------------------------------------

data OperatorAdmitted : Geometry.Ternary27Point -> FibreOperator -> Set where
  admitIdentity : {base : Geometry.Ternary27Point} ->
    OperatorAdmitted base identityOperator
  admitSwapAtS3 : {base : Geometry.Ternary27Point} ->
    Spectral.voxelStabiliser base ≡ Symmetry.fullStabiliserS3 ->
    OperatorAdmitted base swapXYOperator
  admitRotateAtS3 : {base : Geometry.Ternary27Point} ->
    Spectral.voxelStabiliser base ≡ Symmetry.fullStabiliserS3 ->
    OperatorAdmitted base rotateXYZOperator
  admitSwapAtS2 : {base : Geometry.Ternary27Point} ->
    Spectral.voxelStabiliser base ≡ Symmetry.pairStabiliserS2 ->
    OperatorAdmitted base swapXYOperator

positiveCornerSwapAdmitted :
  OperatorAdmitted Geometry.positiveCorner swapXYOperator
positiveCornerSwapAdmitted = admitSwapAtS3 refl

positiveCornerRotateAdmitted :
  OperatorAdmitted Geometry.positiveCorner rotateXYZOperator
positiveCornerRotateAdmitted = admitRotateAtS3 refl

sameSignEdgeSwapAdmitted :
  OperatorAdmitted Sector.sameSignEdge swapXYOperator
sameSignEdgeSwapAdmitted = admitSwapAtS2 refl

------------------------------------------------------------------------
-- 3. Negative admission witnesses.
------------------------------------------------------------------------

oppositeSignEdgeRotateNotAdmitted :
  OperatorAdmitted Sector.oppositeSignEdge rotateXYZOperator -> ⊥
oppositeSignEdgeRotateNotAdmitted ()

oppositeSignEdgeSwapNotAdmitted :
  OperatorAdmitted Sector.oppositeSignEdge swapXYOperator -> ⊥
oppositeSignEdgeSwapNotAdmitted ()

sameSignEdgeRotateNotAdmitted :
  OperatorAdmitted Sector.sameSignEdge rotateXYZOperator -> ⊥
sameSignEdgeRotateNotAdmitted ()

------------------------------------------------------------------------
-- 4. A native base transition can change the admissible operator language.
--
-- (+,-,0)  -- one native step in y -->  (+,0,0)
-- edge-centre / trivial stabiliser        face-centre / S2 stabiliser
------------------------------------------------------------------------

positiveXFace : Geometry.Ternary27Point
positiveXFace = Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero

oppositeEdgeToFaceAdjacent :
  Geometry.HypervoxelAdjacent Sector.oppositeSignEdge positiveXFace
oppositeEdgeToFaceAdjacent = Geometry.adjacentY Geometry.negToZero

oppositeEdgeStratum :
  Stratification.voxelStratum Sector.oppositeSignEdge ≡
  Stratification.edgeCentreStratum
oppositeEdgeStratum = refl

positiveXFaceStratum :
  Stratification.voxelStratum positiveXFace ≡ Stratification.faceCentreStratum
positiveXFaceStratum = refl

positiveXFaceHasS2 :
  Spectral.voxelStabiliser positiveXFace ≡ Symmetry.pairStabiliserS2
positiveXFaceHasS2 = refl

positiveXFaceSwapAdmitted : OperatorAdmitted positiveXFace swapXYOperator
positiveXFaceSwapAdmitted = admitSwapAtS2 refl

------------------------------------------------------------------------
-- 5. Holonomy/order language is itself stabiliser-qualified.
--
-- swap and 3-cycle do not commute on a generic fibre seed, but the pair is
-- jointly admitted only at an S3 base in this finite convention.
------------------------------------------------------------------------

holonomySeed : Geometry.Ternary27Point
holonomySeed =
  Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne

swapThenRotate : Geometry.Ternary27Point
swapThenRotate = applyOperator rotateXYZOperator (applyOperator swapXYOperator holonomySeed)

rotateThenSwap : Geometry.Ternary27Point
rotateThenSwap = applyOperator swapXYOperator (applyOperator rotateXYZOperator holonomySeed)

operatorOrderDefect : swapThenRotate ≡ rotateThenSwap -> ⊥
operatorOrderDefect ()

record AdmissibleHolonomyPair (base : Geometry.Ternary27Point) : Set where
  constructor admissible-holonomy-pair
  field
    first : FibreOperator
    second : FibreOperator
    firstAdmitted : OperatorAdmitted base first
    secondAdmitted : OperatorAdmitted base second

open AdmissibleHolonomyPair public

positiveCornerSwapRotateHolonomy : AdmissibleHolonomyPair Geometry.positiveCorner
positiveCornerSwapRotateHolonomy =
  admissible-holonomy-pair swapXYOperator rotateXYZOperator
    positiveCornerSwapAdmitted positiveCornerRotateAdmitted

sameSignEdgeCannotAdmitSwapRotate :
  (p : AdmissibleHolonomyPair Sector.sameSignEdge) ->
  first p ≡ swapXYOperator ->
  second p ≡ rotateXYZOperator ->
  ⊥
sameSignEdgeCannotAdmitSwapRotate p refl refl =
  sameSignEdgeRotateNotAdmitted (secondAdmitted p)

------------------------------------------------------------------------
-- 6. Boundary.
------------------------------------------------------------------------

record StabiliserOperatorHolonomyBoundary : Set where
  constructor stabiliser-operator-holonomy-boundary
  field
    exactBaseControlsOperatorAdmission : Bool
    coarseStratumAloneControlsOperatorAdmission : Bool
    nativeBaseTransitionMayChangeOperatorLanguage : Bool
    operatorOrderMayMatter : Bool
    everyBaseAdmitsSameHolonomyPair : Bool
    stabiliserAdmissionIsGaugeConnection : Bool
    orderDefectIsGaugeCurvature : Bool

canonicalStabiliserOperatorHolonomyBoundary : StabiliserOperatorHolonomyBoundary
canonicalStabiliserOperatorHolonomyBoundary =
  stabiliser-operator-holonomy-boundary true false true true false false false
