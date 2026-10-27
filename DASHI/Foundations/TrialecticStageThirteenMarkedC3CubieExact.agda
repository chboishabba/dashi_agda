module DASHI.Foundations.TrialecticStageThirteenMarkedC3CubieExact where

------------------------------------------------------------------------
-- Stage-13 marked triple / C3 cubie max-cut.
-- Reuses existing Stage 10/11/12, J marked unit, and ternary 27 geometry.
-- Stage-13 is a NEW proposed typed semantic realization, not a consequence
-- of rank 13 alone and not a claim of physical/Monster action recognition.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Foundations.JPlusOneScaleBridge as J
import DASHI.Foundations.StageAtlasZeroToTwelve as Stage
import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cubie
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral

-- Stage indices and marked local-unit counts do not identify underlying
-- semantic carriers. This numeric bridge is the explicit successor receipt.
stage13Index : Nat
stage13Index = J.tenJ + 3 * J.jBasisUnit

stage13IsThirteen : stage13Index ≡ 13
stage13IsThirteen = refl

stage13AfterStage12 : Stage.toNat Stage.stage-12 + J.jBasisUnit ≡ stage13Index
stage13AfterStage12 = refl

-- Three independently assignable signed units, using the existing cubie.
Stage13MarkedTriple : Set
Stage13MarkedTriple = Cubie.Ternary27Point

stage13Rotate : Stage13MarkedTriple → Stage13MarkedTriple
stage13Rotate = Spectral.rotateXYZ

stage13Reflect : Stage13MarkedTriple → Stage13MarkedTriple
stage13Reflect = Spectral.swapXY

stage13RotationOrderThree :
  (point : Stage13MarkedTriple) →
  stage13Rotate (stage13Rotate (stage13Rotate point)) ≡ point
stage13RotationOrderThree = Spectral.rotateXYZOrderThree

stage13ReflectionInvolutive :
  (point : Stage13MarkedTriple) →
  stage13Reflect (stage13Reflect point) ≡ point
stage13ReflectionInvolutive = Spectral.swapXYInvolutive

-- The permutation generators satisfy the S3 conjugacy relation.
stage13ReflectionConjugatesRotation :
  (point : Stage13MarkedTriple) →
  stage13Reflect (stage13Rotate (stage13Reflect point))
  ≡ stage13Rotate (stage13Rotate point)
stage13ReflectionConjugatesRotation (Cubie.ternary27Point x y z) = refl

-- Actual equivariant representation into the canonical 27-cubie owner.
stage13CubieObserver : Stage13MarkedTriple → Cubie.Ternary27Point
stage13CubieObserver point = point

stage13CubieObserverEquivariant :
  (point : Stage13MarkedTriple) →
  stage13CubieObserver (stage13Rotate point)
  ≡ Spectral.rotateXYZ (stage13CubieObserver point)
stage13CubieObserverEquivariant point = refl

-- Distinguished extremal cubie: fixed point, not a free C3 torsor.
stage13ExtremalCubie : Stage13MarkedTriple
stage13ExtremalCubie = Cubie.positiveCorner

stage13ExtremalCubieFixed :
  stage13Rotate stage13ExtremalCubie ≡ stage13ExtremalCubie
stage13ExtremalCubieFixed = Spectral.positiveCornerFixedByRotation

-- A nonconstant triple has a genuinely moving C3 orbit.
stage13MovingCubie : Stage13MarkedTriple
stage13MovingCubie =
  Cubie.ternary27Point Trit.sspNegOne Trit.sspZero Trit.sspPosOne

stage13MovingCubieNotFixed :
  stage13Rotate stage13MovingCubie ≡ stage13MovingCubie → ⊥
stage13MovingCubieNotFixed ()

-- No inverse identification between numeric rank address, semantic stage,
-- modular j-invariant or the entire signed-SSP/FRACTRAN execution state.
