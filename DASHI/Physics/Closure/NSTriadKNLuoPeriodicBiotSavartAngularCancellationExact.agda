module DASHI.Physics.Closure.NSTriadKNLuoPeriodicBiotSavartAngularCancellationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- DASHI CONTRIBUTION
--
-- The physical strain-kernel angular numerator is implemented as
--
--   K(r,omega) = (r cross omega) tensor r
--                + r tensor (r cross omega).
--
-- It is proved exactly to be symmetric, trace-free and even in r.  More
-- importantly, its values on the three coordinate directions cancel:
--
--   K(e1,omega) + K(e2,omega) + K(e3,omega) = 0.
--
-- This is a finite exact spherical-cubature witness for the mean-zero angular
-- structure required by the principal-value strain kernel.  It advances K1
-- beyond the Fourier multiplier, but it is not a construction of the periodic
-- distribution, the continuum spherical integral, or the Calderon-Zygmund
-- estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _≡_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPositiveStrainGradientSignExact as Matrix

matrixExt :
  ∀ {left right : Matrix.Matrix3} →
  Matrix.a11 left ≡ Matrix.a11 right →
  Matrix.a12 left ≡ Matrix.a12 right →
  Matrix.a13 left ≡ Matrix.a13 right →
  Matrix.a21 left ≡ Matrix.a21 right →
  Matrix.a22 left ≡ Matrix.a22 right →
  Matrix.a23 left ≡ Matrix.a23 right →
  Matrix.a31 left ≡ Matrix.a31 right →
  Matrix.a32 left ≡ Matrix.a32 right →
  Matrix.a33 left ≡ Matrix.a33 right →
  left ≡ right
matrixExt
  {left = Matrix.matrix3 l11 l12 l13 l21 l22 l23 l31 l32 l33}
  {right = Matrix.matrix3 .l11 .l12 .l13 .l21 .l22 .l23 .l31 .l32 .l33}
  refl refl refl refl refl refl refl refl refl = refl

zeroMatrix : Matrix.Matrix3
zeroMatrix = Matrix.matrix3 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ

addMatrix : Matrix.Matrix3 → Matrix.Matrix3 → Matrix.Matrix3
addMatrix left right =
  Matrix.matrix3
    (Matrix.a11 left + Matrix.a11 right)
    (Matrix.a12 left + Matrix.a12 right)
    (Matrix.a13 left + Matrix.a13 right)
    (Matrix.a21 left + Matrix.a21 right)
    (Matrix.a22 left + Matrix.a22 right)
    (Matrix.a23 left + Matrix.a23 right)
    (Matrix.a31 left + Matrix.a31 right)
    (Matrix.a32 left + Matrix.a32 right)
    (Matrix.a33 left + Matrix.a33 right)

negVec : Gram.Vec3 → Gram.Vec3
negVec vector =
  Gram.vec3 (- Gram.x vector) (- Gram.y vector) (- Gram.z vector)

kernelNumerator : Gram.Vec3 → Gram.Vec3 → Matrix.Matrix3
kernelNumerator radial vorticity =
  let crossed = Gram.cross radial vorticity
  in
  Matrix.matrix3
    (Gram.x crossed * Gram.x radial + Gram.x radial * Gram.x crossed)
    (Gram.x crossed * Gram.y radial + Gram.x radial * Gram.y crossed)
    (Gram.x crossed * Gram.z radial + Gram.x radial * Gram.z crossed)

    (Gram.y crossed * Gram.x radial + Gram.y radial * Gram.x crossed)
    (Gram.y crossed * Gram.y radial + Gram.y radial * Gram.y crossed)
    (Gram.y crossed * Gram.z radial + Gram.y radial * Gram.z crossed)

    (Gram.z crossed * Gram.x radial + Gram.z radial * Gram.x crossed)
    (Gram.z crossed * Gram.y radial + Gram.z radial * Gram.y crossed)
    (Gram.z crossed * Gram.z radial + Gram.z radial * Gram.z crossed)

kernelSymmetric12 :
  ∀ radial vorticity →
  Matrix.a12 (kernelNumerator radial vorticity)
  ≡ Matrix.a21 (kernelNumerator radial vorticity)
kernelSymmetric12 radial vorticity =
  solve
    ( Gram.x radial ∷ Gram.y radial
    ∷ Gram.x (Gram.cross radial vorticity)
    ∷ Gram.y (Gram.cross radial vorticity)
    ∷ [])

kernelSymmetric13 :
  ∀ radial vorticity →
  Matrix.a13 (kernelNumerator radial vorticity)
  ≡ Matrix.a31 (kernelNumerator radial vorticity)
kernelSymmetric13 radial vorticity =
  solve
    ( Gram.x radial ∷ Gram.z radial
    ∷ Gram.x (Gram.cross radial vorticity)
    ∷ Gram.z (Gram.cross radial vorticity)
    ∷ [])

kernelSymmetric23 :
  ∀ radial vorticity →
  Matrix.a23 (kernelNumerator radial vorticity)
  ≡ Matrix.a32 (kernelNumerator radial vorticity)
kernelSymmetric23 radial vorticity =
  solve
    ( Gram.y radial ∷ Gram.z radial
    ∷ Gram.y (Gram.cross radial vorticity)
    ∷ Gram.z (Gram.cross radial vorticity)
    ∷ [])

radialDotOwnCrossZero :
  ∀ radial vorticity →
  Gram.dot radial (Gram.cross radial vorticity) ≡ 0ℚ
radialDotOwnCrossZero radial vorticity =
  solve
    ( Gram.x radial ∷ Gram.y radial ∷ Gram.z radial
    ∷ Gram.x vorticity ∷ Gram.y vorticity ∷ Gram.z vorticity
    ∷ [])

kernelTraceFree :
  ∀ radial vorticity →
  Matrix.a11 (kernelNumerator radial vorticity)
  + Matrix.a22 (kernelNumerator radial vorticity)
  + Matrix.a33 (kernelNumerator radial vorticity)
  ≡ 0ℚ
kernelTraceFree radial vorticity =
  solve
    ( Gram.x radial ∷ Gram.y radial ∷ Gram.z radial
    ∷ Gram.x vorticity ∷ Gram.y vorticity ∷ Gram.z vorticity
    ∷ [])

kernelEven :
  ∀ radial vorticity →
  kernelNumerator (negVec radial) vorticity
  ≡ kernelNumerator radial vorticity
kernelEven radial vorticity =
  matrixExt
    (solve values) (solve values) (solve values)
    (solve values) (solve values) (solve values)
    (solve values) (solve values) (solve values)
  where
  values =
    Gram.x radial ∷ Gram.y radial ∷ Gram.z radial
    ∷ Gram.x vorticity ∷ Gram.y vorticity ∷ Gram.z vorticity
    ∷ []

e1 e2 e3 : Gram.Vec3
e1 = Gram.vec3 1ℚ 0ℚ 0ℚ
e2 = Gram.vec3 0ℚ 1ℚ 0ℚ
e3 = Gram.vec3 0ℚ 0ℚ 1ℚ

coordinateAngularSum : Gram.Vec3 → Matrix.Matrix3
coordinateAngularSum vorticity =
  addMatrix
    (addMatrix
      (kernelNumerator e1 vorticity)
      (kernelNumerator e2 vorticity))
    (kernelNumerator e3 vorticity)

coordinateAngularCancellation :
  ∀ vorticity → coordinateAngularSum vorticity ≡ zeroMatrix
coordinateAngularCancellation vorticity =
  matrixExt
    (solve values) (solve values) (solve values)
    (solve values) (solve values) (solve values)
    (solve values) (solve values) (solve values)
  where
  values =
    Gram.x vorticity ∷ Gram.y vorticity ∷ Gram.z vorticity ∷ []

record AngularCancellationAuthorityBoundary : Set where
  constructor angularCancellationAuthorityBoundary
  field
    kernelSymmetryProved : Set
    kernelTraceFreeProved : Set
    kernelEvennessProved : Set
    coordinateCubatureCancellationProved : Set
    continuumSphericalMeanZeroProved : Set
    periodicPrincipalValueKernelConstructed : Set

canonicalAngularCancellationAuthorityBoundary :
  AngularCancellationAuthorityBoundary
canonicalAngularCancellationAuthorityBoundary =
  angularCancellationAuthorityBoundary ⊤ ⊤ ⊤ ⊤ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
