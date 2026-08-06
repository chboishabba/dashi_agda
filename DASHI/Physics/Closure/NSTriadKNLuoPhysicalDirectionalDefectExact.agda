module DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Zoran Grujić.
-- Title: "A Geometric Measure-Type Regularity Criterion for Solutions to the
-- 3D Navier-Stokes Equations".
-- DOI: 10.1088/0951-7715/26/1/289.
-- arXiv DOI: 10.48550/arXiv.1111.0217.
--
-- PURPOSE
-- Lift the checked unit-direction Gram defect to physical vorticity vectors.
-- If
--
--   omega_x = a xi,   omega_y = b eta,
--
-- with unit xi and eta, then the exact rational identity is
--
--   |omega_x × omega_y|²
--     = a² b² Theta(xi,eta).
--
-- This is the concrete F3.1 bridge between angular coherence and the weighted
-- vorticity interaction; it is not merely a declaration that Theta is a scalar
-- in [0,1].
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram

vec3Ext :
  ∀ {left right : Gram.Vec3} →
  Gram.x left ≡ Gram.x right →
  Gram.y left ≡ Gram.y right →
  Gram.z left ≡ Gram.z right →
  left ≡ right
vec3Ext
  {left = Gram.vec3 leftX leftY leftZ}
  {right = Gram.vec3 .leftX .leftY .leftZ}
  refl refl refl = refl

scaleVec3 : ℚ → Gram.Vec3 → Gram.Vec3
scaleVec3 scalar vector =
  Gram.vec3
    (scalar * Gram.x vector)
    (scalar * Gram.y vector)
    (scalar * Gram.z vector)

crossScaleIdentity :
  (leftScale rightScale : ℚ) →
  (left right : Gram.Vec3) →
  Gram.cross
    (scaleVec3 leftScale left)
    (scaleVec3 rightScale right)
  ≡
  scaleVec3
    (leftScale * rightScale)
    (Gram.cross left right)
crossScaleIdentity leftScale rightScale left right =
  vec3Ext
    (solve
      ( leftScale ∷ rightScale
      ∷ Gram.y left ∷ Gram.z left
      ∷ Gram.y right ∷ Gram.z right
      ∷ []))
    (solve
      ( leftScale ∷ rightScale
      ∷ Gram.z left ∷ Gram.x left
      ∷ Gram.z right ∷ Gram.x right
      ∷ []))
    (solve
      ( leftScale ∷ rightScale
      ∷ Gram.x left ∷ Gram.y left
      ∷ Gram.x right ∷ Gram.y right
      ∷ []))

scaledNormSquared :
  (scalar : ℚ) →
  (vector : Gram.Vec3) →
  Gram.normSquared (scaleVec3 scalar vector)
  ≡ L2.square scalar * Gram.normSquared vector
scaledNormSquared scalar vector =
  solve
    ( scalar
    ∷ Gram.x vector
    ∷ Gram.y vector
    ∷ Gram.z vector
    ∷ [])

scaledCrossNormSquared :
  (leftScale rightScale : ℚ) →
  (left right : Gram.Vec3) →
  Gram.crossNormSquared
    (scaleVec3 leftScale left)
    (scaleVec3 rightScale right)
  ≡
  L2.square leftScale
    * L2.square rightScale
    * Gram.crossNormSquared left right
scaledCrossNormSquared leftScale rightScale left right =
  trans
    (cong Gram.normSquared
      (crossScaleIdentity leftScale rightScale left right))
    (trans
      (scaledNormSquared
        (leftScale * rightScale)
        (Gram.cross left right))
      (solve
        ( leftScale
        ∷ rightScale
        ∷ Gram.crossNormSquared left right
        ∷ [])))

record PhysicalVorticityPair : Set where
  constructor physical-vorticity-pair
  field
    leftAmplitude rightAmplitude : ℚ
    directions : Gram.UnitDirectionPair

open PhysicalVorticityPair public

leftVorticity : PhysicalVorticityPair → Gram.Vec3
leftVorticity pair =
  scaleVec3
    (leftAmplitude pair)
    (Gram.left (directions pair))

rightVorticity : PhysicalVorticityPair → Gram.Vec3
rightVorticity pair =
  scaleVec3
    (rightAmplitude pair)
    (Gram.right (directions pair))

physicalDirectionalDefectIdentity :
  (pair : PhysicalVorticityPair) →
  Gram.crossNormSquared
    (leftVorticity pair)
    (rightVorticity pair)
  ≡
  L2.square (leftAmplitude pair)
    * L2.square (rightAmplitude pair)
    * Gram.directionalDefect (directions pair)
physicalDirectionalDefectIdentity pair =
  trans
    (scaledCrossNormSquared
      (leftAmplitude pair)
      (rightAmplitude pair)
      (Gram.left (directions pair))
      (Gram.right (directions pair)))
    (cong
      (λ defect →
        L2.square (leftAmplitude pair)
        * L2.square (rightAmplitude pair)
        * defect)
      (sym
        (Gram.directionalDefectEqualsCrossSquare
          (directions pair))))

weightedPhysicalDirectionalDefectIdentity :
  (weight : ℚ) →
  (pair : PhysicalVorticityPair) →
  weight
    * Gram.crossNormSquared
        (leftVorticity pair)
        (rightVorticity pair)
  ≡
  weight
    * L2.square (leftAmplitude pair)
    * L2.square (rightAmplitude pair)
    * Gram.directionalDefect (directions pair)
weightedPhysicalDirectionalDefectIdentity weight pair
  rewrite physicalDirectionalDefectIdentity pair =
  solve
    ( weight
    ∷ L2.square (leftAmplitude pair)
    ∷ L2.square (rightAmplitude pair)
    ∷ Gram.directionalDefect (directions pair)
    ∷ [])
