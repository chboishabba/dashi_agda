module DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01240221.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Electromagnetic comparison: the same cross-product inverse-curl geometry
-- is the Fourier form of the classical Biot--Savart law.  The static elliptic
-- identity proved here is deliberately not promoted to a dynamical regularity
-- theorem: Euler and Navier--Stokes share this inversion geometry.
--
-- PURPOSE
-- On the repository's exact rational three-vector carrier, define the real
-- amplitude part of the Fourier Biot--Savart operator
--
--   B_k omega = |k|^{-2} (k cross omega).
--
-- The omitted factor i is a Fourier-phase convention.  We prove the Lagrange
-- cross-product identity, transversality, the exact one-derivative norm gain
-- on k-transverse vorticity, and inversion by the phase-corrected curl.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; trans)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V

cross : V.Vector3 → V.Vector3 → V.Vector3
cross (V.v3 ax ay az) (V.v3 bx by bz) =
  V.v3
    (ay * bz - az * by)
    (az * bx - ax * bz)
    (ax * by - ay * bx)

crossOrthogonalLeft :
  (left right : V.Vector3) →
  V.dot left (cross left right) ≡ 0ℚ
crossOrthogonalLeft
  (V.v3 ax ay az) (V.v3 bx by bz) =
  solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])

crossOrthogonalRight :
  (left right : V.Vector3) →
  V.dot right (cross left right) ≡ 0ℚ
crossOrthogonalRight
  (V.v3 ax ay az) (V.v3 bx by bz) =
  solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])

crossNormLagrange :
  (left right : V.Vector3) →
  V.normSquared (cross left right)
  ≡ V.normSquared left * V.normSquared right
    - V.dot left right * V.dot left right
crossNormLagrange
  (V.v3 ax ay az) (V.v3 bx by bz) =
  solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])

doubleCross :
  (left right : V.Vector3) →
  cross left (cross left right)
  ≡ V.subtract
      (V.scale (V.dot left right) left)
      (V.scale (V.normSquared left) right)
doubleCross
  (V.v3 ax ay az) (V.v3 bx by bz) =
  V.vectorExt
    (solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ []))
    (solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ []))
    (solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ []))

crossScaleRight :
  (left right : V.Vector3) →
  (coefficient : ℚ) →
  cross left (V.scale coefficient right)
  ≡ V.scale coefficient (cross left right)
crossScaleRight
  (V.v3 ax ay az) (V.v3 bx by bz) coefficient =
  V.vectorExt
    (solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ coefficient ∷ []))
    (solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ coefficient ∷ []))
    (solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ coefficient ∷ []))

normSquaredScale :
  (coefficient : ℚ) →
  (value : V.Vector3) →
  V.normSquared (V.scale coefficient value)
  ≡ coefficient * coefficient * V.normSquared value
normSquaredScale coefficient (V.v3 vx vy vz) =
  solve (coefficient ∷ vx ∷ vy ∷ vz ∷ [])

biotSavart : V.ProjectionMode → V.Vector3 → V.Vector3
biotSavart modeData omega =
  V.scale
    (V.inverseNormSquared modeData)
    (cross (V.mode modeData) omega)

biotSavartTransverse :
  (modeData : V.ProjectionMode) →
  (omega : V.Vector3) →
  V.dot (V.mode modeData) (biotSavart modeData omega) ≡ 0ℚ
biotSavartTransverse modeData omega =
  begin
    V.dot (V.mode modeData) (biotSavart modeData omega)
  ≡⟨ V.dotScaleRight
       (V.mode modeData)
       (cross (V.mode modeData) omega)
       (V.inverseNormSquared modeData) ⟩
    V.inverseNormSquared modeData
      * V.dot (V.mode modeData) (cross (V.mode modeData) omega)
  ≡⟨ cong
       (V.inverseNormSquared modeData *_)
       (crossOrthogonalLeft (V.mode modeData) omega) ⟩
    V.inverseNormSquared modeData * 0ℚ
  ≡⟨ solve (V.inverseNormSquared modeData ∷ []) ⟩
    0ℚ
  ∎

biotSavartNormGainSquared :
  (modeData : V.ProjectionMode) →
  (omega : V.Vector3) →
  V.dot (V.mode modeData) omega ≡ 0ℚ →
  V.normSquared (biotSavart modeData omega)
  ≡ V.inverseNormSquared modeData * V.normSquared omega
biotSavartNormGainSquared modeData omega transverse =
  begin
    V.normSquared (biotSavart modeData omega)
  ≡⟨ normSquaredScale
       (V.inverseNormSquared modeData)
       (cross (V.mode modeData) omega) ⟩
    V.inverseNormSquared modeData
      * V.inverseNormSquared modeData
      * V.normSquared (cross (V.mode modeData) omega)
  ≡⟨ cong
       (λ crossNorm →
         V.inverseNormSquared modeData
         * V.inverseNormSquared modeData
         * crossNorm)
       (crossNormLagrange (V.mode modeData) omega) ⟩
    V.inverseNormSquared modeData
      * V.inverseNormSquared modeData
      * (V.normSquared (V.mode modeData) * V.normSquared omega
        - V.dot (V.mode modeData) omega
          * V.dot (V.mode modeData) omega)
  ≡⟨ cong
       (λ pairing →
         V.inverseNormSquared modeData
         * V.inverseNormSquared modeData
         * (V.normSquared (V.mode modeData) * V.normSquared omega
           - pairing * pairing))
       transverse ⟩
    V.inverseNormSquared modeData
      * V.inverseNormSquared modeData
      * (V.normSquared (V.mode modeData) * V.normSquared omega
        - 0ℚ * 0ℚ)
  ≡⟨ solve
       ( V.inverseNormSquared modeData
       ∷ V.normSquared (V.mode modeData)
       ∷ V.normSquared omega
       ∷ []) ⟩
    (V.inverseNormSquared modeData
      * V.normSquared (V.mode modeData))
      * (V.inverseNormSquared modeData * V.normSquared omega)
  ≡⟨ cong
       (λ reciprocalProduct →
         reciprocalProduct
           * (V.inverseNormSquared modeData * V.normSquared omega))
       (V.inverseLaw modeData) ⟩
    1ℚ * (V.inverseNormSquared modeData * V.normSquared omega)
  ≡⟨ solve
       ( V.inverseNormSquared modeData
       ∷ V.normSquared omega
       ∷ []) ⟩
    V.inverseNormSquared modeData * V.normSquared omega
  ∎

phaseCorrectedCurl : V.Vector3 → V.Vector3 → V.Vector3
phaseCorrectedCurl mode value =
  V.scale (- 1ℚ) (cross mode value)

phaseCorrectedCurlBiotSavart :
  (modeData : V.ProjectionMode) →
  (omega : V.Vector3) →
  V.dot (V.mode modeData) omega ≡ 0ℚ →
  phaseCorrectedCurl
    (V.mode modeData)
    (biotSavart modeData omega)
  ≡ omega
phaseCorrectedCurlBiotSavart modeData omega transverse =
  let
    modeValue = V.mode modeData
    inverse = V.inverseNormSquared modeData
  in
  begin
    phaseCorrectedCurl modeValue (biotSavart modeData omega)
  ≡⟨ cong (V.scale (- 1ℚ))
       (crossScaleRight modeValue (cross modeValue omega) inverse) ⟩
    V.scale (- 1ℚ) (V.scale inverse (cross modeValue (cross modeValue omega)))
  ≡⟨ cong (λ doubled → V.scale (- 1ℚ) (V.scale inverse doubled))
       (doubleCross modeValue omega) ⟩
    V.scale (- 1ℚ)
      (V.scale inverse
        (V.subtract
          (V.scale (V.dot modeValue omega) modeValue)
          (V.scale (V.normSquared modeValue) omega)))
  ≡⟨ cong
       (λ pairing →
         V.scale (- 1ℚ)
           (V.scale inverse
             (V.subtract
               (V.scale pairing modeValue)
               (V.scale (V.normSquared modeValue) omega))))
       transverse ⟩
    V.scale (- 1ℚ)
      (V.scale inverse
        (V.subtract
          (V.scale 0ℚ modeValue)
          (V.scale (V.normSquared modeValue) omega)))
  ≡⟨ finalCoordinates modeValue inverse omega (V.inverseLaw modeData) ⟩
    omega
  ∎
  where
  finalCoordinates :
    (modeValue : V.Vector3) →
    (inverse : ℚ) →
    (omega : V.Vector3) →
    inverse * V.normSquared modeValue ≡ 1ℚ →
    V.scale (- 1ℚ)
      (V.scale inverse
        (V.subtract
          (V.scale 0ℚ modeValue)
          (V.scale (V.normSquared modeValue) omega)))
    ≡ omega
  finalCoordinates
    (V.v3 kx ky kz) inverse (V.v3 wx wy wz) inverseLaw =
    V.vectorExt
      (coordinateFinal wx)
      (coordinateFinal wy)
      (coordinateFinal wz)
    where
    normMode : ℚ
    normMode = kx * kx + ky * ky + kz * kz

    coordinateFinal :
      (coordinate : ℚ) →
      (- 1ℚ) *
        (inverse *
          (0ℚ - normMode * coordinate))
      ≡ coordinate
    coordinateFinal coordinate =
      trans
        (solve (inverse ∷ normMode ∷ coordinate ∷ []))
        (trans
          (cong (_* coordinate) inverseLaw)
          (solve (coordinate ∷ [])))
