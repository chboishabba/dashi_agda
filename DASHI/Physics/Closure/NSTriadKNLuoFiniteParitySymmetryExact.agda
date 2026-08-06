module DASHI.Physics.Closure.NSTriadKNLuoFiniteParitySymmetryExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Alexandros Alexakis.
-- Title: "Symmetries of the Navier--Stokes Equations" (course notes,
-- Fluid Dynamics and Turbulence, ENS Paris, 2024).
-- DOI: none assigned to the cited course notes.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- PURPOSE
-- Formalize the exact finite parity transformation used by the centered and
-- triadic lanes.  Simultaneous reflection
--
--   k -> -k,  u -> -u
--
-- preserves dot products, squared norms, incompressibility and three-mode
-- resonance.  This validates parity as a symmetry of the finite geometric
-- data; it does not imply that each nonlinear Fourier pair cancels.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (0ℚ; _+_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V

reflect : V.Vector3 → V.Vector3
reflect (V.v3 vx vy vz) = V.v3 (- vx) (- vy) (- vz)

reflectionInvolutive :
  (value : V.Vector3) →
  reflect (reflect value) ≡ value
reflectionInvolutive (V.v3 vx vy vz) =
  V.vectorExt (solve (vx ∷ [])) (solve (vy ∷ [])) (solve (vz ∷ []))

reflectionPreservesDot :
  (left right : V.Vector3) →
  V.dot (reflect left) (reflect right) ≡ V.dot left right
reflectionPreservesDot
  (V.v3 lx ly lz) (V.v3 rx ry rz) =
  solve (lx ∷ ly ∷ lz ∷ rx ∷ ry ∷ rz ∷ [])

reflectionPreservesNormSquared :
  (value : V.Vector3) →
  V.normSquared (reflect value) ≡ V.normSquared value
reflectionPreservesNormSquared value =
  reflectionPreservesDot value value

reflectionPreservesTransversality :
  (mode velocity : V.Vector3) →
  V.dot mode velocity ≡ 0ℚ →
  V.dot (reflect mode) (reflect velocity) ≡ 0ℚ
reflectionPreservesTransversality mode velocity transverse =
  trans
    (reflectionPreservesDot mode velocity)
    transverse

reflectionDistributesOverAdd :
  (left right : V.Vector3) →
  reflect (V.add left right)
  ≡ V.add (reflect left) (reflect right)
reflectionDistributesOverAdd
  (V.v3 lx ly lz) (V.v3 rx ry rz) =
  V.vectorExt
    (solve (lx ∷ rx ∷ []))
    (solve (ly ∷ ry ∷ []))
    (solve (lz ∷ rz ∷ []))

reflectionPreservesTriadResonance :
  (k p q : V.Vector3) →
  V.add (V.add k p) q ≡ V.v3 0ℚ 0ℚ 0ℚ →
  V.add (V.add (reflect k) (reflect p)) (reflect q)
  ≡ V.v3 0ℚ 0ℚ 0ℚ
reflectionPreservesTriadResonance
  (V.v3 kx ky kz)
  (V.v3 px py pz)
  (V.v3 qx qy qz)
  resonance =
  let
    xZero : kx + px + qx ≡ 0ℚ
    yZero : ky + py + qy ≡ 0ℚ
    zZero : kz + pz + qz ≡ 0ℚ
    xZero = cong V.x resonance
    yZero = cong V.y resonance
    zZero = cong V.z resonance

    reflectedXZero : -(kx + px + qx) ≡ 0ℚ
    reflectedXZero = trans (cong -_ xZero) (solve [])

    reflectedYZero : -(ky + py + qy) ≡ 0ℚ
    reflectedYZero = trans (cong -_ yZero) (solve [])

    reflectedZZero : -(kz + pz + qz) ≡ 0ℚ
    reflectedZZero = trans (cong -_ zZero) (solve [])
  in
  V.vectorExt
    (trans (solve (kx ∷ px ∷ qx ∷ [])) reflectedXZero)
    (trans (solve (ky ∷ py ∷ qy ∷ [])) reflectedYZero)
    (trans (solve (kz ∷ pz ∷ qz ∷ [])) reflectedZZero)
