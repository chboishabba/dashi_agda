module DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- PURPOSE
-- Prove the literal three-dimensional Leray projection algebra over exact
-- rationals.  For a mode m carrying inv*|m|^2=1, define
--
--   P_m v = v - inv (m dot v) m.
--
-- Transversality, fixing of transverse vectors, idempotence, orthogonal
-- decomposition and squared contraction are all derived from this formula.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; subst; sym; trans)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record Vector3 : Set where
  constructor v3
  field x y z : ℚ
open Vector3 public

vectorExt : ∀ {a b : Vector3} →
  x a ≡ x b → y a ≡ y b → z a ≡ z b → a ≡ b
vectorExt {v3 ax ay az} {v3 .ax .ay .az} refl refl refl = refl

scale : ℚ → Vector3 → Vector3
scale c (v3 vx vy vz) = v3 (c * vx) (c * vy) (c * vz)

add : Vector3 → Vector3 → Vector3
add (v3 ax ay az) (v3 bx by bz) =
  v3 (ax + bx) (ay + by) (az + bz)

subtract : Vector3 → Vector3 → Vector3
subtract (v3 ax ay az) (v3 bx by bz) =
  v3 (ax - bx) (ay - by) (az - bz)

dot : Vector3 → Vector3 → ℚ
dot (v3 ax ay az) (v3 bx by bz) =
  ax * bx + ay * by + az * bz

normSquared : Vector3 → ℚ
normSquared value = dot value value

record ProjectionMode : Set where
  constructor projection-mode
  field
    mode : Vector3
    inverseNormSquared : ℚ
    inverseLaw : inverseNormSquared * normSquared mode ≡ 1ℚ
open ProjectionMode public

longitudinal : ProjectionMode → Vector3 → Vector3
longitudinal data value =
  scale (inverseNormSquared data * dot (mode data) value) (mode data)

project : ProjectionMode → Vector3 → Vector3
project data value = subtract value (longitudinal data value)

dotCommutative : (a b : Vector3) → dot a b ≡ dot b a
dotCommutative (v3 ax ay az) (v3 bx by bz) =
  solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])

dotScaleRight : (a b : Vector3) (c : ℚ) →
  dot a (scale c b) ≡ c * dot a b
dotScaleRight (v3 ax ay az) (v3 bx by bz) c =
  solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ c ∷ [])

projectTransverse : (data : ProjectionMode) (value : Vector3) →
  dot (mode data) (project data value) ≡ 0ℚ
projectTransverse data value =
  begin
    dot (mode data) (project data value)
  ≡⟨ componentExpansion ⟩
    dot (mode data) value
      * (1ℚ - inverseNormSquared data * normSquared (mode data))
  ≡⟨ cong
       (λ factor → dot (mode data) value * (1ℚ - factor))
       (inverseLaw data) ⟩
    dot (mode data) value * (1ℚ - 1ℚ)
  ≡⟨ solve (dot (mode data) value ∷ []) ⟩
    0ℚ
  ∎
  where
  componentExpansion :
    dot (mode data) (project data value)
    ≡ dot (mode data) value
      * (1ℚ - inverseNormSquared data * normSquared (mode data))
  componentExpansion with mode data | value
  ... | v3 mx my mz | v3 vx vy vz =
    solve (mx ∷ my ∷ mz ∷ vx ∷ vy ∷ vz
      ∷ inverseNormSquared data ∷ [])

projectFixesTransverse : (data : ProjectionMode) (value : Vector3) →
  dot (mode data) value ≡ 0ℚ → project data value ≡ value
projectFixesTransverse data value transverse
  with mode data | value
... | v3 mx my mz | v3 vx vy vz
  rewrite transverse =
  vectorExt
    (solve (vx ∷ mx ∷ inverseNormSquared data ∷ []))
    (solve (vy ∷ my ∷ inverseNormSquared data ∷ []))
    (solve (vz ∷ mz ∷ inverseNormSquared data ∷ []))

projectIdempotent : (data : ProjectionMode) (value : Vector3) →
  project data (project data value) ≡ project data value
projectIdempotent data value =
  projectFixesTransverse data (project data value)
    (projectTransverse data value)

projectPlusLongitudinal : (data : ProjectionMode) (value : Vector3) →
  add (project data value) (longitudinal data value) ≡ value
projectPlusLongitudinal data value
  with mode data | value
... | v3 mx my mz | v3 vx vy vz =
  vectorExt
    (solve (vx ∷ mx ∷ my ∷ mz ∷ vy ∷ vz
      ∷ inverseNormSquared data ∷ []))
    (solve (vy ∷ mx ∷ my ∷ mz ∷ vx ∷ vz
      ∷ inverseNormSquared data ∷ []))
    (solve (vz ∷ mx ∷ my ∷ mz ∷ vx ∷ vy
      ∷ inverseNormSquared data ∷ []))

projectLongitudinalOrthogonal : (data : ProjectionMode) (value : Vector3) →
  dot (project data value) (longitudinal data value) ≡ 0ℚ
projectLongitudinalOrthogonal data value =
  begin
    dot (project data value) (longitudinal data value)
  ≡⟨ dotScaleRight (project data value) (mode data)
       (inverseNormSquared data * dot (mode data) value) ⟩
    (inverseNormSquared data * dot (mode data) value)
      * dot (project data value) (mode data)
  ≡⟨ cong
       ((inverseNormSquared data * dot (mode data) value) *_)
       (Eq.trans
         (dotCommutative (project data value) (mode data))
         (projectTransverse data value)) ⟩
    (inverseNormSquared data * dot (mode data) value) * 0ℚ
  ≡⟨ solve (inverseNormSquared data ∷ dot (mode data) value ∷ []) ⟩
    0ℚ
  ∎

normAddExpansion : (a b : Vector3) →
  normSquared (add a b)
  ≡ normSquared a + normSquared b + (dot a b + dot a b)
normAddExpansion (v3 ax ay az) (v3 bx by bz) =
  solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])

projectPythagorean : (data : ProjectionMode) (value : Vector3) →
  normSquared value
  ≡ normSquared (project data value) + normSquared (longitudinal data value)
projectPythagorean data value =
  begin
    normSquared value
  ≡⟨ cong normSquared (sym (projectPlusLongitudinal data value)) ⟩
    normSquared (add (project data value) (longitudinal data value))
  ≡⟨ normAddExpansion (project data value) (longitudinal data value) ⟩
    normSquared (project data value) + normSquared (longitudinal data value)
      + (dot (project data value) (longitudinal data value)
        + dot (project data value) (longitudinal data value))
  ≡⟨ cong
       (λ cross → normSquared (project data value)
         + normSquared (longitudinal data value) + (cross + cross))
       (projectLongitudinalOrthogonal data value) ⟩
    normSquared (project data value) + normSquared (longitudinal data value)
      + (0ℚ + 0ℚ)
  ≡⟨ solve (normSquared (project data value)
      ∷ normSquared (longitudinal data value) ∷ []) ⟩
    normSquared (project data value) + normSquared (longitudinal data value)
  ∎

normSquaredNonnegative : (value : Vector3) → 0ℚ ≤ normSquared value
normSquaredNonnegative (v3 vx vy vz) =
  L2.addNonnegative
    (L2.addNonnegative (L2.squareNonnegative vx) (L2.squareNonnegative vy))
    (L2.squareNonnegative vz)

projectContractionSquared : (data : ProjectionMode) (value : Vector3) →
  normSquared (project data value) ≤ normSquared value
projectContractionSquared data value =
  subst
    (λ upper → normSquared (project data value) ≤ upper)
    (sym (projectPythagorean data value))
    (subst
      (λ lower → lower ≤ normSquared (project data value)
        + normSquared (longitudinal data value))
      (ℚₚ.+-identityʳ (normSquared (project data value)))
      (ℚₚ.+-monoʳ-≤
        (normSquared (project data value))
        (normSquaredNonnegative (longitudinal data value))))

rationalLerayProjectionClosed : Bool
rationalLerayProjectionClosed = true

rationalLerayProjectionClosedIsTrue :
  rationalLerayProjectionClosed ≡ true
rationalLerayProjectionClosedIsTrue = refl
