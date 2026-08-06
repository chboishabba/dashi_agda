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
longitudinal projectionData value =
  scale
    (inverseNormSquared projectionData * dot (mode projectionData) value)
    (mode projectionData)

project : ProjectionMode → Vector3 → Vector3
project projectionData value =
  subtract value (longitudinal projectionData value)

dotCommutative : (a b : Vector3) → dot a b ≡ dot b a
dotCommutative (v3 ax ay az) (v3 bx by bz) =
  solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])

dotScaleRight : (a b : Vector3) (c : ℚ) →
  dot a (scale c b) ≡ c * dot a b
dotScaleRight (v3 ax ay az) (v3 bx by bz) c =
  solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ c ∷ [])

projectTransverse : (projectionData : ProjectionMode) (value : Vector3) →
  dot (mode projectionData) (project projectionData value) ≡ 0ℚ
projectTransverse projectionData value =
  begin
    dot (mode projectionData) (project projectionData value)
  ≡⟨ componentExpansion ⟩
    dot (mode projectionData) value
      * (1ℚ - inverseNormSquared projectionData
          * normSquared (mode projectionData))
  ≡⟨ cong
       (λ factor → dot (mode projectionData) value * (1ℚ - factor))
       (inverseLaw projectionData) ⟩
    dot (mode projectionData) value * (1ℚ - 1ℚ)
  ≡⟨ solve (dot (mode projectionData) value ∷ []) ⟩
    0ℚ
  ∎
  where
  componentExpansion :
    dot (mode projectionData) (project projectionData value)
    ≡ dot (mode projectionData) value
      * (1ℚ - inverseNormSquared projectionData
          * normSquared (mode projectionData))
  componentExpansion with mode projectionData | value
  ... | v3 mx my mz | v3 vx vy vz =
    solve (mx ∷ my ∷ mz ∷ vx ∷ vy ∷ vz
      ∷ inverseNormSquared projectionData ∷ [])

projectFixesTransverse :
  (projectionData : ProjectionMode) (value : Vector3) →
  dot (mode projectionData) value ≡ 0ℚ →
  project projectionData value ≡ value
projectFixesTransverse projectionData value transverse
  with mode projectionData | value
... | v3 mx my mz | v3 vx vy vz
  rewrite transverse =
  vectorExt
    (solve (vx ∷ mx ∷ inverseNormSquared projectionData ∷ []))
    (solve (vy ∷ my ∷ inverseNormSquared projectionData ∷ []))
    (solve (vz ∷ mz ∷ inverseNormSquared projectionData ∷ []))

projectIdempotent : (projectionData : ProjectionMode) (value : Vector3) →
  project projectionData (project projectionData value)
  ≡ project projectionData value
projectIdempotent projectionData value =
  projectFixesTransverse projectionData (project projectionData value)
    (projectTransverse projectionData value)

projectPlusLongitudinal :
  (projectionData : ProjectionMode) (value : Vector3) →
  add (project projectionData value) (longitudinal projectionData value)
  ≡ value
projectPlusLongitudinal projectionData value
  with mode projectionData | value
... | v3 mx my mz | v3 vx vy vz =
  vectorExt
    (solve (vx ∷ mx ∷ my ∷ mz ∷ vy ∷ vz
      ∷ inverseNormSquared projectionData ∷ []))
    (solve (vy ∷ mx ∷ my ∷ mz ∷ vx ∷ vz
      ∷ inverseNormSquared projectionData ∷ []))
    (solve (vz ∷ mx ∷ my ∷ mz ∷ vx ∷ vy
      ∷ inverseNormSquared projectionData ∷ []))

projectLongitudinalOrthogonal :
  (projectionData : ProjectionMode) (value : Vector3) →
  dot (project projectionData value) (longitudinal projectionData value)
  ≡ 0ℚ
projectLongitudinalOrthogonal projectionData value =
  begin
    dot (project projectionData value) (longitudinal projectionData value)
  ≡⟨ dotScaleRight
       (project projectionData value)
       (mode projectionData)
       (inverseNormSquared projectionData
         * dot (mode projectionData) value) ⟩
    (inverseNormSquared projectionData * dot (mode projectionData) value)
      * dot (project projectionData value) (mode projectionData)
  ≡⟨ cong
       ((inverseNormSquared projectionData
         * dot (mode projectionData) value) *_)
       (Eq.trans
         (dotCommutative (project projectionData value) (mode projectionData))
         (projectTransverse projectionData value)) ⟩
    (inverseNormSquared projectionData * dot (mode projectionData) value)
      * 0ℚ
  ≡⟨ solve
       (inverseNormSquared projectionData
       ∷ dot (mode projectionData) value
       ∷ []) ⟩
    0ℚ
  ∎

normAddExpansion : (a b : Vector3) →
  normSquared (add a b)
  ≡ normSquared a + normSquared b + (dot a b + dot a b)
normAddExpansion (v3 ax ay az) (v3 bx by bz) =
  solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])

projectPythagorean :
  (projectionData : ProjectionMode) (value : Vector3) →
  normSquared value
  ≡ normSquared (project projectionData value)
    + normSquared (longitudinal projectionData value)
projectPythagorean projectionData value =
  begin
    normSquared value
  ≡⟨ cong normSquared (sym (projectPlusLongitudinal projectionData value)) ⟩
    normSquared
      (add (project projectionData value) (longitudinal projectionData value))
  ≡⟨ normAddExpansion
       (project projectionData value)
       (longitudinal projectionData value) ⟩
    normSquared (project projectionData value)
      + normSquared (longitudinal projectionData value)
      + (dot (project projectionData value)
          (longitudinal projectionData value)
        + dot (project projectionData value)
          (longitudinal projectionData value))
  ≡⟨ cong
       (λ cross → normSquared (project projectionData value)
         + normSquared (longitudinal projectionData value)
         + (cross + cross))
       (projectLongitudinalOrthogonal projectionData value) ⟩
    normSquared (project projectionData value)
      + normSquared (longitudinal projectionData value)
      + (0ℚ + 0ℚ)
  ≡⟨ solve
       (normSquared (project projectionData value)
       ∷ normSquared (longitudinal projectionData value)
       ∷ []) ⟩
    normSquared (project projectionData value)
      + normSquared (longitudinal projectionData value)
  ∎

normSquaredNonnegative : (value : Vector3) → 0ℚ ≤ normSquared value
normSquaredNonnegative (v3 vx vy vz) =
  L2.addNonnegative
    (L2.addNonnegative
      (L2.squareNonnegative vx)
      (L2.squareNonnegative vy))
    (L2.squareNonnegative vz)

projectContractionSquared :
  (projectionData : ProjectionMode) (value : Vector3) →
  normSquared (project projectionData value) ≤ normSquared value
projectContractionSquared projectionData value =
  subst
    (λ upper → normSquared (project projectionData value) ≤ upper)
    (sym (projectPythagorean projectionData value))
    (subst
      (λ lower →
        lower
        ≤ normSquared (project projectionData value)
          + normSquared (longitudinal projectionData value))
      (ℚₚ.+-identityʳ (normSquared (project projectionData value)))
      (ℚₚ.+-monoʳ-≤
        (normSquared (project projectionData value))
        (normSquaredNonnegative (longitudinal projectionData value))))

rationalLerayProjectionClosed : Bool
rationalLerayProjectionClosed = true

rationalLerayProjectionClosedIsTrue :
  rationalLerayProjectionClosed ≡ true
rationalLerayProjectionClosedIsTrue = refl
