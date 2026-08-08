module DASHI.Physics.YangMills.BalabanWilsonSixteenAtomCentredProbeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Generalize the three-sector centred-probe identity used in the Monster lane
-- to the literal sixteen Wilson second-variation placements.  If
--
--   a_i = b + delta_i,
--
-- then, without division,
--
--   16 sum_i w_i a_i
--     = (sum_i w_i)(16 b + sum_i delta_i)
--       + sum_i (16 w_i - sum_j w_j) delta_i.
--
-- The first term is the augmentation/uniform-placement channel.  The second
-- is the complete centred correlation defect.  Uniform weights annihilate the
-- centred coefficients exactly.  This is finite rational algebra only; it does
-- not assert that a particular physical Wilson coefficient is optimal.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record Vector16 : Set where
  constructor vector16
  field
    v00 v01 v02 v03 : ℚ
    v04 v05 v06 v07 : ℚ
    v08 v09 v10 v11 : ℚ
    v12 v13 v14 v15 : ℚ

open Vector16 public

map16 : (ℚ → ℚ) → Vector16 → Vector16
map16 f values = vector16
  (f (v00 values)) (f (v01 values))
  (f (v02 values)) (f (v03 values))
  (f (v04 values)) (f (v05 values))
  (f (v06 values)) (f (v07 values))
  (f (v08 values)) (f (v09 values))
  (f (v10 values)) (f (v11 values))
  (f (v12 values)) (f (v13 values))
  (f (v14 values)) (f (v15 values))

zipWith16 : (ℚ → ℚ → ℚ) → Vector16 → Vector16 → Vector16
zipWith16 f left right = vector16
  (f (v00 left) (v00 right)) (f (v01 left) (v01 right))
  (f (v02 left) (v02 right)) (f (v03 left) (v03 right))
  (f (v04 left) (v04 right)) (f (v05 left) (v05 right))
  (f (v06 left) (v06 right)) (f (v07 left) (v07 right))
  (f (v08 left) (v08 right)) (f (v09 left) (v09 right))
  (f (v10 left) (v10 right)) (f (v11 left) (v11 right))
  (f (v12 left) (v12 right)) (f (v13 left) (v13 right))
  (f (v14 left) (v14 right)) (f (v15 left) (v15 right))

sum16 : Vector16 → ℚ
sum16 values =
  v00 values + v01 values + v02 values + v03 values
  + v04 values + v05 values + v06 values + v07 values
  + v08 values + v09 values + v10 values + v11 values
  + v12 values + v13 values + v14 values + v15 values

weightedSum16 : Vector16 → Vector16 → ℚ
weightedSum16 weights values =
  sum16 (zipWith16 _*_ weights values)

constant16 : ℚ → Vector16
constant16 value = vector16
  value value value value value value value value
  value value value value value value value value

addBase16 : ℚ → Vector16 → Vector16
addBase16 base defects = map16 (base +_) defects

sixteen : ℚ
sixteen = + 16

centredWeight16 : Vector16 → Vector16
centredWeight16 weights =
  map16 (λ weight → sixteen * weight - sum16 weights) weights

centredDefectProbe16 : Vector16 → Vector16 → ℚ
centredDefectProbe16 weights defects =
  weightedSum16 (centredWeight16 weights) defects

sixteenAtomCentredProbeExact : ∀ base weights defects →
  sixteen * weightedSum16 weights (addBase16 base defects)
  ≡ sum16 weights * (sixteen * base + sum16 defects)
    + centredDefectProbe16 weights defects
sixteenAtomCentredProbeExact base
    (vector16 w00 w01 w02 w03 w04 w05 w06 w07
      w08 w09 w10 w11 w12 w13 w14 w15)
    (vector16 d00 d01 d02 d03 d04 d05 d06 d07
      d08 d09 d10 d11 d12 d13 d14 d15) =
  ℚRing.solve-∀
    base
    w00 w01 w02 w03 w04 w05 w06 w07
    w08 w09 w10 w11 w12 w13 w14 w15
    d00 d01 d02 d03 d04 d05 d06 d07
    d08 d09 d10 d11 d12 d13 d14 d15

uniformWeightCentredCoefficientZero : ∀ weight →
  centredWeight16 (constant16 weight)
  ≡ constant16 (+ 0)
uniformWeightCentredCoefficientZero weight =
  Vector16-ext
    (ℚRing.solve-∀ weight) (ℚRing.solve-∀ weight)
    (ℚRing.solve-∀ weight) (ℚRing.solve-∀ weight)
    (ℚRing.solve-∀ weight) (ℚRing.solve-∀ weight)
    (ℚRing.solve-∀ weight) (ℚRing.solve-∀ weight)
    (ℚRing.solve-∀ weight) (ℚRing.solve-∀ weight)
    (ℚRing.solve-∀ weight) (ℚRing.solve-∀ weight)
    (ℚRing.solve-∀ weight) (ℚRing.solve-∀ weight)
    (ℚRing.solve-∀ weight) (ℚRing.solve-∀ weight)
  where
  Vector16-ext :
    ∀ {left right : Vector16} →
    v00 left ≡ v00 right → v01 left ≡ v01 right →
    v02 left ≡ v02 right → v03 left ≡ v03 right →
    v04 left ≡ v04 right → v05 left ≡ v05 right →
    v06 left ≡ v06 right → v07 left ≡ v07 right →
    v08 left ≡ v08 right → v09 left ≡ v09 right →
    v10 left ≡ v10 right → v11 left ≡ v11 right →
    v12 left ≡ v12 right → v13 left ≡ v13 right →
    v14 left ≡ v14 right → v15 left ≡ v15 right →
    left ≡ right
  Vector16-ext
    {vector16 a00 a01 a02 a03 a04 a05 a06 a07
      a08 a09 a10 a11 a12 a13 a14 a15}
    {vector16 .a00 .a01 .a02 .a03 .a04 .a05 .a06 .a07
      .a08 .a09 .a10 .a11 .a12 .a13 .a14 .a15}
    refl refl refl refl refl refl refl refl
    refl refl refl refl refl refl refl refl = refl

uniformWeightsSeeOnlyAugmentation : ∀ weight base defects →
  sixteen
    * weightedSum16 (constant16 weight) (addBase16 base defects)
  ≡ sum16 (constant16 weight)
      * (sixteen * base + sum16 defects)
uniformWeightsSeeOnlyAugmentation weight base defects =
  let
    full = sixteenAtomCentredProbeExact
      base (constant16 weight) defects
  in
  substituteCentredZero full
  where
  substituteCentredZero :
    sixteen
      * weightedSum16 (constant16 weight) (addBase16 base defects)
    ≡ sum16 (constant16 weight) * (sixteen * base + sum16 defects)
      + centredDefectProbe16 (constant16 weight) defects →
    sixteen
      * weightedSum16 (constant16 weight) (addBase16 base defects)
    ≡ sum16 (constant16 weight) * (sixteen * base + sum16 defects)
  substituteCentredZero equality
    rewrite uniformWeightCentredCoefficientZero weight =
    trans equality (ℚRing.solve-∀
      (sum16 (constant16 weight)) base (sum16 defects))

wilsonSixteenAtomCentredProbeLevel : ProofLevel
wilsonSixteenAtomCentredProbeLevel = machineChecked

uniformPlacementAugmentationLevel : ProofLevel
uniformPlacementAugmentationLevel = machineChecked
