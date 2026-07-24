module DASHI.Physics.YangMills.BalabanBoolean4PatchExtensionsExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact

------------------------------------------------------------------------
-- Literal face and corner retracts of the Boolean four-cell.
--
-- `extendFace0` reflects an 8-site x0 = 0 face across the x0 direction.
-- `extendCorner01` reflects a 4-site x0 = x1 = 0 corner across both missing
-- directions.  The restriction-after-extension laws are definitional.
--
-- The norm and edge-energy scaling factors are exact polynomial identities:
--
--   face:   ||Ef||² = 2 ||f||²,    E4(Ef) = 2 E3(f)
--   corner: ||Ec||² = 4 ||c||²,    E4(Ec) = 4 E2(c).
------------------------------------------------------------------------

record Face8 : Set where
  constructor face8
  field
    y000 y001 y010 y011 y100 y101 y110 y111 : ℚ

open Face8 public

faceSum : Face8 → ℚ
faceSum (face8 y000 y001 y010 y011 y100 y101 y110 y111) =
  sumQ (y000 ∷ y001 ∷ y010 ∷ y011 ∷ y100 ∷ y101 ∷ y110 ∷ y111 ∷ [])

faceNormSq : Face8 → ℚ
faceNormSq (face8 y000 y001 y010 y011 y100 y101 y110 y111) =
  sumQ
    (sq y000 ∷ sq y001 ∷ sq y010 ∷ sq y011
    ∷ sq y100 ∷ sq y101 ∷ sq y110 ∷ sq y111 ∷ [])

faceEdgeEnergy : Face8 → ℚ
faceEdgeEnergy (face8 y000 y001 y010 y011 y100 y101 y110 y111) =
  sumQ
    (sqDiff y000 y100 ∷ sqDiff y000 y010 ∷ sqDiff y000 y001
    ∷ sqDiff y001 y101 ∷ sqDiff y001 y011
    ∷ sqDiff y010 y110 ∷ sqDiff y010 y011
    ∷ sqDiff y011 y111
    ∷ sqDiff y100 y110 ∷ sqDiff y100 y101
    ∷ sqDiff y101 y111 ∷ sqDiff y110 y111 ∷ [])

extendFace0 : Face8 → Cube16
extendFace0 (face8 y000 y001 y010 y011 y100 y101 y110 y111) =
  cube16
    y000 y001 y010 y011
    y100 y101 y110 y111
    y000 y001 y010 y011
    y100 y101 y110 y111

restrictFace0 : Cube16 → Face8
restrictFace0
  (cube16 x0000 x0001 x0010 x0011 x0100 x0101 x0110 x0111
          x1000 x1001 x1010 x1011 x1100 x1101 x1110 x1111) =
  face8 x0000 x0001 x0010 x0011 x0100 x0101 x0110 x0111

restrictFaceAfterExtend : ∀ face →
  restrictFace0 (extendFace0 face) ≡ face
restrictFaceAfterExtend (face8 y000 y001 y010 y011 y100 y101 y110 y111) =
  refl

faceBlockSumIdentityRaw :
  ∀ y000 y001 y010 y011 y100 y101 y110 y111 →
  blockSum
    (extendFace0 (face8 y000 y001 y010 y011 y100 y101 y110 y111))
  ≡ twoℚ * faceSum
    (face8 y000 y001 y010 y011 y100 y101 y110 y111)
faceBlockSumIdentityRaw = ℚRing.solve-∀

faceBlockSumIdentity : ∀ face →
  blockSum (extendFace0 face) ≡ twoℚ * faceSum face
faceBlockSumIdentity (face8 y000 y001 y010 y011 y100 y101 y110 y111) =
  faceBlockSumIdentityRaw y000 y001 y010 y011 y100 y101 y110 y111

faceNormIdentityRaw :
  ∀ y000 y001 y010 y011 y100 y101 y110 y111 →
  normSq
    (extendFace0 (face8 y000 y001 y010 y011 y100 y101 y110 y111))
  ≡ twoℚ * faceNormSq
    (face8 y000 y001 y010 y011 y100 y101 y110 y111)
faceNormIdentityRaw = ℚRing.solve-∀

faceNormIdentity : ∀ face →
  normSq (extendFace0 face) ≡ twoℚ * faceNormSq face
faceNormIdentity (face8 y000 y001 y010 y011 y100 y101 y110 y111) =
  faceNormIdentityRaw y000 y001 y010 y011 y100 y101 y110 y111

faceEnergyIdentityRaw :
  ∀ y000 y001 y010 y011 y100 y101 y110 y111 →
  edgeEnergy
    (extendFace0 (face8 y000 y001 y010 y011 y100 y101 y110 y111))
  ≡ twoℚ * faceEdgeEnergy
    (face8 y000 y001 y010 y011 y100 y101 y110 y111)
faceEnergyIdentityRaw = ℚRing.solve-∀

faceEnergyIdentity : ∀ face →
  edgeEnergy (extendFace0 face) ≡ twoℚ * faceEdgeEnergy face
faceEnergyIdentity (face8 y000 y001 y010 y011 y100 y101 y110 y111) =
  faceEnergyIdentityRaw y000 y001 y010 y011 y100 y101 y110 y111

twoTimesZero : twoℚ * 0ℚ ≡ 0ℚ
twoTimesZero = ℚRing.solve-∀

faceMeanZeroImpliesExtendedMeanZero : ∀ face →
  faceSum face ≡ 0ℚ →
  blockSum (extendFace0 face) ≡ 0ℚ
faceMeanZeroImpliesExtendedMeanZero face meanZero =
  trans
    (faceBlockSumIdentity face)
    (trans (cong (twoℚ *_) meanZero) twoTimesZero)

faceScaledPoincare : ∀ face →
  faceSum face ≡ 0ℚ →
  twoℚ * (twoℚ * faceNormSq face)
  ≤ twoℚ * faceEdgeEnergy face
faceScaledPoincare face meanZero =
  subst
    (λ left →
      twoℚ * left ≤ twoℚ * faceEdgeEnergy face)
    (faceNormIdentity face)
    (subst
      (λ right →
        twoℚ * normSq (extendFace0 face) ≤ right)
      (faceEnergyIdentity face)
      (boolean4BlockPoincare
        (extendFace0 face)
        (faceMeanZeroImpliesExtendedMeanZero face meanZero)))

facePoincare : ∀ face →
  faceSum face ≡ 0ℚ →
  twoℚ * faceNormSq face ≤ faceEdgeEnergy face
facePoincare face meanZero =
  ℚP.*-cancelˡ-≤-pos twoℚ (faceScaledPoincare face meanZero)

------------------------------------------------------------------------
-- Codimension-two corner.
------------------------------------------------------------------------

record Corner4 : Set where
  constructor corner4
  field
    z00 z01 z10 z11 : ℚ

open Corner4 public

cornerSum : Corner4 → ℚ
cornerSum (corner4 z00 z01 z10 z11) =
  sumQ (z00 ∷ z01 ∷ z10 ∷ z11 ∷ [])

cornerNormSq : Corner4 → ℚ
cornerNormSq (corner4 z00 z01 z10 z11) =
  sumQ (sq z00 ∷ sq z01 ∷ sq z10 ∷ sq z11 ∷ [])

cornerEdgeEnergy : Corner4 → ℚ
cornerEdgeEnergy (corner4 z00 z01 z10 z11) =
  sumQ
    (sqDiff z00 z10 ∷ sqDiff z00 z01
    ∷ sqDiff z01 z11 ∷ sqDiff z10 z11 ∷ [])

extendCorner01 : Corner4 → Cube16
extendCorner01 (corner4 z00 z01 z10 z11) =
  cube16
    z00 z01 z10 z11
    z00 z01 z10 z11
    z00 z01 z10 z11
    z00 z01 z10 z11

restrictCorner01 : Cube16 → Corner4
restrictCorner01
  (cube16 x0000 x0001 x0010 x0011 x0100 x0101 x0110 x0111
          x1000 x1001 x1010 x1011 x1100 x1101 x1110 x1111) =
  corner4 x0000 x0001 x0010 x0011

restrictCornerAfterExtend : ∀ corner →
  restrictCorner01 (extendCorner01 corner) ≡ corner
restrictCornerAfterExtend (corner4 z00 z01 z10 z11) = refl

cornerBlockSumIdentityRaw : ∀ z00 z01 z10 z11 →
  blockSum (extendCorner01 (corner4 z00 z01 z10 z11))
  ≡ fourℚ * cornerSum (corner4 z00 z01 z10 z11)
cornerBlockSumIdentityRaw = ℚRing.solve-∀

cornerBlockSumIdentity : ∀ corner →
  blockSum (extendCorner01 corner) ≡ fourℚ * cornerSum corner
cornerBlockSumIdentity (corner4 z00 z01 z10 z11) =
  cornerBlockSumIdentityRaw z00 z01 z10 z11

cornerNormIdentityRaw : ∀ z00 z01 z10 z11 →
  normSq (extendCorner01 (corner4 z00 z01 z10 z11))
  ≡ fourℚ * cornerNormSq (corner4 z00 z01 z10 z11)
cornerNormIdentityRaw = ℚRing.solve-∀

cornerNormIdentity : ∀ corner →
  normSq (extendCorner01 corner) ≡ fourℚ * cornerNormSq corner
cornerNormIdentity (corner4 z00 z01 z10 z11) =
  cornerNormIdentityRaw z00 z01 z10 z11

cornerEnergyIdentityRaw : ∀ z00 z01 z10 z11 →
  edgeEnergy (extendCorner01 (corner4 z00 z01 z10 z11))
  ≡ fourℚ * cornerEdgeEnergy (corner4 z00 z01 z10 z11)
cornerEnergyIdentityRaw = ℚRing.solve-∀

cornerEnergyIdentity : ∀ corner →
  edgeEnergy (extendCorner01 corner) ≡ fourℚ * cornerEdgeEnergy corner
cornerEnergyIdentity (corner4 z00 z01 z10 z11) =
  cornerEnergyIdentityRaw z00 z01 z10 z11

fourTimesZero : fourℚ * 0ℚ ≡ 0ℚ
fourTimesZero = ℚRing.solve-∀

cornerMeanZeroImpliesExtendedMeanZero : ∀ corner →
  cornerSum corner ≡ 0ℚ →
  blockSum (extendCorner01 corner) ≡ 0ℚ
cornerMeanZeroImpliesExtendedMeanZero corner meanZero =
  trans
    (cornerBlockSumIdentity corner)
    (trans (cong (fourℚ *_) meanZero) fourTimesZero)

cornerScaledPoincare : ∀ corner →
  cornerSum corner ≡ 0ℚ →
  twoℚ * (fourℚ * cornerNormSq corner)
  ≤ fourℚ * cornerEdgeEnergy corner
cornerScaledPoincare corner meanZero =
  subst
    (λ left →
      twoℚ * left ≤ fourℚ * cornerEdgeEnergy corner)
    (cornerNormIdentity corner)
    (subst
      (λ right →
        twoℚ * normSq (extendCorner01 corner) ≤ right)
      (cornerEnergyIdentity corner)
      (boolean4BlockPoincare
        (extendCorner01 corner)
        (cornerMeanZeroImpliesExtendedMeanZero corner meanZero)))

cornerScaleCommute : ∀ q →
  twoℚ * (fourℚ * q) ≡ fourℚ * (twoℚ * q)
cornerScaleCommute = ℚRing.solve-∀

cornerPoincare : ∀ corner →
  cornerSum corner ≡ 0ℚ →
  twoℚ * cornerNormSq corner ≤ cornerEdgeEnergy corner
cornerPoincare corner meanZero =
  ℚP.*-cancelˡ-≤-pos fourℚ
    (subst
      (λ left → left ≤ fourℚ * cornerEdgeEnergy corner)
      (cornerScaleCommute (cornerNormSq corner))
      (cornerScaledPoincare corner meanZero))

boolean4BoundaryRetractLevel : ProofLevel
boolean4BoundaryRetractLevel = machineChecked

boolean4CornerRetractLevel : ProofLevel
boolean4CornerRetractLevel = machineChecked

boolean4PatchNormEnergyLevel : ProofLevel
boolean4PatchNormEnergyLevel = computed

physicalWeightedPatchResidualLevel : ProofLevel
physicalWeightedPatchResidualLevel = conditional
