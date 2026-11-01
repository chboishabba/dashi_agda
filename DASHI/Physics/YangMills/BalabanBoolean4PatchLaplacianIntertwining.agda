module DASHI.Physics.YangMills.BalabanBoolean4PatchLaplacianIntertwining where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact
open import DASHI.Physics.YangMills.BalabanBoolean4PatchExtensionsExact

------------------------------------------------------------------------
-- Exact reference-operator intertwining for the concrete face and corner
-- reflections.  The operator is the positive graph Laplacian on Q4 and on
-- its Q3/Q2 patches:
--
--   (Lf)(x) = degree f(x) - Σ_{y~x} f(y).
--
-- Reflection makes every missing normal difference vanish, so restriction
-- after the four-dimensional operator agrees exactly with the lower
-- dimensional patch operator.  The reference residual is therefore zero,
-- not merely small, for these literal finite cells.
------------------------------------------------------------------------

threeℚ : ℚ
threeℚ = twoℚ + 1ℚ

lap4 : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
lap4 center n0 n1 n2 n3 =
  fourℚ * center - (n0 + (n1 + (n2 + n3)))

lap3 : ℚ → ℚ → ℚ → ℚ → ℚ
lap3 center n1 n2 n3 =
  threeℚ * center - (n1 + (n2 + n3))

lap2 : ℚ → ℚ → ℚ → ℚ
lap2 center n2 n3 =
  twoℚ * center - (n2 + n3)

cubeLaplacian : Cube16 → Cube16
cubeLaplacian
  (cube16 x0000 x0001 x0010 x0011 x0100 x0101 x0110 x0111
          x1000 x1001 x1010 x1011 x1100 x1101 x1110 x1111) =
  cube16
    (lap4 x0000 x1000 x0100 x0010 x0001)
    (lap4 x0001 x1001 x0101 x0011 x0000)
    (lap4 x0010 x1010 x0110 x0000 x0011)
    (lap4 x0011 x1011 x0111 x0001 x0010)
    (lap4 x0100 x1100 x0000 x0110 x0101)
    (lap4 x0101 x1101 x0001 x0111 x0100)
    (lap4 x0110 x1110 x0010 x0100 x0111)
    (lap4 x0111 x1111 x0011 x0101 x0110)
    (lap4 x1000 x0000 x1100 x1010 x1001)
    (lap4 x1001 x0001 x1101 x1011 x1000)
    (lap4 x1010 x0010 x1110 x1000 x1011)
    (lap4 x1011 x0011 x1111 x1001 x1010)
    (lap4 x1100 x0100 x1000 x1110 x1101)
    (lap4 x1101 x0101 x1001 x1111 x1100)
    (lap4 x1110 x0110 x1010 x1100 x1111)
    (lap4 x1111 x0111 x1011 x1101 x1110)

faceLaplacian : Face8 → Face8
faceLaplacian (face8 y000 y001 y010 y011 y100 y101 y110 y111) =
  face8
    (lap3 y000 y100 y010 y001)
    (lap3 y001 y101 y011 y000)
    (lap3 y010 y110 y000 y011)
    (lap3 y011 y111 y001 y010)
    (lap3 y100 y000 y110 y101)
    (lap3 y101 y001 y111 y100)
    (lap3 y110 y010 y100 y111)
    (lap3 y111 y011 y101 y110)

cornerLaplacian : Corner4 → Corner4
cornerLaplacian (corner4 z00 z01 z10 z11) =
  corner4
    (lap2 z00 z10 z01)
    (lap2 z01 z11 z00)
    (lap2 z10 z00 z11)
    (lap2 z11 z01 z10)

faceExt :
  ∀ {left right : Face8} →
  y000 left ≡ y000 right →
  y001 left ≡ y001 right →
  y010 left ≡ y010 right →
  y011 left ≡ y011 right →
  y100 left ≡ y100 right →
  y101 left ≡ y101 right →
  y110 left ≡ y110 right →
  y111 left ≡ y111 right →
  left ≡ right
faceExt {face8 a000 a001 a010 a011 a100 a101 a110 a111}
        {face8 .a000 .a001 .a010 .a011 .a100 .a101 .a110 .a111}
        refl refl refl refl refl refl refl refl = refl

cornerExt :
  ∀ {left right : Corner4} →
  z00 left ≡ z00 right →
  z01 left ≡ z01 right →
  z10 left ≡ z10 right →
  z11 left ≡ z11 right →
  left ≡ right
cornerExt {corner4 a00 a01 a10 a11}
          {corner4 .a00 .a01 .a10 .a11}
          refl refl refl refl = refl

reflection4To3 :
  ∀ center n1 n2 n3 →
  lap4 center center n1 n2 n3 ≡ lap3 center n1 n2 n3
reflection4To3 = ℚRing.solve-∀

reflection4To2 :
  ∀ center n2 n3 →
  lap4 center center center n2 n3 ≡ lap2 center n2 n3
reflection4To2 = ℚRing.solve-∀

faceLaplacianIntertwining : ∀ face →
  restrictFace0 (cubeLaplacian (extendFace0 face))
  ≡ faceLaplacian face
faceLaplacianIntertwining
  (face8 y000 y001 y010 y011 y100 y101 y110 y111) =
  faceExt
    (reflection4To3 y000 y100 y010 y001)
    (reflection4To3 y001 y101 y011 y000)
    (reflection4To3 y010 y110 y000 y011)
    (reflection4To3 y011 y111 y001 y010)
    (reflection4To3 y100 y000 y110 y101)
    (reflection4To3 y101 y001 y111 y100)
    (reflection4To3 y110 y010 y100 y111)
    (reflection4To3 y111 y011 y101 y110)

cornerLaplacianIntertwining : ∀ corner →
  restrictCorner01 (cubeLaplacian (extendCorner01 corner))
  ≡ cornerLaplacian corner
cornerLaplacianIntertwining (corner4 z00 z01 z10 z11) =
  cornerExt
    (reflection4To2 z00 z10 z01)
    (reflection4To2 z01 z11 z00)
    (reflection4To2 z10 z00 z11)
    (reflection4To2 z11 z01 z10)

boolean4BoundaryReferenceIntertwiningLevel : ProofLevel
boolean4BoundaryReferenceIntertwiningLevel = computed

boolean4CornerReferenceIntertwiningLevel : ProofLevel
boolean4CornerReferenceIntertwiningLevel = computed

boolean4BoundaryReferenceResidualZeroLevel : ProofLevel
boolean4BoundaryReferenceResidualZeroLevel = machineChecked

boolean4CornerReferenceResidualZeroLevel : ProofLevel
boolean4CornerReferenceResidualZeroLevel = machineChecked

physicalBackgroundPatchResidualLevel : ProofLevel
physicalBackgroundPatchResidualLevel = conditional
