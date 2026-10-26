module DASHI.Mathematics.Symmetry.CrystalClassificationSevenFourteenExact where

-- Classification labels, not a classification theorem.
-- Source authority: IUCr, International Tables for Crystallography,
-- Volume A; standard 7 systems / 14 Bravais types.
-- No claims about measured specimens, space groups, or typecheck receipt.
open import Agda.Builtin.Equality using (_≡_; refl)

data CrystalSystem : Set where
  triclinic monoclinic orthorhombic tetragonal trigonal hexagonal cubic : CrystalSystem

data BravaisType : Set where
  aP : BravaisType
  mP mC : BravaisType
  oP oC oI oF : BravaisType
  tP tI : BravaisType
  hR hP : BravaisType
  cP cI cF : BravaisType

systemOf : BravaisType → CrystalSystem
systemOf aP = triclinic
systemOf mP = monoclinic
systemOf mC = monoclinic
systemOf oP = orthorhombic
systemOf oC = orthorhombic
systemOf oI = orthorhombic
systemOf oF = orthorhombic
systemOf tP = tetragonal
systemOf tI = tetragonal
systemOf hR = trigonal
systemOf hP = hexagonal
systemOf cP = cubic
systemOf cI = cubic
systemOf cF = cubic

tetragonalPrimitive : systemOf tP ≡ tetragonal
tetragonalPrimitive = refl
tetragonalBodyCentred : systemOf tI ≡ tetragonal
tetragonalBodyCentred = refl

-- Formal point-group records should carry a faithful integral
-- lattice automorphism action; bare HM/Schoenflies strings do not
-- supply that proof. In particular hR is a trigonal Bravais lattice
-- and hP is the hexagonal Bravais lattice (both in hexagonal axes
-- when conventionally represented).
