module DASHI.Moonshine.OggSSP2BM24Outer2BDuadTateDefectExact where

------------------------------------------------------------------------
-- EXACT WITHIN-FIBRE M24-2B DUAD TATE-DEFECT TARGET
--
-- Source facts (ATLAS):
--   * the relevant outer M22:2 involution class has centralizer order 640;
--   * M24 involution classes have centralizer orders
--       2A : 21504
--       2B : 7680;
--   * therefore an M22:2 involution with centralizer 640 cannot fuse to 2A
--     (640 does not divide 21504) but can fuse to 2B (7680 = 12 * 640);
--   * M24 class 2B has cycle shape 2^12 on the natural 24-point action.
--
-- On duads (= unordered 2-subsets of the 24 points), a 2^12 permutation fixes
-- exactly the 12 transposition-pairs.  The remaining 264 duads form 132
-- 2-cycles.  Hence on F2[duads]:
--
--   dim = 276
--   J1 blocks = 12
--   J2 blocks = 132
--   rank(g-I) = 132
--   dim Fix(g) = 12 + 132 = 144
--   dim Hhat^0(<g>,F2[duads]) = 12.
--
-- This is a same-object TEST TARGET for the actual 2B Tate head.  It does not
-- identify the Tate extension with the duad extension.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

m24TwoACentralizerOrder : Nat
m24TwoACentralizerOrder = 21504

m24TwoBCentralizerOrder : Nat
m24TwoBCentralizerOrder = 7680

m22d2OuterCentralizerOrder : Nat
m22d2OuterCentralizerOrder = 640

m24TwoBCentralizerFactor :
  12 * m22d2OuterCentralizerOrder ≡ m24TwoBCentralizerOrder
m24TwoBCentralizerFactor = refl

naturalPointCount : Nat
naturalPointCount = 24

naturalTwoBCycleCount : Nat
naturalTwoBCycleCount = 12

duadDimension : Nat
duadDimension = 276

fixedDuadCount : Nat
fixedDuadCount = 12

swappedDuadPairCount : Nat
swappedDuadPairCount = 132

fixedSpaceDimension : Nat
fixedSpaceDimension = fixedDuadCount + swappedDuadPairCount

rankGMinusI : Nat
rankGMinusI = swappedDuadPairCount

iteratedTateDefectDimension : Nat
iteratedTateDefectDimension = fixedDuadCount

duadDimensionClosure :
  fixedDuadCount + (2 * swappedDuadPairCount) ≡ duadDimension
duadDimensionClosure = refl

fixedSpaceDimensionIs144 : fixedSpaceDimension ≡ 144
fixedSpaceDimensionIs144 = refl

rankGMinusIIs132 : rankGMinusI ≡ 132
rankGMinusIIs132 = refl

iteratedTateDefectIsTwelve : iteratedTateDefectDimension ≡ 12
iteratedTateDefectIsTwelve = refl

record DuadOuter2BDefectBoundary : Set where
  constructor duad-outer-2b-defect-boundary
  field
    atlasCentralizerDataSourced : Bool
    atlasNatural24CycleShapeSourced : Bool
    localPythonDuadOrbitAuditPassed : Bool
    exactDuadDefectTwelvePaid : Bool
    actualTwoBTateDefectComputed : Bool
    actualTateExtensionMatched : Bool

canonicalDuadOuter2BDefectBoundary : DuadOuter2BDefectBoundary
canonicalDuadOuter2BDefectBoundary =
  duad-outer-2b-defect-boundary
    true true true true false false
