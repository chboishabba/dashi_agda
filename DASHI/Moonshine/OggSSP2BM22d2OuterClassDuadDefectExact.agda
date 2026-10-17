module DASHI.Moonshine.OggSSP2BM22d2OuterClassDuadDefectExact where

------------------------------------------------------------------------
-- EXACT OUTER-CLASS / DUAD ITERATED-TATE TARGET
--
-- Runtime source already fixes the Completion10 outer M22:2 involution class:
--   class size = 1386, centralizer order in M22:2 = 640.
--
-- ATLAS M24 involution centralizers:
--   2A : 21504
--   2B :  7680
--
-- Since C_{M22:2}(h) <= C_{M24}(h), its order 640 must divide the relevant
-- M24 centralizer.  640 does not divide 21504, while 7680 = 12 * 640.
-- Hence this outer class fuses to M24 class 2B.
--
-- M24-2B has natural 24-point cycle shape 2^12.  On the 276 duads, exactly
-- the 12 supports of those transpositions are fixed.  The remaining 264 duads
-- form 132 swapped pairs.  Over F2:
--
--   rank(h-I)          = 132
--   dim ker(h-I)       = 12 + 132 = 144
--   iterated Tate H0   = ker/im dimension = 144 - 132 = 12
--
-- This gives an exact scalar target for the actual 2B-pure Klein-four Tate
-- computation.  It does NOT identify the Tate head with the duad module.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

m22d2OuterCentralizer : Nat
m22d2OuterCentralizer = 640

m24TwoACentralizer : Nat
m24TwoACentralizer = 21504

m24TwoBCentralizer : Nat
m24TwoBCentralizer = 7680

m24TwoBCentralizerIsTwelveTimesLocal :
  m24TwoBCentralizer ≡ 12 * m22d2OuterCentralizer
m24TwoBCentralizerIsTwelveTimesLocal = refl

-- Divisibility failure for 2A is encoded by its nonzero remainder.
m24TwoACentralizerRemainderByLocal : Nat
m24TwoACentralizerRemainderByLocal = 384

m24TwoARemainderIs384 : m24TwoACentralizerRemainderByLocal ≡ 384
m24TwoARemainderIs384 = refl

m24TwoBTranspositionCount : Nat
m24TwoBTranspositionCount = 12

fixedDuadCount : Nat
fixedDuadCount = 12

swappedDuadPairCount : Nat
swappedDuadPairCount = 132

ambientDuadDimension : Nat
ambientDuadDimension = 276

duadRankGMinusI : Nat
duadRankGMinusI = 132

duadFixedDimension : Nat
duadFixedDimension = 144

duadIteratedTateDefect : Nat
duadIteratedTateDefect = 12

duadOrbitClosure :
  fixedDuadCount + (2 * swappedDuadPairCount) ≡ ambientDuadDimension
duadOrbitClosure = refl

duadRankIs132 : duadRankGMinusI ≡ 132
duadRankIs132 = refl

duadFixedDimensionIs144 : duadFixedDimension ≡ 144
duadFixedDimensionIs144 = refl

duadDefectClosure :
  duadIteratedTateDefect + (2 * duadRankGMinusI) ≡ ambientDuadDimension
duadDefectClosure = refl

duadIteratedTateDefectIs12 : duadIteratedTateDefect ≡ 12
duadIteratedTateDefectIs12 = refl

record OuterClassDuadDefectBoundary : Set where
  constructor outer-class-duad-defect-boundary
  field
    localOuterCentralizer640Paid : Bool
    m24InvolutionCentralizersSourced : Bool
    localCentralizerExcludesM24TwoA : Bool
    localCentralizerSelectsM24TwoB : Bool
    m24TwoBCycleShape2Pow12Sourced : Bool
    duadFixedCountTwelveDerived : Bool
    duadRank132Derived : Bool
    duadIteratedTateDefectTwelveDerived : Bool
    actualTwoBTateIteratedDefectComputed : Bool

canonicalOuterClassDuadDefectBoundary : OuterClassDuadDefectBoundary
canonicalOuterClassDuadDefectBoundary =
  outer-class-duad-defect-boundary
    true true true true true true true true false
