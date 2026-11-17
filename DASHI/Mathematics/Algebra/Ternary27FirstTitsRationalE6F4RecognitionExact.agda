module DASHI.Mathematics.Algebra.Ternary27FirstTitsRationalE6F4RecognitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Mathematics.Algebra.Ternary27FirstTitsAlbertExact as Tits
import DASHI.Mathematics.Algebra.Ternary27FirstTitsDerivationF4SignalExact as Derivation
import DASHI.Mathematics.Algebra.Ternary27FirstTitsF4RootRecognitionExact as F3Roots
import DASHI.Reasoning.AlbertF4FiniteWeylMaxCutExact as Finite

------------------------------------------------------------------------
-- RATIONAL FIRST-TITS E6 / F4 LIE-ALGEBRA RECOGNITION
--
-- `scripts/exceptional_e6_f4_root_weld_probe.py` works directly with the
-- rational first-Tits M3^3 cubic and Jordan product.
--
-- Cubic norm symmetry:
--   729 infinitesimal matrix unknowns;
--   rank 651 invariance system over good primes 5,7,101;
--   dimension 78;
--   six-dimensional Cartan + 72 one-dimensional nonzero root spaces;
--   extracted Cartan matrix is exactly E6.
--
-- Unit stabilizer / Jordan derivations:
--   adding unit-fixing raises the rank to 677, leaving dimension 52;
--   the unit stabilizer and the derivation equations have the same row space;
--   rational root extraction gives rank 4 + 48 one-dimensional roots;
--   exact F4 Cartan, 24 short + 24 long roots;
--   explicit linear weld maps that root set to the repository finite F4 set.
--
-- This is same-product/cubic Lie-algebra evidence. It does not by itself prove
-- equality of global algebraic groups or a characteristic-three smooth group
-- scheme, and it does not identify the split first-Tits rational form with the
-- repository's positive rational H3(O_Q) form (the signature no-go remains).
------------------------------------------------------------------------

record RationalFirstTitsE6F4LocalReceipt : Set where
  constructor rational-first-tits-e6-f4-local-receipt
  field
    actualFirstTitsCubicUsed : Bool
    cubicInfinitesimalUnknownCount : Nat
    cubicInvarianceRankGoodPrime : Nat
    cubicSymmetryLieDimension : Nat
    e6CartanDimension : Nat
    e6DistinctRootCount : Nat
    e6RootSpacesOneDimensional : Bool
    exactE6CartanRecovered : Bool
    minusculeWeightGraphIsSRG2716108 : Bool

    unitStabilizerRankGoodPrime : Nat
    unitStabilizerDimension : Nat
    jordanDerivationRankGoodPrime : Nat
    jordanDerivationDimension : Nat
    unitStabilizerEqualsDerivationSubspace : Bool
    f4CartanDimension : Nat
    f4DistinctRootCount : Nat
    f4RootSpacesOneDimensional : Bool
    f4ShortRootCount : Nat
    f4LongRootCount : Nat
    exactF4CartanRecovered : Bool
    rootSetWeldToExistingFiniteF4PaidLocally : Bool

    lieAlgebraE6RecognitionPaidLocally : Bool
    lieAlgebraF4RecognitionPaidLocally : Bool
    globalE6NormGroupRecognitionPaid : Bool
    globalF4AutomorphismGroupRecognitionPaid : Bool
    sameKernelAgdaRecognitionPaid : Bool
    boundary : String
open RationalFirstTitsE6F4LocalReceipt public

canonicalRationalFirstTitsE6F4LocalReceipt : RationalFirstTitsE6F4LocalReceipt
canonicalRationalFirstTitsE6F4LocalReceipt =
  rational-first-tits-e6-f4-local-receipt
    true
    729 651 78 6 72 true true true
    677 52 677 52 true
    4 48 true 24 24 true true
    true true
    false false false
    "On the actual rational first-Tits M3^3 cubic, infinitesimal norm symmetries form a rank-six/72-root E6 Lie-algebra candidate and the unit stabilizer is exactly the 52-dimensional Jordan-derivation subspace with rank-four/48-root F4 Cartan data. The root set is explicitly welded to the existing finite F4 model. Remaining obligations are kernelization and global algebraic-group/action recognition, not dimension hunting."

------------------------------------------------------------------------
-- Explicit classical Cartan receipts retained as strings for cross-kernel use.
------------------------------------------------------------------------

e6CartanText : String
e6CartanText =
  "[[2,-1,0,0,0,0],[-1,2,-1,0,0,0],[0,-1,2,-1,0,-1],[0,0,-1,2,-1,0],[0,0,0,-1,2,0],[0,0,-1,0,0,2]]"

f4CartanText : String
f4CartanText =
  "[[2,-1,0,0],[-1,2,-2,0],[0,-1,2,-1],[0,0,-1,2]]"

record RationalFirstTitsRecognitionBoundary : Set where
  constructor rational-first-tits-recognition-boundary
  field
    normSymmetryDimensionAloneCreatesE6 : Bool
    unitStabilizerDimensionAloneCreatesF4 : Bool
    rootCartanSameProductEvidencePresent : Bool
    globalGroupStillIndependent : Bool
    positiveAndSplitRationalAlbertFormsCollapsed : Bool
open RationalFirstTitsRecognitionBoundary public

canonicalRationalFirstTitsRecognitionBoundary : RationalFirstTitsRecognitionBoundary
canonicalRationalFirstTitsRecognitionBoundary =
  rational-first-tits-recognition-boundary false false true true false
