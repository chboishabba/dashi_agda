module DASHI.Biology.Physical.BiologicalRNA9HammingExact where

------------------------------------------------------------------------
-- Native nine-base RNA edit distance on the already source-pinned dmsC
-- carrier, rather than the unrelated two-bit Gray-code metric.
-- No phenotype equivalence or mechanistic inference is made from distance.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Biology.Physical.OriginalDmscTwoGenotypeMeasuredExact as Dmsc

open Dmsc using (RNABase; RNA8; RNA9; rna8; rna9; A; C; G; U)

baseDifference : RNABase → RNABase → Nat
baseDifference A A = 0
baseDifference C C = 0
baseDifference G G = 0
baseDifference U U = 0
baseDifference _ _ = 1

baseDifferenceSelf : (a : RNABase) → baseDifference a a ≡ 0
baseDifferenceSelf A = refl
baseDifferenceSelf C = refl
baseDifferenceSelf G = refl
baseDifferenceSelf U = refl

baseDifferenceSymmetric :
  (a b : RNABase) → baseDifference a b ≡ baseDifference b a
baseDifferenceSymmetric A A = refl
baseDifferenceSymmetric A C = refl
baseDifferenceSymmetric A G = refl
baseDifferenceSymmetric A U = refl
baseDifferenceSymmetric C A = refl
baseDifferenceSymmetric C C = refl
baseDifferenceSymmetric C G = refl
baseDifferenceSymmetric C U = refl
baseDifferenceSymmetric G A = refl
baseDifferenceSymmetric G C = refl
baseDifferenceSymmetric G G = refl
baseDifferenceSymmetric G U = refl
baseDifferenceSymmetric U A = refl
baseDifferenceSymmetric U C = refl
baseDifferenceSymmetric U G = refl
baseDifferenceSymmetric U U = refl

hamming8 : RNA8 → RNA8 → Nat
hamming8 (rna8 a b c d e f g h) (rna8 i j k l m n o p) =
  baseDifference a i + baseDifference b j +
  baseDifference c k + baseDifference d l +
  baseDifference e m + baseDifference f n +
  baseDifference g o + baseDifference h p

hamming9 : RNA9 → RNA9 → Nat
hamming9 (rna9 prefixA lastA) (rna9 prefixB lastB) =
  hamming8 prefixA prefixB + baseDifference lastA lastB

hamming8Self : (x : RNA8) → hamming8 x x ≡ 0
hamming8Self (rna8 a b c d e f g h)
  rewrite baseDifferenceSelf a
        | baseDifferenceSelf b
        | baseDifferenceSelf c
        | baseDifferenceSelf d
        | baseDifferenceSelf e
        | baseDifferenceSelf f
        | baseDifferenceSelf g
        | baseDifferenceSelf h = refl

hamming9Self : (x : RNA9) → hamming9 x x ≡ 0
hamming9Self (rna9 prefix last)
  rewrite hamming8Self prefix
        | baseDifferenceSelf last = refl

hamming8Symmetric : (x y : RNA8) → hamming8 x y ≡ hamming8 y x
hamming8Symmetric
  (rna8 a b c d e f g h) (rna8 i j k l m n o p)
  rewrite baseDifferenceSymmetric a i
        | baseDifferenceSymmetric b j
        | baseDifferenceSymmetric c k
        | baseDifferenceSymmetric d l
        | baseDifferenceSymmetric e m
        | baseDifferenceSymmetric f n
        | baseDifferenceSymmetric g o
        | baseDifferenceSymmetric h p = refl

hamming9Symmetric : (x y : RNA9) → hamming9 x y ≡ hamming9 y x
hamming9Symmetric (rna9 prefixA lastA) (rna9 prefixB lastB)
  rewrite hamming8Symmetric prefixA prefixB
        | baseDifferenceSymmetric lastA lastB = refl

-- A real pair of RNA strings in the original published assay, not a
-- hypothetical genotype or a two-bit illustrative Gray-code fixture.
originalsOneSubstitution :
  hamming9 Dmsc.firstOriginalGenotype Dmsc.secondOriginalGenotype ≡ 1
originalsOneSubstitution = refl

originalsOneSubstitutionReverse :
  hamming9 Dmsc.secondOriginalGenotype Dmsc.firstOriginalGenotype ≡ 1
originalsOneSubstitutionReverse =
  trans (hamming9Symmetric
    Dmsc.secondOriginalGenotype Dmsc.firstOriginalGenotype)
    originalsOneSubstitution

-- Exact arithmetic on observed replicate means: 664 - 563 = 101 in
-- thousandths.  This is NOT a p-value, confidence bound or causal effect.
originalMeanDifferenceThousandths :
  Dmsc.meanThousandths Dmsc.originalAAAC
    ≡ Dmsc.meanThousandths Dmsc.originalAAAA + 101
originalMeanDifferenceThousandths = refl

-- Exact counterexample to inferring identical reported means from a
-- small edit distance: the pair has distance one and distinct means.
oneSubstitutionDoesNotForceEqualMeans :
  Dmsc.meanThousandths Dmsc.originalAAAA
    ≡ Dmsc.meanThousandths Dmsc.originalAAAC → ⊥
oneSubstitutionDoesNotForceEqualMeans = Dmsc.differentRawMeanReadouts
