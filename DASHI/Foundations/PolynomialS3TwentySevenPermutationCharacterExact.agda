module DASHI.Foundations.PolynomialS3TwentySevenPermutationCharacterExact where

------------------------------------------------------------------------
-- EXACT TRACE CHARACTER OF THE ACTUAL 27 ENDO(T3) CONJUGATION
-- PERMUTATION REPRESENTATION. An S3 element fixes a code f
-- precisely when p*f*p^-1=f. Hence its permutation-matrix trace
-- is the number of fixed endomorphism codes.
--
-- 27 at identity; 3 for the two nontrivial rotations AND for each
-- of the three reflections. Burnside gives 7 S3 orbits and 11 C3
-- orbits. With the classical characteristic-zero S3 character
-- table (1,triv), (sgn), (2,standard), multiplicities solve as
-- 7*1 + 4*sgn + 8*std = 27 in dimension.
--
-- IMPORTANT: proof of this arithmetic character identification is
-- NOT a source-constructed characteristic-zero representation
-- isomorphism. It requires semisimplicity/character theory over
-- characteristic zero (classical Maschke). In characteristic 3,
-- S3 has order divisible by the characteristic, so NEVER promote
-- the 7+4+16 numeric split to a semisimple F3 decomposition.
--
-- Prior owners: exact S3 conjugacy and seven shapes, and original
-- #1414 eleven-class F3 reflection-Fourier source.
-- SOURCE-WRITTEN, no Agda kernel verification performed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_,_)
import Base369 as Base
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Shape

sameTruth : Base.TriTruth → Base.TriTruth → Bool
sameTruth Base.tri-low Base.tri-low = true
sameTruth Base.tri-low Base.tri-mid = false
sameTruth Base.tri-low Base.tri-high = false
sameTruth Base.tri-mid Base.tri-low = false
sameTruth Base.tri-mid Base.tri-mid = true
sameTruth Base.tri-mid Base.tri-high = false
sameTruth Base.tri-high Base.tri-low = false
sameTruth Base.tri-high Base.tri-mid = false
sameTruth Base.tri-high Base.tri-high = true

andBool : Bool → Bool → Bool
andBool true true = true
andBool _ _ = false

sameCode :
  Tower.LevelTwoCode → Tower.LevelTwoCode → Bool
sameCode (a , (b , c)) (x , (y , z)) =
  andBool (sameTruth a x)
    (andBool (sameTruth b y) (sameTruth c z))

allTwentySeven : List Tower.LevelTwoCode
allTwentySeven =
  (Base.tri-low , (Base.tri-low , Base.tri-low))
  ∷   (Base.tri-low , (Base.tri-low , Base.tri-mid))
  ∷   (Base.tri-low , (Base.tri-low , Base.tri-high))
  ∷   (Base.tri-low , (Base.tri-mid , Base.tri-low))
  ∷   (Base.tri-low , (Base.tri-mid , Base.tri-mid))
  ∷   (Base.tri-low , (Base.tri-mid , Base.tri-high))
  ∷   (Base.tri-low , (Base.tri-high , Base.tri-low))
  ∷   (Base.tri-low , (Base.tri-high , Base.tri-mid))
  ∷   (Base.tri-low , (Base.tri-high , Base.tri-high))
  ∷   (Base.tri-mid , (Base.tri-low , Base.tri-low))
  ∷   (Base.tri-mid , (Base.tri-low , Base.tri-mid))
  ∷   (Base.tri-mid , (Base.tri-low , Base.tri-high))
  ∷   (Base.tri-mid , (Base.tri-mid , Base.tri-low))
  ∷   (Base.tri-mid , (Base.tri-mid , Base.tri-mid))
  ∷   (Base.tri-mid , (Base.tri-mid , Base.tri-high))
  ∷   (Base.tri-mid , (Base.tri-high , Base.tri-low))
  ∷   (Base.tri-mid , (Base.tri-high , Base.tri-mid))
  ∷   (Base.tri-mid , (Base.tri-high , Base.tri-high))
  ∷   (Base.tri-high , (Base.tri-low , Base.tri-low))
  ∷   (Base.tri-high , (Base.tri-low , Base.tri-mid))
  ∷   (Base.tri-high , (Base.tri-low , Base.tri-high))
  ∷   (Base.tri-high , (Base.tri-mid , Base.tri-low))
  ∷   (Base.tri-high , (Base.tri-mid , Base.tri-mid))
  ∷   (Base.tri-high , (Base.tri-mid , Base.tri-high))
  ∷   (Base.tri-high , (Base.tri-high , Base.tri-low))
  ∷   (Base.tri-high , (Base.tri-high , Base.tri-mid))
  ∷   (Base.tri-high , (Base.tri-high , Base.tri-high))
  ∷ []

countList : ∀ {A : Set} → List A → Nat
countList [] = 0
countList (_ ∷ rest) = 1 + countList rest

fullEnumerationHasTwentySeven :
  countList allTwentySeven ≡ 27
fullEnumerationHasTwentySeven = refl

boolCount : Bool → Nat
boolCount false = 0
boolCount true = 1

countFixed :
  Shape.TriPermutation → List Tower.LevelTwoCode → Nat
countFixed p [] = 0
countFixed p (x ∷ xs) =
  boolCount (sameCode (Shape.conjugateCode p x) x)
    + countFixed p xs

fixed0 : countFixed Shape.permIdentity allTwentySeven ≡ 27
fixed0 = refl

fixed1 : countFixed Shape.permRotate allTwentySeven ≡ 3
fixed1 = refl

fixed2 : countFixed Shape.permRotate2 allTwentySeven ≡ 3
fixed2 = refl

fixed3 : countFixed Shape.permSwapLowMid allTwentySeven ≡ 3
fixed3 = refl

fixed4 : countFixed Shape.permSwapLowHigh allTwentySeven ≡ 3
fixed4 = refl

fixed5 : countFixed Shape.permSwapMidHigh allTwentySeven ≡ 3
fixed5 = refl

-- The identity and two rotations count to 3*11, as the
-- eleven-class proof already independently constructed.
c3BurnsideNumerator : 27 + 3 + 3 ≡ 3 * 11
c3BurnsideNumerator = refl

-- All six elements count to 6*7; the original seven-shape owner
-- independently identifies the seven actual orbit classes.
s3BurnsideNumerator :
  27 + 3 + 3 + 3 + 3 + 3 ≡ 6 * 7
s3BurnsideNumerator = refl

-- Character reconciliation over characteristic ZERO, conditional
-- on the classical S3 table and complete reducibility:
--   class identity       trivial 1 + sign 1 + standard 2
--   class 3-cycle        trivial 1 + sign 1 + standard -1
--   class transposition  trivial 1 + sign -1 + standard 0
dimensionReconstructed : 7 + 4 + (8 * 2) ≡ 27
dimensionReconstructed = refl

threeCycleCharacterReconstructed : 7 + 4 ≡ 3 + 8
threeCycleCharacterReconstructed = refl

transpositionCharacterReconstructed : 7 ≡ 3 + 4
transpositionCharacterReconstructed = refl

-- 3 fixed sites + 4 transposed pairs on eleven C3-orbits.
-- Character of that C2 action: 11 at identity, 3 at reflection.
elevenDimensionReconstructed : 7 + 4 ≡ 11
elevenDimensionReconstructed = refl

elevenReflectionTraceReconstructed : 7 ≡ 3 + 4
elevenReflectionTraceReconstructed = refl

-- These numbers are actual permutation fixed-point trace counts,
-- NOT a proof that the polynomial Galois representation, horned
-- wild-exterior pi1, physical wave transport, or Monster3B
-- module is the same 27-dimensional representation.
