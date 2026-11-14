module DASHI.Reasoning.T5QuadraticOrbitAuditExact where

------------------------------------------------------------------------
-- T5 QUADRATIC-ORBIT AUDIT
--
-- DASHI CONTRIBUTION / CROSS-LANGUAGE AUDIT
--
-- Local Python exhaustive enumeration and the Lean mirror use the standard
-- balanced F3^5 quadratic form
--
--   Q(x) = x0^2 + ... + x4^2.
--
-- Since a nonzero F3 coordinate has square 1, Q is Hamming weight modulo 3.
-- The five-coordinate support counts are therefore enough to derive
--
--   243 = 1 + 80 + 90 + 72.
--
-- This owner pays that combinatorial arithmetic and records the important
-- mismatch with the distinct diagonal 3 + 240 cut.  It does NOT claim an Agda
-- enumeration of the concrete Kernel5 carrier, and it does not promote the
-- Lean source-written result to an Agda/kernel theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.T5E8RelativeComplementCandidateExact as Relative
import DASHI.Cognition.Teleodynamics.ExceptionalPriorFamilyExact as Exceptional

------------------------------------------------------------------------
-- 1. Closed combinatorial derivation.
--
-- Exactly k nonzero coordinates contribute C(5,k) * 2^k states.
------------------------------------------------------------------------

weight0Count weight1Count weight2Count weight3Count weight4Count weight5Count : Nat
weight0Count = 1
weight1Count = 10
weight2Count = 40
weight3Count = 80
weight4Count = 80
weight5Count = 32

weight0CountIs1 : weight0Count ≡ 1
weight0CountIs1 = refl

weight1CountIs10 : weight1Count ≡ 10
weight1CountIs10 = refl

weight2CountIs40 : weight2Count ≡ 40
weight2CountIs40 = refl

weight3CountIs80 : weight3Count ≡ 80
weight3CountIs80 = refl

weight4CountIs80 : weight4Count ≡ 80
weight4CountIs80 = refl

weight5CountIs32 : weight5Count ≡ 32
weight5CountIs32 = refl

qZeroCount qOneCount qTwoCount : Nat
qZeroCount = weight0Count + weight3Count
qOneCount = weight1Count + weight4Count
qTwoCount = weight2Count + weight5Count

qZeroCountIs81 : qZeroCount ≡ 81
qZeroCountIs81 = refl

qOneCountIs90 : qOneCount ≡ 90
qOneCountIs90 = refl

qTwoCountIs72 : qTwoCount ≡ 72
qTwoCountIs72 = refl

qZeroNonzeroCount : Nat
qZeroNonzeroCount = 80

qZeroNonzeroCountIs80 : qZeroNonzeroCount ≡ 80
qZeroNonzeroCountIs80 = refl

fullT5Count : Nat
fullT5Count = Relative.kernel5ExpectedCount

fullPartitionOneEightyNinetySeventyTwo :
  fullT5Count ≡ 1 + 80 + 90 + 72
fullPartitionOneEightyNinetySeventyTwo = refl

------------------------------------------------------------------------
-- 2. The diagonal 3 + 240 cut is a different decomposition.
--
-- Python and Lean exhaustively check the diagonal Q-pattern as 2,0,2.
-- Therefore removing all three diagonal points removes one Q=0 point and two
-- Q=2 points:
--
--   240 = 80 + 90 + 70.
--
-- Here Agda records the resulting closed arithmetic and the evidence grade.
------------------------------------------------------------------------

diagonalNegativeQ diagonalZeroQ diagonalPositiveQ : Nat
diagonalNegativeQ = 2
diagonalZeroQ = 0
diagonalPositiveQ = 2

relativeQZeroCount relativeQOneCount relativeQTwoCount : Nat
relativeQZeroCount = 80
relativeQOneCount = 90
relativeQTwoCount = 70

relativeCount : Nat
relativeCount = Relative.relativeExpectedCount

relativePartitionEightyNinetySeventy :
  relativeCount ≡ relativeQZeroCount + relativeQOneCount + relativeQTwoCount
relativePartitionEightyNinetySeventy = refl

qTwoFullCountSplitsDiagonalTwoPlusRelativeSeventy :
  qTwoCount ≡ 2 + relativeQTwoCount
qTwoFullCountSplitsDiagonalTwoPlusRelativeSeventy = refl

qZeroFullCountSplitsDiagonalOnePlusRelativeEighty :
  qZeroCount ≡ 1 + relativeQZeroCount
qZeroFullCountSplitsDiagonalOnePlusRelativeEighty = refl

------------------------------------------------------------------------
-- 3. Existing exceptional-prior row agrees at the cardinality coordinate.
--
-- This is count agreement only; no E6 action or root-shell same-object theorem
-- is manufactured on the Agda side here.
------------------------------------------------------------------------

e6PriorRootCountIs72 : Exceptional.rootCount Exceptional.e6RootPrior ≡ 72
e6PriorRootCountIs72 = refl

e6PriorCountMatchesQTwo : Exceptional.rootCount Exceptional.e6RootPrior ≡ qTwoCount
e6PriorCountMatchesQTwo = refl

------------------------------------------------------------------------
-- 4. Cross-language execution receipt.
------------------------------------------------------------------------

record CrossLanguageQuadraticReceipt : Set where
  constructor cross-language-quadratic-receipt
  field
    pythonFullT5Enumeration : Bool
    pythonDiagonalQPatternChecked : Bool
    pythonE6RootEnumeration72 : Bool
    pythonE6Mod3RadicalChecked : Bool
    pythonE6RootToQTwoBijectionChecked : Bool
    pythonE6CoxeterRelationsChecked : Bool
    leanSourceWritten : Bool
    leanKernelVerified : Bool
    agdaConcreteKernel5EnumerationProvedHere : Bool
    agdaE6RootBijectionProvedHere : Bool
    evidenceNote : String

open CrossLanguageQuadraticReceipt public

canonicalCrossLanguageQuadraticReceipt : CrossLanguageQuadraticReceipt
canonicalCrossLanguageQuadraticReceipt =
  cross-language-quadratic-receipt
    true true true true true true
    true false
    false false
    "Python exhaustively checked the finite mathematics; Lean owners are source-written; no exact-head Lean/Agda kernel receipt is available in this connector session."

------------------------------------------------------------------------
-- 5. Non-collapse boundary.
------------------------------------------------------------------------

record T5QuadraticOrbitBoundary : Set where
  constructor t5-quadratic-orbit-boundary
  field
    combinatorialQPartitionPaid : Bool
    qTwoCountMatchesE6RootPriorCount : Bool
    diagonalCutDistinctFromQuadraticOrbitCut : Bool
    relative240IsQTwoShell : Bool
    qTwoShellAutomaticallyE6Action : Bool
    qTwoShellAutomaticallyE8Roots : Bool
    countMatchCreatesSameObjectRecognition : Bool

open T5QuadraticOrbitBoundary public

canonicalT5QuadraticOrbitBoundary : T5QuadraticOrbitBoundary
canonicalT5QuadraticOrbitBoundary =
  t5-quadratic-orbit-boundary
    true true true
    false false false false

reflRelativeNotQTwo :
  relative240IsQTwoShell canonicalT5QuadraticOrbitBoundary ≡ false
reflRelativeNotQTwo = refl

reflLeanKernelUnverified :
  leanKernelVerified canonicalCrossLanguageQuadraticReceipt ≡ false
reflLeanKernelUnverified = refl
