module DASHI.Mathematics.NumberTheory.EisensteinLatticeCountingExact where

------------------------------------------------------------------------
-- EISENSTEIN LATTICE: SAME CARRIER, DISTINCT COUNTING LAWS
--
-- Reuses the repository's executable positive-divisor scanner and the
-- existing exact three-phase/six-unit Eisenstein owner.  This module does
-- not identify norm shells, graph-radius shells, wedge counts, or Pascal
-- path multiplicities merely because they can be drawn on the same
-- triangular/A2 carrier.
--
-- The arithmetic shell law implemented here is the divisor side of
--
--   r_hex(n) = 6 * sum_{d|n} chi_{-3}(d),
--
-- represented constructively as the difference between the numbers of
-- positive divisors congruent to 1 and 2 modulo 3.  Identification of this
-- executable arithmetic function with an independently constructed finite
-- fibre of a^2-a*b+b^2 is kept as an explicit bridge obligation below.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (Nat; zero; suc; _+_; _*_; _∸_)

import DASHI.Mathematics.NumberTheory.FiniteDivisorSumExact as Divisor
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Biology.EisensteinThreeSixSymmetryExact as ThreeSix

------------------------------------------------------------------------
-- 1. Triangular / graph-radius counting.
------------------------------------------------------------------------

triangularNumber : Nat → Nat
triangularNumber zero = 0
triangularNumber (suc k) = triangularNumber k + suc k

hexShellCount : Nat → Nat
hexShellCount zero = 1
hexShellCount (suc k) = 6 * suc k

hexBallCount : Nat → Nat
hexBallCount k = 1 + 6 * triangularNumber k

wedgeRowCount : Nat → Nat
wedgeRowCount k = suc k

wedgeTriangleCount : Nat → Nat
wedgeTriangleCount k = triangularNumber (suc k)

------------------------------------------------------------------------
-- 2. Pascal paths in an oriented two-generator wedge.
------------------------------------------------------------------------

choose : Nat → Nat → Nat
choose zero zero = 1
choose zero (suc k) = 0
choose (suc n) zero = 1
choose (suc n) (suc k) = choose n k + choose n (suc k)

binaryPathTotal : Nat → Nat
binaryPathTotal zero = 1
binaryPathTotal (suc n) = 2 * binaryPathTotal n

------------------------------------------------------------------------
-- 3. Executable chi_{-3} divisor shell law.
--
-- Instead of introducing signed arithmetic into the existing Nat fold, keep
-- the positive and negative residue contributions separately and subtract
-- only after folding the positive-divisor list.
------------------------------------------------------------------------

chiMinus3Positive : Nat → Nat
chiMinus3Positive zero = 0
chiMinus3Positive (suc zero) = 1
chiMinus3Positive (suc (suc zero)) = 0
chiMinus3Positive (suc (suc (suc n))) = chiMinus3Positive n

chiMinus3Negative : Nat → Nat
chiMinus3Negative zero = 0
chiMinus3Negative (suc zero) = 0
chiMinus3Negative (suc (suc zero)) = 1
chiMinus3Negative (suc (suc (suc n))) = chiMinus3Negative n

chiMinus3PositiveDivisorCount : Nat → Nat
chiMinus3PositiveDivisorCount n =
  Reindex.foldNat chiMinus3Positive (Divisor.positiveDivisors n)

chiMinus3NegativeDivisorCount : Nat → Nat
chiMinus3NegativeDivisorCount n =
  Reindex.foldNat chiMinus3Negative (Divisor.positiveDivisors n)

chiMinus3DivisorBalance : Nat → Nat
chiMinus3DivisorBalance n =
  chiMinus3PositiveDivisorCount n ∸ chiMinus3NegativeDivisorCount n

eisensteinDivisorShellCount : Nat → Nat
eisensteinDivisorShellCount n = 6 * chiMinus3DivisorBalance n

------------------------------------------------------------------------
-- 4. Reuse the already-owned six-unit theorem rather than rebuilding a
-- second phase/unit carrier.
------------------------------------------------------------------------

existingEisensteinUnitCount : Nat
existingEisensteinUnitCount = ThreeSix.eisensteinUnitCount

existingEisensteinUnitCountIsSix : existingEisensteinUnitCount ≡ 6
existingEisensteinUnitCountIsSix = ThreeSix.eisensteinUnitCountIsSix

------------------------------------------------------------------------
-- 5. Concrete non-collapse witnesses.
------------------------------------------------------------------------

hexShellTwoIsTwelve : hexShellCount 2 ≡ 12
hexShellTwoIsTwelve = refl

normShellTwoIsZero : eisensteinDivisorShellCount 2 ≡ 0
normShellTwoIsZero = refl

hexShellIsNotNormShellAtTwo :
  hexShellCount 2 ≡ eisensteinDivisorShellCount 2 → ⊥
hexShellIsNotNormShellAtTwo ()

wedgeTriangleThreeIsTen : wedgeTriangleCount 3 ≡ 10
wedgeTriangleThreeIsTen = refl

binaryPathTotalThreeIsEight : binaryPathTotal 3 ≡ 8
binaryPathTotalThreeIsEight = refl

wedgeTriangleIsNotBinaryPathTotalAtThree :
  wedgeTriangleCount 3 ≡ binaryPathTotal 3 → ⊥
wedgeTriangleIsNotBinaryPathTotalAtThree ()

------------------------------------------------------------------------
-- 6. Same-object bridge obligation.
--
-- A future geometric owner may independently enumerate the actual finite
-- fibres of Q(a,b)=a^2-a*b+b^2.  Promotion to the classical representation
-- theorem requires that independently constructed count to equal the divisor
-- function above for every n.  This interface prevents the divisor formula
-- from being silently relabelled as a geometric enumeration theorem.
------------------------------------------------------------------------

record EisensteinNormRepresentationBridge : Set₁ where
  constructor eisenstein-norm-representation-bridge
  field
    representationCount : Nat → Nat
    representationCountAgreesWithDivisorLaw :
      (n : Nat) → representationCount n ≡ eisensteinDivisorShellCount n

------------------------------------------------------------------------
-- 7. Claim-strength / cross-pollination boundary.
------------------------------------------------------------------------

record EisensteinLatticeCountingBoundary : Set where
  constructor eisenstein-lattice-counting-boundary
  field
    existingThreeSixUnitOwnerReused : Bool
    positiveDivisorScannerReused : Bool
    triangularAndHexCountsExecutable : Bool
    pascalPathCountsExecutable : Bool
    chiMinus3DivisorShellExecutable : Bool
    graphRadiusShellEqualsNormShell : Bool
    wedgeTriangleEqualsPascalPathTotal : Bool
    divisorFormulaAlreadyGeometricNormFibreTheorem : Bool
    ternaryCountImpliesE6Identification : Bool
    modularEisensteinSeriesIdentifiedWithEisensteinIntegerShells : Bool
    reading : String
open EisensteinLatticeCountingBoundary public

canonicalEisensteinLatticeCountingBoundary : EisensteinLatticeCountingBoundary
canonicalEisensteinLatticeCountingBoundary =
  eisenstein-lattice-counting-boundary
    true true true true true
    false false false false false
    "One triangular/A2-style carrier supports several distinct observables: graph radius, wedge size, directed path multiplicity, and the chi_-3 divisor shell law. Matching 3/6 structure is not by itself an E6, modular-form, or physical identification; the geometric norm-fibre representation theorem remains an explicit same-object bridge."
