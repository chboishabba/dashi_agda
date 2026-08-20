module DASHI.Moonshine.P11FiveStatePositiveHeckeAlgebraExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- Jean-Pierre Serre,
-- "Trees", Springer Monographs in Mathematics.
-- DOI: 10.1007/978-3-642-61856-7.
--
-- DASHI CONTRIBUTION
--
-- Test the five-state positive lift against the gates that killed the earlier
-- six-sector model.  All statements are literal path counts on positive
-- neighbour systems; no signed kernel completion is used.
--
-- The three prime systems commute entrywise.  Their prime-square residuals
-- R2^2-2I, R3^2-3I and R5^2-5I are explicitly Nat-valued on every one of the
-- 25 source/target entries.  In particular, positivity survives the unital
-- Hecke-square gate that falsified the natural six-sector quotient.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine

indicator : Fine.P11Fine5 → Fine.P11Fine5 → Nat
indicator Fine.a0 Fine.a0 = 1
indicator Fine.a0 _ = 0
indicator Fine.a1 Fine.a1 = 1
indicator Fine.a1 _ = 0
indicator Fine.b0 Fine.b0 = 1
indicator Fine.b0 _ = 0
indicator Fine.b1 Fine.b1 = 1
indicator Fine.b1 _ = 0
indicator Fine.b2 Fine.b2 = 1
indicator Fine.b2 _ = 0

pathCount :
  Positive.PositiveFiniteNeighbourSystem Fine.P11Fine5 →
  Positive.PositiveFiniteNeighbourSystem Fine.P11Fine5 →
  Fine.P11Fine5 → Fine.P11Fine5 → Nat
pathCount first second source target =
  Positive.twoStepOperator first second (indicator target) source

------------------------------------------------------------------------
-- Pairwise commutation on every matrix entry.
------------------------------------------------------------------------

r2r3CommutesEntry :
  (source target : Fine.P11Fine5) →
  pathCount Fine.R2Positive Fine.R3Positive source target
  ≡ pathCount Fine.R3Positive Fine.R2Positive source target
r2r3CommutesEntry Fine.a0 Fine.a0 = refl
r2r3CommutesEntry Fine.a0 Fine.a1 = refl
r2r3CommutesEntry Fine.a0 Fine.b0 = refl
r2r3CommutesEntry Fine.a0 Fine.b1 = refl
r2r3CommutesEntry Fine.a0 Fine.b2 = refl
r2r3CommutesEntry Fine.a1 Fine.a0 = refl
r2r3CommutesEntry Fine.a1 Fine.a1 = refl
r2r3CommutesEntry Fine.a1 Fine.b0 = refl
r2r3CommutesEntry Fine.a1 Fine.b1 = refl
r2r3CommutesEntry Fine.a1 Fine.b2 = refl
r2r3CommutesEntry Fine.b0 Fine.a0 = refl
r2r3CommutesEntry Fine.b0 Fine.a1 = refl
r2r3CommutesEntry Fine.b0 Fine.b0 = refl
r2r3CommutesEntry Fine.b0 Fine.b1 = refl
r2r3CommutesEntry Fine.b0 Fine.b2 = refl
r2r3CommutesEntry Fine.b1 Fine.a0 = refl
r2r3CommutesEntry Fine.b1 Fine.a1 = refl
r2r3CommutesEntry Fine.b1 Fine.b0 = refl
r2r3CommutesEntry Fine.b1 Fine.b1 = refl
r2r3CommutesEntry Fine.b1 Fine.b2 = refl
r2r3CommutesEntry Fine.b2 Fine.a0 = refl
r2r3CommutesEntry Fine.b2 Fine.a1 = refl
r2r3CommutesEntry Fine.b2 Fine.b0 = refl
r2r3CommutesEntry Fine.b2 Fine.b1 = refl
r2r3CommutesEntry Fine.b2 Fine.b2 = refl

r2r5CommutesEntry :
  (source target : Fine.P11Fine5) →
  pathCount Fine.R2Positive Fine.R5Positive source target
  ≡ pathCount Fine.R5Positive Fine.R2Positive source target
r2r5CommutesEntry Fine.a0 Fine.a0 = refl
r2r5CommutesEntry Fine.a0 Fine.a1 = refl
r2r5CommutesEntry Fine.a0 Fine.b0 = refl
r2r5CommutesEntry Fine.a0 Fine.b1 = refl
r2r5CommutesEntry Fine.a0 Fine.b2 = refl
r2r5CommutesEntry Fine.a1 Fine.a0 = refl
r2r5CommutesEntry Fine.a1 Fine.a1 = refl
r2r5CommutesEntry Fine.a1 Fine.b0 = refl
r2r5CommutesEntry Fine.a1 Fine.b1 = refl
r2r5CommutesEntry Fine.a1 Fine.b2 = refl
r2r5CommutesEntry Fine.b0 Fine.a0 = refl
r2r5CommutesEntry Fine.b0 Fine.a1 = refl
r2r5CommutesEntry Fine.b0 Fine.b0 = refl
r2r5CommutesEntry Fine.b0 Fine.b1 = refl
r2r5CommutesEntry Fine.b0 Fine.b2 = refl
r2r5CommutesEntry Fine.b1 Fine.a0 = refl
r2r5CommutesEntry Fine.b1 Fine.a1 = refl
r2r5CommutesEntry Fine.b1 Fine.b0 = refl
r2r5CommutesEntry Fine.b1 Fine.b1 = refl
r2r5CommutesEntry Fine.b1 Fine.b2 = refl
r2r5CommutesEntry Fine.b2 Fine.a0 = refl
r2r5CommutesEntry Fine.b2 Fine.a1 = refl
r2r5CommutesEntry Fine.b2 Fine.b0 = refl
r2r5CommutesEntry Fine.b2 Fine.b1 = refl
r2r5CommutesEntry Fine.b2 Fine.b2 = refl

r3r5CommutesEntry :
  (source target : Fine.P11Fine5) →
  pathCount Fine.R3Positive Fine.R5Positive source target
  ≡ pathCount Fine.R5Positive Fine.R3Positive source target
r3r5CommutesEntry Fine.a0 Fine.a0 = refl
r3r5CommutesEntry Fine.a0 Fine.a1 = refl
r3r5CommutesEntry Fine.a0 Fine.b0 = refl
r3r5CommutesEntry Fine.a0 Fine.b1 = refl
r3r5CommutesEntry Fine.a0 Fine.b2 = refl
r3r5CommutesEntry Fine.a1 Fine.a0 = refl
r3r5CommutesEntry Fine.a1 Fine.a1 = refl
r3r5CommutesEntry Fine.a1 Fine.b0 = refl
r3r5CommutesEntry Fine.a1 Fine.b1 = refl
r3r5CommutesEntry Fine.a1 Fine.b2 = refl
r3r5CommutesEntry Fine.b0 Fine.a0 = refl
r3r5CommutesEntry Fine.b0 Fine.a1 = refl
r3r5CommutesEntry Fine.b0 Fine.b0 = refl
r3r5CommutesEntry Fine.b0 Fine.b1 = refl
r3r5CommutesEntry Fine.b0 Fine.b2 = refl
r3r5CommutesEntry Fine.b1 Fine.a0 = refl
r3r5CommutesEntry Fine.b1 Fine.a1 = refl
r3r5CommutesEntry Fine.b1 Fine.b0 = refl
r3r5CommutesEntry Fine.b1 Fine.b1 = refl
r3r5CommutesEntry Fine.b1 Fine.b2 = refl
r3r5CommutesEntry Fine.b2 Fine.a0 = refl
r3r5CommutesEntry Fine.b2 Fine.a1 = refl
r3r5CommutesEntry Fine.b2 Fine.b0 = refl
r3r5CommutesEntry Fine.b2 Fine.b1 = refl
r3r5CommutesEntry Fine.b2 Fine.b2 = refl

------------------------------------------------------------------------
-- Explicit positive residual matrices.
------------------------------------------------------------------------

r4Multiplicity : Fine.P11Fine5 → Fine.P11Fine5 → Nat
r4Multiplicity Fine.a0 Fine.a0 = 1
r4Multiplicity Fine.a0 Fine.a1 = 3
r4Multiplicity Fine.a0 Fine.b0 = 1
r4Multiplicity Fine.a0 Fine.b1 = 1
r4Multiplicity Fine.a0 Fine.b2 = 1
r4Multiplicity Fine.a1 Fine.a0 = 3
r4Multiplicity Fine.a1 Fine.a1 = 1
r4Multiplicity Fine.a1 Fine.b0 = 1
r4Multiplicity Fine.a1 Fine.b1 = 1
r4Multiplicity Fine.a1 Fine.b2 = 1
r4Multiplicity Fine.b0 Fine.a0 = 1
r4Multiplicity Fine.b0 Fine.a1 = 1
r4Multiplicity Fine.b0 Fine.b0 = 1
r4Multiplicity Fine.b0 Fine.b1 = 2
r4Multiplicity Fine.b0 Fine.b2 = 2
r4Multiplicity Fine.b1 Fine.a0 = 1
r4Multiplicity Fine.b1 Fine.a1 = 1
r4Multiplicity Fine.b1 Fine.b0 = 2
r4Multiplicity Fine.b1 Fine.b1 = 1
r4Multiplicity Fine.b1 Fine.b2 = 2
r4Multiplicity Fine.b2 Fine.a0 = 1
r4Multiplicity Fine.b2 Fine.a1 = 1
r4Multiplicity Fine.b2 Fine.b0 = 2
r4Multiplicity Fine.b2 Fine.b1 = 2
r4Multiplicity Fine.b2 Fine.b2 = 1

r9Multiplicity : Fine.P11Fine5 → Fine.P11Fine5 → Nat
r9Multiplicity Fine.a0 Fine.a0 = 1
r9Multiplicity Fine.a0 Fine.a1 = 3
r9Multiplicity Fine.a0 Fine.b0 = 3
r9Multiplicity Fine.a0 Fine.b1 = 3
r9Multiplicity Fine.a0 Fine.b2 = 3
r9Multiplicity Fine.a1 Fine.a0 = 3
r9Multiplicity Fine.a1 Fine.a1 = 1
r9Multiplicity Fine.a1 Fine.b0 = 3
r9Multiplicity Fine.a1 Fine.b1 = 3
r9Multiplicity Fine.a1 Fine.b2 = 3
r9Multiplicity Fine.b0 Fine.a0 = 3
r9Multiplicity Fine.b0 Fine.a1 = 3
r9Multiplicity Fine.b0 Fine.b0 = 1
r9Multiplicity Fine.b0 Fine.b1 = 3
r9Multiplicity Fine.b0 Fine.b2 = 3
r9Multiplicity Fine.b1 Fine.a0 = 3
r9Multiplicity Fine.b1 Fine.a1 = 3
r9Multiplicity Fine.b1 Fine.b0 = 3
r9Multiplicity Fine.b1 Fine.b1 = 1
r9Multiplicity Fine.b1 Fine.b2 = 3
r9Multiplicity Fine.b2 Fine.a0 = 3
r9Multiplicity Fine.b2 Fine.a1 = 3
r9Multiplicity Fine.b2 Fine.b0 = 3
r9Multiplicity Fine.b2 Fine.b1 = 3
r9Multiplicity Fine.b2 Fine.b2 = 1

r25Multiplicity : Fine.P11Fine5 → Fine.P11Fine5 → Nat
r25Multiplicity Fine.a0 Fine.a0 = 7
r25Multiplicity Fine.a0 Fine.a1 = 3
r25Multiplicity Fine.a0 Fine.b0 = 7
r25Multiplicity Fine.a0 Fine.b1 = 7
r25Multiplicity Fine.a0 Fine.b2 = 7
r25Multiplicity Fine.a1 Fine.a0 = 3
r25Multiplicity Fine.a1 Fine.a1 = 7
r25Multiplicity Fine.a1 Fine.b0 = 7
r25Multiplicity Fine.a1 Fine.b1 = 7
r25Multiplicity Fine.a1 Fine.b2 = 7
r25Multiplicity Fine.b0 Fine.a0 = 7
r25Multiplicity Fine.b0 Fine.a1 = 7
r25Multiplicity Fine.b0 Fine.b0 = 5
r25Multiplicity Fine.b0 Fine.b1 = 6
r25Multiplicity Fine.b0 Fine.b2 = 6
r25Multiplicity Fine.b1 Fine.a0 = 7
r25Multiplicity Fine.b1 Fine.a1 = 7
r25Multiplicity Fine.b1 Fine.b0 = 6
r25Multiplicity Fine.b1 Fine.b1 = 5
r25Multiplicity Fine.b1 Fine.b2 = 6
r25Multiplicity Fine.b2 Fine.a0 = 7
r25Multiplicity Fine.b2 Fine.a1 = 7
r25Multiplicity Fine.b2 Fine.b0 = 6
r25Multiplicity Fine.b2 Fine.b1 = 6
r25Multiplicity Fine.b2 Fine.b2 = 5

r2SquareEntry :
  (source target : Fine.P11Fine5) →
  pathCount Fine.R2Positive Fine.R2Positive source target
  ≡ r4Multiplicity source target + 2 * indicator target source
r2SquareEntry Fine.a0 Fine.a0 = refl
r2SquareEntry Fine.a0 Fine.a1 = refl
r2SquareEntry Fine.a0 Fine.b0 = refl
r2SquareEntry Fine.a0 Fine.b1 = refl
r2SquareEntry Fine.a0 Fine.b2 = refl
r2SquareEntry Fine.a1 Fine.a0 = refl
r2SquareEntry Fine.a1 Fine.a1 = refl
r2SquareEntry Fine.a1 Fine.b0 = refl
r2SquareEntry Fine.a1 Fine.b1 = refl
r2SquareEntry Fine.a1 Fine.b2 = refl
r2SquareEntry Fine.b0 Fine.a0 = refl
r2SquareEntry Fine.b0 Fine.a1 = refl
r2SquareEntry Fine.b0 Fine.b0 = refl
r2SquareEntry Fine.b0 Fine.b1 = refl
r2SquareEntry Fine.b0 Fine.b2 = refl
r2SquareEntry Fine.b1 Fine.a0 = refl
r2SquareEntry Fine.b1 Fine.a1 = refl
r2SquareEntry Fine.b1 Fine.b0 = refl
r2SquareEntry Fine.b1 Fine.b1 = refl
r2SquareEntry Fine.b1 Fine.b2 = refl
r2SquareEntry Fine.b2 Fine.a0 = refl
r2SquareEntry Fine.b2 Fine.a1 = refl
r2SquareEntry Fine.b2 Fine.b0 = refl
r2SquareEntry Fine.b2 Fine.b1 = refl
r2SquareEntry Fine.b2 Fine.b2 = refl

r3SquareEntry :
  (source target : Fine.P11Fine5) →
  pathCount Fine.R3Positive Fine.R3Positive source target
  ≡ r9Multiplicity source target + 3 * indicator target source
r3SquareEntry Fine.a0 Fine.a0 = refl
r3SquareEntry Fine.a0 Fine.a1 = refl
r3SquareEntry Fine.a0 Fine.b0 = refl
r3SquareEntry Fine.a0 Fine.b1 = refl
r3SquareEntry Fine.a0 Fine.b2 = refl
r3SquareEntry Fine.a1 Fine.a0 = refl
r3SquareEntry Fine.a1 Fine.a1 = refl
r3SquareEntry Fine.a1 Fine.b0 = refl
r3SquareEntry Fine.a1 Fine.b1 = refl
r3SquareEntry Fine.a1 Fine.b2 = refl
r3SquareEntry Fine.b0 Fine.a0 = refl
r3SquareEntry Fine.b0 Fine.a1 = refl
r3SquareEntry Fine.b0 Fine.b0 = refl
r3SquareEntry Fine.b0 Fine.b1 = refl
r3SquareEntry Fine.b0 Fine.b2 = refl
r3SquareEntry Fine.b1 Fine.a0 = refl
r3SquareEntry Fine.b1 Fine.a1 = refl
r3SquareEntry Fine.b1 Fine.b0 = refl
r3SquareEntry Fine.b1 Fine.b1 = refl
r3SquareEntry Fine.b1 Fine.b2 = refl
r3SquareEntry Fine.b2 Fine.a0 = refl
r3SquareEntry Fine.b2 Fine.a1 = refl
r3SquareEntry Fine.b2 Fine.b0 = refl
r3SquareEntry Fine.b2 Fine.b1 = refl
r3SquareEntry Fine.b2 Fine.b2 = refl

r5SquareEntry :
  (source target : Fine.P11Fine5) →
  pathCount Fine.R5Positive Fine.R5Positive source target
  ≡ r25Multiplicity source target + 5 * indicator target source
r5SquareEntry Fine.a0 Fine.a0 = refl
r5SquareEntry Fine.a0 Fine.a1 = refl
r5SquareEntry Fine.a0 Fine.b0 = refl
r5SquareEntry Fine.a0 Fine.b1 = refl
r5SquareEntry Fine.a0 Fine.b2 = refl
r5SquareEntry Fine.a1 Fine.a0 = refl
r5SquareEntry Fine.a1 Fine.a1 = refl
r5SquareEntry Fine.a1 Fine.b0 = refl
r5SquareEntry Fine.a1 Fine.b1 = refl
r5SquareEntry Fine.a1 Fine.b2 = refl
r5SquareEntry Fine.b0 Fine.a0 = refl
r5SquareEntry Fine.b0 Fine.a1 = refl
r5SquareEntry Fine.b0 Fine.b0 = refl
r5SquareEntry Fine.b0 Fine.b1 = refl
r5SquareEntry Fine.b0 Fine.b2 = refl
r5SquareEntry Fine.b1 Fine.a0 = refl
r5SquareEntry Fine.b1 Fine.a1 = refl
r5SquareEntry Fine.b1 Fine.b0 = refl
r5SquareEntry Fine.b1 Fine.b1 = refl
r5SquareEntry Fine.b1 Fine.b2 = refl
r5SquareEntry Fine.b2 Fine.a0 = refl
r5SquareEntry Fine.b2 Fine.a1 = refl
r5SquareEntry Fine.b2 Fine.b0 = refl
r5SquareEntry Fine.b2 Fine.b1 = refl
r5SquareEntry Fine.b2 Fine.b2 = refl

record P11FiveStatePositiveHeckeAlgebraBoundary : Set where
  field
    allThreePrimePairsCommuteOnEveryEntry : Bool
    allThreePrimePairsCommuteOnEveryEntryIsTrue :
      allThreePrimePairsCommuteOnEveryEntry ≡ true

    ell2SquareResidualEntrywiseNonnegative : Bool
    ell2SquareResidualEntrywiseNonnegativeIsTrue :
      ell2SquareResidualEntrywiseNonnegative ≡ true

    ell3SquareResidualEntrywiseNonnegative : Bool
    ell3SquareResidualEntrywiseNonnegativeIsTrue :
      ell3SquareResidualEntrywiseNonnegative ≡ true

    ell5SquareResidualEntrywiseNonnegative : Bool
    ell5SquareResidualEntrywiseNonnegativeIsTrue :
      ell5SquareResidualEntrywiseNonnegative ≡ true

    fullPositivePrimeSquareNeighbourListsConstructedHere : Bool
    fullPositivePrimeSquareNeighbourListsConstructedHereIsFalse :
      fullPositivePrimeSquareNeighbourListsConstructedHere ≡ false

    classicalQuaternionGeometryIdentifiedHere : Bool
    classicalQuaternionGeometryIdentifiedHereIsFalse :
      classicalQuaternionGeometryIdentifiedHere ≡ false

canonicalP11FiveStatePositiveHeckeAlgebraBoundary :
  P11FiveStatePositiveHeckeAlgebraBoundary
canonicalP11FiveStatePositiveHeckeAlgebraBoundary =
  record
    { allThreePrimePairsCommuteOnEveryEntry = true
    ; allThreePrimePairsCommuteOnEveryEntryIsTrue = refl
    ; ell2SquareResidualEntrywiseNonnegative = true
    ; ell2SquareResidualEntrywiseNonnegativeIsTrue = refl
    ; ell3SquareResidualEntrywiseNonnegative = true
    ; ell3SquareResidualEntrywiseNonnegativeIsTrue = refl
    ; ell5SquareResidualEntrywiseNonnegative = true
    ; ell5SquareResidualEntrywiseNonnegativeIsTrue = refl
    ; fullPositivePrimeSquareNeighbourListsConstructedHere = false
    ; fullPositivePrimeSquareNeighbourListsConstructedHereIsFalse = refl
    ; classicalQuaternionGeometryIdentifiedHere = false
    ; classicalQuaternionGeometryIdentifiedHereIsFalse = refl
    }
