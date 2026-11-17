module DASHI.Analysis.CollatzSyracuseCoefficientResonanceExact where

------------------------------------------------------------------------
-- EXACT COEFFICIENT-RESONANCE COORDINATE
--
-- This module isolates the Diophantine coordinate that controls the
-- multiplicative part of a parity prefix:
--
--   (m , s)  |->  (2^m , 3^s)
--
-- where s is the number of odd steps.  The coordinate is exact integer data;
-- no floating logarithm is needed.  Continued-fraction / Stern-Brocot
-- descriptions from external work may be attached later as separately
-- attributed classifiers of near-equality between 2^m and 3^s.
--
-- Crucially, this coordinate does not recover the affine correction A(w).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)
open import Relation.Nullary using (_≢_)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseParadoxicalPrefixExact as Paradox

record CoefficientCoordinate
    {m : Nat}
    (word : Binary.BinaryWord m) : Set where
  constructor coefficientCoordinate
  field
    lengthCoordinate : Nat
    oddCoordinate : Nat
    twoPower : Nat
    threePower : Nat
    lengthExact : lengthCoordinate ≡ m
    oddExact : oddCoordinate ≡ Affine.parityCount word
    twoPowerExact : twoPower ≡ Affine.powNat 2 m
    threePowerExact :
      threePower ≡ Affine.powNat 3 (Affine.parityCount word)

open CoefficientCoordinate public

canonicalCoefficientCoordinate :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  CoefficientCoordinate word
canonicalCoefficientCoordinate {m} word =
  coefficientCoordinate
    m
    (Affine.parityCount word)
    (Affine.powNat 2 m)
    (Affine.powNat 3 (Affine.parityCount word))
    refl refl refl refl

sameOddCountSameThreePower :
  {m : Nat} →
  (left right : Binary.BinaryWord m) →
  Affine.parityCount left ≡ Affine.parityCount right →
  Affine.powNat 3 (Affine.parityCount left)
    ≡ Affine.powNat 3 (Affine.parityCount right)
sameOddCountSameThreePower left right countMatch =
  cong (Affine.powNat 3) countMatch

------------------------------------------------------------------------
-- Exact collision: same coefficient coordinate, different additive correction.
------------------------------------------------------------------------

witnessSameOddCount :
  Affine.parityCount Paradox.word11010
    ≡ Affine.parityCount Paradox.word10110
witnessSameOddCount = Paradox.sameOddCountWitness

witnessSameThreePower :
  Affine.powNat 3 (Affine.parityCount Paradox.word11010)
    ≡ Affine.powNat 3 (Affine.parityCount Paradox.word10110)
witnessSameThreePower =
  sameOddCountSameThreePower
    Paradox.word11010
    Paradox.word10110
    witnessSameOddCount

witnessDifferentCorrection :
  Affine.affineAdditiveTerm Paradox.word11010
  ≢ Affine.affineAdditiveTerm Paradox.word10110
witnessDifferentCorrection = Paradox.sameCountDifferentCorrection

------------------------------------------------------------------------
-- An attributed near-resonance theorem can feed this interface only by
-- supplying exact integer information.  The source must not merely assert a
-- floating approximation to log_3 2.
------------------------------------------------------------------------

record ExactNearResonanceCertificate
    {m : Nat}
    (word : Binary.BinaryWord m) : Set where
  field
    coefficientGap : Paradox.ContractingCoefficientGap word
    gapCeiling : Nat
    gapWithinCeiling :
      Paradox.gap coefficientGap ≤ gapCeiling

open ExactNearResonanceCertificate public

record CoefficientResonanceBoundary : Set where
  constructor coefficientResonanceBoundary
  field
    exactCoefficientCoordinatePaid : Nat
    sameOddCountSameMultiplicativeCoefficientPaid : Nat
    sameCountSameCoefficientDifferentCorrectionWitnessPaid : Nat
    exactIntegerNearResonanceSocketPaid : Nat

    floatingLogApproximationCountsAsExactCertificate : Nat
    continuedFractionObservationImportedAsUniversalTheorem : Nat
    resonanceCoordinateAutomaticallyDeterminesLiteralDescent : Nat
    boundedNearResonanceEnumerationEliminatesResidualTail : Nat

canonicalCoefficientResonanceBoundary : CoefficientResonanceBoundary
canonicalCoefficientResonanceBoundary =
  coefficientResonanceBoundary
    1 1 1 1
    0 0 0 0
