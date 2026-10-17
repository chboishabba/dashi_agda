module DASHI.Analysis.CollatzSyracuseParadoxicalPrefixExact where

------------------------------------------------------------------------
-- PARADOXICAL PREFIXES ON THE LITERAL SYRACUSE CARRIER
--
-- The external paradoxical-sequence literature motivates a distinction that
-- the repo's exact affine normal form makes lossless:
--
--   multiplicative coefficient data:  2^m versus 3^(ones w)
--   additive orbit data:               A(w)
--
-- The odd count controls only the first coordinate.  Literal descent requires
-- the additive correction to fit inside the positive coefficient gap.
--
-- This module owns that same-object seam.  It does not import any external
-- theorem and does not claim that classifying paradoxical prefixes eliminates
-- the universal residual tail.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Nat using (_<_; _≤_)
import Data.Nat.Properties as NatP
open import Relation.Nullary using (¬_; _≢_)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseUniformWordDescentCertificateExact as Uniform

------------------------------------------------------------------------
-- Exact positive multiplicative gap.
------------------------------------------------------------------------

record ContractingCoefficientGap
    {m : Nat}
    (word : Binary.BinaryWord m) : Set where
  constructor contractingCoefficientGap
  field
    gap : Nat
    gapPositive : zero < gap
    denominatorSplit :
      Affine.powNat 2 m
      ≡ Affine.powNat 3 (Affine.parityCount word) + gap

open ContractingCoefficientGap public

contractingCorrectionFitImpliesLiteralDescent :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (coefficient : ContractingCoefficientGap word) →
  (x : Syracuse.PositiveNat) →
  Affine.affineAdditiveTerm word
    < gap coefficient * Syracuse.toNat x →
  Itinerary.parityWord m x ≡ word →
  Syracuse.toNat (Syracuse.syracuseIterate m x)
    < Syracuse.toNat x
contractingCorrectionFitImpliesLiteralDescent
  word coefficient x correctionFits wordMatch =
  Uniform.uniformWordCertificateImpliesDescent
    word
    (record
      { gap = gap coefficient
      ; minimumStart = Syracuse.toNat x
      ; denominatorSplit = denominatorSplit coefficient
      ; correctionBelowGapAtMinimum = correctionFits
      })
    x
    NatP.≤-refl
    wordMatch

------------------------------------------------------------------------
-- Exact same-start paradoxical prefix.
--
-- "Paradoxical" here is a repo-local formal term: the multiplicative
-- coefficient is contracting, but the literal orbit has not descended at the
-- selected horizon.  This is intentionally narrower than any prose usage in
-- an external source.
------------------------------------------------------------------------

record ParadoxicalPrefix
    (x : Syracuse.PositiveNat)
    (m : Nat) : Set where
  constructor paradoxicalPrefix
  field
    coefficientGap :
      ContractingCoefficientGap (Itinerary.parityWord m x)
    noLiteralDescent :
      ¬ (Syracuse.toNat (Syracuse.syracuseIterate m x)
         < Syracuse.toNat x)

open ParadoxicalPrefix public

paradoxicalPrefixBlocksCorrectionFit :
  {x : Syracuse.PositiveNat} {m : Nat} →
  (paradoxical : ParadoxicalPrefix x m) →
  ¬ (Affine.affineAdditiveTerm (Itinerary.parityWord m x)
      < gap (coefficientGap paradoxical) * Syracuse.toNat x)
paradoxicalPrefixBlocksCorrectionFit {x} {m} paradoxical correctionFits =
  noLiteralDescent paradoxical
    (contractingCorrectionFitImpliesLiteralDescent
      (Itinerary.parityWord m x)
      (coefficientGap paradoxical)
      x
      correctionFits
      refl)

-- Because Nat order is decidable/linear, failure of the strict correction-fit
-- inequality gives the exact reverse weak inequality:
--
--     gap * x <= A(actual parity word).
paradoxicalPrefixForcesCorrectionDominance :
  {x : Syracuse.PositiveNat} {m : Nat} →
  (paradoxical : ParadoxicalPrefix x m) →
  gap (coefficientGap paradoxical) * Syracuse.toNat x
  ≤ Affine.affineAdditiveTerm (Itinerary.parityWord m x)
paradoxicalPrefixForcesCorrectionDominance paradoxical =
  NatP.≮⇒≥ (paradoxicalPrefixBlocksCorrectionFit paradoxical)

-- The gap is positive, hence at least one.  A paradoxical start is therefore
-- bounded by the exact correction of its word.  This is a genuine finite
-- exception bound for every fixed contracting cylinder:
--
--     x <= gap*x <= A(w), hence x <= A(w).
paradoxicalPrefixStartBoundedByCorrection :
  {x : Syracuse.PositiveNat} {m : Nat} →
  (paradoxical : ParadoxicalPrefix x m) →
  Syracuse.toNat x
  ≤ Affine.affineAdditiveTerm (Itinerary.parityWord m x)
paradoxicalPrefixStartBoundedByCorrection {x} paradoxical =
  NatP.≤-trans
    (NatP.*-monoˡ-≤
      (Syracuse.toNat x)
      (gapPositive (coefficientGap paradoxical)))
    (paradoxicalPrefixForcesCorrectionDominance paradoxical)

------------------------------------------------------------------------
-- Concrete non-factorability witness for odd-count-only reasoning.
--
-- Both length-five words contain three odd steps.  Their multiplicative
-- coefficient is therefore the same (3^3 against 2^5), but their exact affine
-- corrections are 23 and 29.  Hence odd count / odd proportion cannot by
-- itself recover the exact affine descent margin.
------------------------------------------------------------------------

word11010 : Binary.BinaryWord 5
word11010 =
  Binary.bit1
    (Binary.bit1
      (Binary.bit0
        (Binary.bit1
          (Binary.bit0 Binary.end))))

word10110 : Binary.BinaryWord 5
word10110 =
  Binary.bit1
    (Binary.bit0
      (Binary.bit1
        (Binary.bit1
          (Binary.bit0 Binary.end))))

sameOddCountWitness :
  Affine.parityCount word11010 ≡ Affine.parityCount word10110
sameOddCountWitness = refl

word11010Correction :
  Affine.affineAdditiveTerm word11010 ≡ 23
word11010Correction = refl

word10110Correction :
  Affine.affineAdditiveTerm word10110 ≡ 29
word10110Correction = refl

sameCountDifferentCorrection :
  Affine.affineAdditiveTerm word11010
  ≢ Affine.affineAdditiveTerm word10110
sameCountDifferentCorrection ()

word11010GapFive :
  Affine.powNat 2 5
  ≡ Affine.powNat 3 (Affine.parityCount word11010) + 5
word11010GapFive = refl

word10110GapFive :
  Affine.powNat 2 5
  ≡ Affine.powNat 3 (Affine.parityCount word10110) + 5
word10110GapFive = refl

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record ParadoxicalPrefixBoundary : Set where
  constructor paradoxicalPrefixBoundary
  field
    literalSameStartDefinitionPaid : Nat
    exactPositiveCoefficientGapPaid : Nat
    contractingCorrectionFitImpliesLiteralDescent : Nat
    paradoxicalPrefixForcesCorrectionFailure : Nat
    paradoxicalPrefixForcesExactCorrectionDominance : Nat
    paradoxicalPrefixStartBoundedByCorrectionPaid : Nat
    sameOddCountDoesNotDetermineAffineCorrection : Nat
    externalParadoxicalTheoremImported : Nat
    parityProportionAloneDeterminesStopping : Nat
    paradoxicalClassificationAutomaticallyEliminatesAllResidualStarts : Nat

canonicalParadoxicalPrefixBoundary : ParadoxicalPrefixBoundary
canonicalParadoxicalPrefixBoundary =
  paradoxicalPrefixBoundary 1 1 1 1 1 1 1 0 0 0
