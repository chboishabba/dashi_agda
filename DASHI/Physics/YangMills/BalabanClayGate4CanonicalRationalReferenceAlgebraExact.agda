module DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalReferenceAlgebraExact where

------------------------------------------------------------------------
-- CANONICAL RATIONAL ALGEBRAS FOR GATE4 REFERENCE NORMALIZATION
--
-- This owner removes the remaining scalar-algebra freedom on the preferred
-- finite reference lane:
--
--   zero        = 0
--   add         = rational addition
--   one         = 1
--   multiply    = rational multiplication
--   Nonnegative = ordinary rational 0 <= q
--   Positive    = ordinary rational 0 < q
--
-- All closure laws are standard exact rational order/ring facts.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; Positive; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP3CanonicalRationalConstrainedSumExact as RationalSum
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibreNormalizationExact as Reference
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal

positiveZeroImpossible : Positive 0ℚ → PositiveMass.Empty
positiveZeroImpossible ()

canonicalReferenceAlgebra :
  ∀ {Fine Coarse} →
  (dataSet : RationalSum.CanonicalRationalConstrainedSumData Fine Coarse) →
  Reference.FiniteReferenceFibreAlgebra
    (RationalSum.canonicalRationalConstrainedSum dataSet)
canonicalReferenceAlgebra dataSet = record
  { one = 1ℚ
  ; multiply = _*_
  ; multiplyZeroRight = λ value → ℚRing.solve-∀ value
  ; distributeLeftOverAdd = λ coefficient left right →
      ℚRing.solve-∀ coefficient left right
  ; multiplyOneRight = λ value → ℚRing.solve-∀ value
  }

canonicalPositiveFoldAlgebra :
  ∀ {Fine Coarse} →
  (dataSet : RationalSum.CanonicalRationalConstrainedSumData Fine Coarse) →
  PositiveMass.PositiveFiniteFoldAlgebra
    (RationalSum.canonicalRationalConstrainedSum dataSet)
canonicalPositiveFoldAlgebra dataSet = record
  { Nonnegative = λ value → 0ℚ ≤ value
  ; Positive = Positive
  ; zeroNonnegative = ℚP.≤-refl
  ; addNonnegative = λ {left} {right} leftNN rightNN →
      ℚP.+-mono-≤ leftNN rightNN
  ; addPositiveLeft = λ {left} {right} leftPositive rightNN →
      let
        raw : 0ℚ + 0ℚ < left + right
        raw = ℚP.+-mono-<-≤ leftPositive rightNN
      in
      subst
        (λ lower → lower < left + right)
        (ℚRing.solve [])
        raw
  ; addPositiveRight = λ {left} {right} leftNN rightPositive →
      let
        raw : 0ℚ + 0ℚ < left + right
        raw = ℚP.+-mono-≤-< leftNN rightPositive
      in
      subst
        (λ lower → lower < left + right)
        (ℚRing.solve [])
        raw
  ; positiveImpliesNonzero = λ {value} positive valueZero →
      positiveZeroImpossible (subst Positive valueZero positive)
  }

canonicalRationalPositiveMassInterpretation :
  ∀ {Fine Coarse}
    (dataSet : RationalSum.CanonicalRationalConstrainedSumData Fine Coarse) →
  Reciprocal.RationalPositiveMassInterpretation
    (canonicalReferenceAlgebra dataSet)
    (canonicalPositiveFoldAlgebra dataSet)
canonicalRationalPositiveMassInterpretation dataSet = record
  { positiveMeansRationalPositive = λ positive → positive
  ; multiplyMeaning = λ left right → refl
  ; oneMeaning = refl
  }

canonicalReferenceAlgebraLevel : ProofLevel
canonicalReferenceAlgebraLevel = machineChecked

canonicalPositiveFoldAlgebraLevel : ProofLevel
canonicalPositiveFoldAlgebraLevel = machineChecked

canonicalRationalPositiveMassInterpretationLevel : ProofLevel
canonicalRationalPositiveMassInterpretationLevel = machineChecked
