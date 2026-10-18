module DASHI.Physics.YangMills.BalabanClayP3CanonicalRationalConstrainedSumExact where

------------------------------------------------------------------------
-- CANONICAL RATIONAL INSTANCE OF THE FINITE CONSTRAINED SUM ABI
--
-- BalabanClayP3FiniteConstrainedIntegralExact deliberately abstracts the scalar
-- zero and addition.  The selected finite-probability lane needs the literal
-- rational fold.  This owner supplies the preferred rational presentation
-- without changing any physical carrier, block map, fibre selector or weight.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral

record CanonicalRationalConstrainedSumData
    (Fine Coarse : Set) : Set₁ where
  field
    fineFields : List Fine
    blockMap : Fine → Coarse
    coarseMatches : Fine → Coarse → Bool
    coarseMatchesSound : ∀ fineField coarse →
      coarseMatches fineField coarse ≡ true →
      blockMap fineField ≡ coarse
    coarseMatchesComplete : ∀ fineField coarse →
      blockMap fineField ≡ coarse →
      coarseMatches fineField coarse ≡ true

    isSmall : Fine → Bool
    weight : Fine → ℚ

open CanonicalRationalConstrainedSumData public

canonicalRationalConstrainedSum :
  ∀ {Fine Coarse} →
  CanonicalRationalConstrainedSumData Fine Coarse →
  Integral.FiniteConstrainedSum Fine Coarse ℚ
canonicalRationalConstrainedSum dataSet = record
  { fineFields = fineFields dataSet
  ; blockMap = blockMap dataSet
  ; coarseMatches = coarseMatches dataSet
  ; coarseMatchesSound = coarseMatchesSound dataSet
  ; coarseMatchesComplete = coarseMatchesComplete dataSet
  ; isSmall = isSmall dataSet
  ; weight = weight dataSet
  ; zero = 0ℚ
  ; add = _+_
  ; addZeroLeft = λ value → ℚRing.solve-∀ value
  ; addZeroRight = λ value → ℚRing.solve-∀ value
  ; interchange = λ first second third fourth →
      ℚRing.solve-∀ first second third fourth
  }

canonicalZeroIsRationalZero :
  ∀ {Fine Coarse}
    (dataSet : CanonicalRationalConstrainedSumData Fine Coarse) →
  Integral.zero (canonicalRationalConstrainedSum dataSet) ≡ 0ℚ
canonicalZeroIsRationalZero dataSet = refl

canonicalAddIsRationalAdd :
  ∀ {Fine Coarse}
    (dataSet : CanonicalRationalConstrainedSumData Fine Coarse)
    left right →
  Integral.add (canonicalRationalConstrainedSum dataSet) left right
  ≡ left + right
canonicalAddIsRationalAdd dataSet left right = refl

canonicalRationalConstrainedSumLevel : ProofLevel
canonicalRationalConstrainedSumLevel = machineChecked

canonicalRationalFoldArithmeticLevel : ProofLevel
canonicalRationalFoldArithmeticLevel = machineChecked
