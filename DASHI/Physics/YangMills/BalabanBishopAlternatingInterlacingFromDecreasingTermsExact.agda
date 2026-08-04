module DASHI.Physics.YangMills.BalabanBishopAlternatingInterlacingFromDecreasingTermsExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- PURPOSE
-- Prove the concrete alternating interlacing theorem once and for all.  A
-- convergent series whose even terms are +m_{2n}, odd terms are -m_{2n+1}, and
-- whose nonnegative magnitudes decrease has increasing even partial sums,
-- decreasing odd partial sums, a common represented limit, and exact
-- first-omitted adjacent differences.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_<_; s≤s)
import Data.Nat.Properties as NatProperties
open import Data.Product.Base using (_,_)

import Real as BishopReal
import RealProperties as BishopProperties
import Sequence as BishopSequence

import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Interlacing
import DASHI.Physics.YangMills.BalabanBishopSetoidAlternatingFirstOmittedExact as Alternating
open import DASHI.Physics.YangMills.CompactLieProofLevel

double : Nat → Nat
double zero = zero
double (suc index) = suc (suc (double index))

doubleStrictlyIncreases :
  ∀ index → double index < double (suc index)
doubleStrictlyIncreases index =
  s≤s (NatProperties.n≤1+n (double index))

oddIndexStrictlyIncreases :
  ∀ index → suc (double index) < suc (double (suc index))
oddIndexStrictlyIncreases index =
  s≤s (doubleStrictlyIncreases index)

record AlternatingDecreasingSeriesData : Set₁ where
  field
    term magnitude : Nat → BishopReal.ℝ
    representedLimit : BishopReal.ℝ

    magnitudeNonnegative :
      ∀ index → BishopReal.NonNegative (magnitude index)

    magnitudeDecreasing :
      ∀ index →
      BishopReal._≤_ (magnitude (suc index)) (magnitude index)

    evenTermIsPositiveMagnitude :
      ∀ index →
      BishopReal._≃_
        (term (double index))
        (magnitude (double index))

    oddTermIsNegativeMagnitude :
      ∀ index →
      BishopReal._≃_
        (term (suc (double index)))
        (BishopReal.- (magnitude (suc (double index))))

    seriesConvergesToRepresentedLimit :
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf term)
        representedLimit

open AlternatingDecreasingSeriesData public

lowerPartial upperPartial nextLowerPartial :
  AlternatingDecreasingSeriesData → Nat → BishopReal.ℝ
lowerPartial dataSet index =
  BishopSequence.SeriesOf (term dataSet) (double index)

upperPartial dataSet index =
  BishopSequence.SeriesOf (term dataSet) (suc (double index))

nextLowerPartial dataSet index =
  lowerPartial dataSet (suc index)

lowerSuccessorExpansion :
  (dataSet : AlternatingDecreasingSeriesData) →
  ∀ index →
  BishopReal._≃_
    (lowerPartial dataSet (suc index))
    (BishopReal._+_
      (lowerPartial dataSet index)
      (BishopReal._-_
        (magnitude dataSet (double index))
        (magnitude dataSet (suc (double index)))))
lowerSuccessorExpansion dataSet index =
  let
    partial = lowerPartial dataSet index
    evenMagnitude = magnitude dataSet (double index)
    oddMagnitude = magnitude dataSet (suc (double index))
  in
  BishopProperties.≃-trans
    (BishopProperties.+-cong
      (BishopProperties.+-cong
        BishopProperties.≃-refl
        (evenTermIsPositiveMagnitude dataSet index))
      (oddTermIsNegativeMagnitude dataSet index))
    (let open BishopProperties.ℝ-Solver
     in solve 3
        (λ s a b → (s ⊕ a) ⊕ (⊝ b) ⊜ s ⊕ (a ⊖ b))
        BishopProperties.≃-refl
        partial evenMagnitude oddMagnitude)

upperSuccessorExpansion :
  (dataSet : AlternatingDecreasingSeriesData) →
  ∀ index →
  BishopReal._≃_
    (upperPartial dataSet (suc index))
    (BishopReal._+_
      (BishopReal._-_
        (upperPartial dataSet index)
        (magnitude dataSet (suc (double index))))
      (magnitude dataSet (suc (suc (double index)))))
upperSuccessorExpansion dataSet index =
  let
    currentUpper = upperPartial dataSet index
    oddMagnitude = magnitude dataSet (suc (double index))
    nextEvenMagnitude = magnitude dataSet (suc (suc (double index)))
  in
  BishopProperties.≃-trans
    (BishopProperties.+-cong
      (BishopProperties.+-cong
        BishopProperties.≃-refl
        (oddTermIsNegativeMagnitude dataSet index))
      (evenTermIsPositiveMagnitude dataSet (suc index)))
    (let open BishopProperties.ℝ-Solver
     in solve 3
        (λ s b c → (s ⊕ (⊝ b)) ⊕ c ⊜ (s ⊖ b) ⊕ c)
        BishopProperties.≃-refl
        currentUpper oddMagnitude nextEvenMagnitude)

lowerPartialIncreasing :
  (dataSet : AlternatingDecreasingSeriesData) →
  BishopSequence._isIncreasing (lowerPartial dataSet)
lowerPartialIncreasing dataSet index =
  let
    partial = lowerPartial dataSet index
    evenMagnitude = magnitude dataSet (double index)
    oddMagnitude = magnitude dataSet (suc (double index))

    differenceNonnegative :
      BishopReal._≤_
        BishopReal.0ℝ
        (BishopReal._-_ evenMagnitude oddMagnitude)
    differenceNonnegative =
      Alternating.differenceNonnegative
        Alternating.bishopSetoidOrderedDifferenceKernel
        (magnitudeDecreasing dataSet (double index))

    baseBound :
      BishopReal._≤_
        partial
        (BishopReal._+_ partial
          (BishopReal._-_ evenMagnitude oddMagnitude))
    baseBound =
      BishopProperties.≤-respˡ-≃
        (BishopProperties.≃-symm
          (BishopProperties.+-identityʳ partial))
        (BishopProperties.+-monoˡ-≤ partial differenceNonnegative)
  in
  BishopProperties.≤-respʳ-≃
    (BishopProperties.≃-symm
      (lowerSuccessorExpansion dataSet index))
    baseBound

upperPartialDecreasing :
  (dataSet : AlternatingDecreasingSeriesData) →
  BishopSequence._isDecreasing (upperPartial dataSet)
upperPartialDecreasing dataSet index =
  let
    currentUpper = upperPartial dataSet index
    oddMagnitude = magnitude dataSet (suc (double index))
    nextEvenMagnitude = magnitude dataSet (suc (suc (double index)))

    rawBound :
      BishopReal._≤_
        (BishopReal._+_
          (BishopReal._-_ currentUpper oddMagnitude)
          nextEvenMagnitude)
        (BishopReal._+_
          (BishopReal._-_ currentUpper oddMagnitude)
          oddMagnitude)
    rawBound =
      BishopProperties.+-monoˡ-≤
        (BishopReal._-_ currentUpper oddMagnitude)
        (magnitudeDecreasing dataSet (suc (double index)))

    rightCancels :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._-_ currentUpper oddMagnitude)
          oddMagnitude)
        currentUpper
    rightCancels =
      let open BishopProperties.ℝ-Solver
      in solve 2
          (λ s b → (s ⊖ b) ⊕ b ⊜ s)
          BishopProperties.≃-refl
          currentUpper oddMagnitude
  in
  BishopProperties.≤-respʳ-≃ rightCancels
    (BishopProperties.≤-respˡ-≃
      (upperSuccessorExpansion dataSet index)
      rawBound)

lowerSubsequence :
  (dataSet : AlternatingDecreasingSeriesData) →
  BishopSequence._SubsequenceOf_
    (lowerPartial dataSet)
    (BishopSequence.SeriesOf (term dataSet))
lowerSubsequence dataSet =
  BishopSequence.subseq*
    (double ,
      (λ index → BishopProperties.≃-refl) ,
      doubleStrictlyIncreases)

upperSubsequence :
  (dataSet : AlternatingDecreasingSeriesData) →
  BishopSequence._SubsequenceOf_
    (upperPartial dataSet)
    (BishopSequence.SeriesOf (term dataSet))
upperSubsequence dataSet =
  BishopSequence.subseq*
    ((λ index → suc (double index)) ,
      (λ index → BishopProperties.≃-refl) ,
      oddIndexStrictlyIncreases)

fullSeriesConvergent :
  (dataSet : AlternatingDecreasingSeriesData) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf (term dataSet))
fullSeriesConvergent dataSet =
  representedLimit dataSet ,
  seriesConvergesToRepresentedLimit dataSet

lowerConvergesToRepresentedLimit :
  (dataSet : AlternatingDecreasingSeriesData) →
  BishopSequence._ConvergesTo_
    (lowerPartial dataSet)
    (representedLimit dataSet)
lowerConvergesToRepresentedLimit dataSet =
  BishopSequence.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
    (lowerSubsequence dataSet)
    (fullSeriesConvergent dataSet)

upperConvergesToRepresentedLimit :
  (dataSet : AlternatingDecreasingSeriesData) →
  BishopSequence._ConvergesTo_
    (upperPartial dataSet)
    (representedLimit dataSet)
upperConvergesToRepresentedLimit dataSet =
  BishopSequence.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
    (upperSubsequence dataSet)
    (fullSeriesConvergent dataSet)

lowerConvergent upperConvergent :
  (dataSet : AlternatingDecreasingSeriesData) →
  BishopSequence._isConvergent (lowerPartial dataSet)
lowerConvergent dataSet =
  representedLimit dataSet ,
  lowerConvergesToRepresentedLimit dataSet

upperConvergent dataSet =
  representedLimit dataSet ,
  upperConvergesToRepresentedLimit dataSet

upperMinusLowerIsEvenMagnitude :
  (dataSet : AlternatingDecreasingSeriesData) →
  ∀ index →
  BishopReal._≃_
    (BishopReal._-_
      (upperPartial dataSet index)
      (lowerPartial dataSet index))
    (magnitude dataSet (double index))
upperMinusLowerIsEvenMagnitude dataSet index =
  let partial = lowerPartial dataSet index
      magnitudeAt = magnitude dataSet (double index)
  in BishopProperties.≃-trans
      (BishopProperties.+-congʳ
        (BishopReal.- partial)
        (evenTermIsPositiveMagnitude dataSet index))
      (let open BishopProperties.ℝ-Solver
       in solve 2
          (λ s a → (s ⊕ a) ⊖ s ⊜ a)
          BishopProperties.≃-refl
          partial magnitudeAt)

upperMinusNextLowerIsOddMagnitude :
  (dataSet : AlternatingDecreasingSeriesData) →
  ∀ index →
  BishopReal._≃_
    (BishopReal._-_
      (upperPartial dataSet index)
      (nextLowerPartial dataSet index))
    (magnitude dataSet (suc (double index)))
upperMinusNextLowerIsOddMagnitude dataSet index =
  let currentUpper = upperPartial dataSet index
      oddMagnitude = magnitude dataSet (suc (double index))
  in BishopProperties.≃-trans
      (BishopProperties.+-congʳ
        currentUpper
        (BishopProperties.-‿cong
          (lowerSuccessorExpansion dataSet index)))
      (let open BishopProperties.ℝ-Solver
       in solve 3
          (λ u a b → u ⊖ (u ⊕ (a ⊖ b)) ⊜ b)
          BishopProperties.≃-refl
          currentUpper
          (magnitude dataSet (double index))
          oddMagnitude)

alternatingInterlacingData :
  (dataSet : AlternatingDecreasingSeriesData) →
  Interlacing.BishopAlternatingInterlacingData
alternatingInterlacingData dataSet = record
  { lowerPartial = lowerPartial dataSet
  ; upperPartial = upperPartial dataSet
  ; nextLowerPartial = nextLowerPartial dataSet
  ; representedLimit = representedLimit dataSet
  ; firstOmittedAfterLower = λ index →
      magnitude dataSet (double index)
  ; firstOmittedAfterUpper = λ index →
      magnitude dataSet (suc (double index))
  ; lowerIncreasing = lowerPartialIncreasing dataSet
  ; upperDecreasing = upperPartialDecreasing dataSet
  ; lowerConverges = lowerConvergent dataSet
  ; upperConverges = upperConvergent dataSet
  ; lowerLimitIsRepresentedLimit = BishopProperties.≃-refl
  ; upperLimitIsRepresentedLimit = BishopProperties.≃-refl
  ; nextLowerIsSuccessorLower = λ index → BishopProperties.≃-refl
  ; upperMinusLowerEquivalentFirstOmitted =
      upperMinusLowerIsEvenMagnitude dataSet
  ; upperMinusNextLowerEquivalentFirstOmitted =
      upperMinusNextLowerIsOddMagnitude dataSet
  }

alternatingDecreasingInterlacingLevel : ProofLevel
alternatingDecreasingInterlacingLevel = machineChecked

alternatingSubsequenceConvergenceLevel : ProofLevel
alternatingSubsequenceConvergenceLevel = machineChecked
