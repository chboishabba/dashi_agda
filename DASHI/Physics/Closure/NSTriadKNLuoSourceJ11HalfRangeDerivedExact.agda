module DASHI.Physics.Closure.NSTriadKNLuoSourceJ11HalfRangeDerivedExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Implement the actual lower/upper r=q/2 split in (4.7)--(4.9).  Weighted
-- shell Jensen is applied at every time sample, finite time/shell Fubini is
-- proved, and the decidable classifier 2r<=q separates the resulting
-- lambda_r^4 energy sum.  Primitive assumptions occur only at the local PDE
-- leaves: a lower-range shell contribution is controlled by its energy shell,
-- and an upper-range shell contribution by 2 delta lambda_r.
--
-- From these local estimates, total energy, dyadic prefix summation, and the
-- high-shell relation E<=delta lambda_q, the module derives
--
--   J11^2 <= 10 delta lambda_q^2.
--
-- Neither range aggregate nor the final J11 bound is stored as a field.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
import Data.Integer.Base as Int
import Data.Nat.Base as ℕ
open import Data.Nat.Properties using (_≤?_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import Relation.Nullary using (yes; no)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Sum
import DASHI.Physics.Closure.NSTriadKNLuoFinitePrefixJensenExact as Prefix
import DASHI.Physics.Closure.NSTriadKNLuoSourceWeightedJ11Exact as Source
import DASHI.Physics.Closure.NSTriadKNLuoSourceJ12FiveShellExact as Time

weightedTimeSumScale :
  ∀ {T : Set}
    (times : List T)
    (weight value : T → ℚ)
    (scale : ℚ) →
  Time.weightedTimeSum times weight (λ time → scale * value time)
  ≡ scale * Time.weightedTimeSum times weight value
weightedTimeSumScale [] weight value scale = solve (scale ∷ [])
weightedTimeSumScale (time ∷ times) weight value scale
  rewrite weightedTimeSumScale times weight value scale =
  solve
    ( scale
    ∷ weight time
    ∷ value time
    ∷ Time.weightedTimeSum times weight value
    ∷ []
    )

weightedTimeSumAdd :
  ∀ {T : Set}
    (times : List T)
    (weight left right : T → ℚ) →
  Time.weightedTimeSum times weight (λ time → left time + right time)
  ≡ Time.weightedTimeSum times weight left
    + Time.weightedTimeSum times weight right
weightedTimeSumAdd [] weight left right = solve []
weightedTimeSumAdd (time ∷ times) weight left right
  rewrite weightedTimeSumAdd times weight left right =
  solve
    ( weight time
    ∷ left time
    ∷ right time
    ∷ Time.weightedTimeSum times weight left
    ∷ Time.weightedTimeSum times weight right
    ∷ []
    )

weightedTimeShellFubini :
  ∀ {T : Set}
    (times : List T)
    (weight : T → ℚ)
    (value : T → Nat → ℚ)
    (cutoff : Nat) →
  Time.weightedTimeSum times weight
    (λ time → Sum.sumTo (value time) cutoff)
  ≡ Sum.sumTo
      (λ shell →
        Time.weightedTimeSum times weight (λ time → value time shell))
      cutoff
weightedTimeShellFubini times weight value zero = refl
weightedTimeShellFubini times weight value (suc cutoff)
  rewrite weightedTimeSumAdd
            times weight
            (λ time → value time (suc cutoff))
            (λ time → Sum.sumTo (value time) cutoff)
        | weightedTimeShellFubini times weight value cutoff = refl

sumToCong :
  (left right : Nat → ℚ) →
  (cutoff : Nat) →
  ((shell : Nat) → left shell ≡ right shell) →
  Sum.sumTo left cutoff ≡ Sum.sumTo right cutoff
sumToCong left right zero pointwise = pointwise zero
sumToCong left right (suc cutoff) pointwise
  rewrite pointwise (suc cutoff)
        | sumToCong left right cutoff pointwise = refl

sumToAdd :
  (left right : Nat → ℚ) →
  (cutoff : Nat) →
  Sum.sumTo (λ shell → left shell + right shell) cutoff
  ≡ Sum.sumTo left cutoff + Sum.sumTo right cutoff
sumToAdd left right zero = solve (left zero ∷ right zero ∷ [])
sumToAdd left right (suc cutoff)
  rewrite sumToAdd left right cutoff =
  solve
    ( left (suc cutoff)
    ∷ right (suc cutoff)
    ∷ Sum.sumTo left cutoff
    ∷ Sum.sumTo right cutoff
    ∷ []
    )

record SourceJ11HalfRangeData (T : Set) : Set₁ where
  field
    outputShell : Nat
    times : List T
    timeWeight : T → ℚ
    normalizedAmplitude : T → Nat → ℚ

    timeWeightNonnegative :
      (time : T) → 0ℚ ≤ timeWeight time

    referenceEnergy : Nat → ℚ
    globalEnergy delta : ℚ

    referenceEnergyNonnegative :
      (shell : Nat) → 0ℚ ≤ referenceEnergy shell
    deltaNonnegative : 0ℚ ≤ delta

    lowerLocalPhysicalBound :
      (shell : Nat) →
      ℕ._≤_ (ℕ._+_ shell shell) outputShell →
      Time.weightedTimeSum times timeWeight
        (λ time →
          Source.sourceSquareEnergy
            (normalizedAmplitude time) shell)
      ≤ referenceEnergy shell

    upperLocalCriterionBound :
      (shell : Nat) →
      (ℕ._≤_ (ℕ._+_ shell shell) outputShell → ⊥) →
      Time.weightedTimeSum times timeWeight
        (λ time →
          Source.sourceSquareEnergy
            (normalizedAmplitude time) shell)
      ≤ Prefix.two * delta * Source.lambda shell

    totalReferenceEnergyBound :
      Sum.sumTo referenceEnergy outputShell ≤ globalEnergy

    highShellEnergyAbsorption :
      globalEnergy ≤ delta * Source.lambda outputShell

open SourceJ11HalfRangeData public

shellContribution :
  ∀ {T} → SourceJ11HalfRangeData T → Nat → ℚ
shellContribution rangeData shell =
  Time.weightedTimeSum
    (times rangeData)
    (timeWeight rangeData)
    (λ time →
      Source.sourceSquareEnergy
        (normalizedAmplitude rangeData time) shell)

lowerContribution :
  ∀ {T} → SourceJ11HalfRangeData T → Nat → ℚ
lowerContribution rangeData shell
  with ℕ._+_ shell shell ≤? outputShell rangeData
... | yes proof = shellContribution rangeData shell
... | no refutation = 0ℚ

upperContribution :
  ∀ {T} → SourceJ11HalfRangeData T → Nat → ℚ
upperContribution rangeData shell
  with ℕ._+_ shell shell ≤? outputShell rangeData
... | yes proof = 0ℚ
... | no refutation = shellContribution rangeData shell

contributionSplitPointwise :
  ∀ {T}
    (rangeData : SourceJ11HalfRangeData T)
    (shell : Nat) →
  shellContribution rangeData shell
  ≡ lowerContribution rangeData shell + upperContribution rangeData shell
contributionSplitPointwise rangeData shell
  with ℕ._+_ shell shell ≤? outputShell rangeData
... | yes proof = solve (shellContribution rangeData shell ∷ [])
... | no refutation = solve (shellContribution rangeData shell ∷ [])

sourceHalfSplitReconstructs :
  ∀ {T} (rangeData : SourceJ11HalfRangeData T) →
  Sum.sumTo (shellContribution rangeData) (outputShell rangeData)
  ≡ Sum.sumTo (lowerContribution rangeData) (outputShell rangeData)
    + Sum.sumTo (upperContribution rangeData) (outputShell rangeData)
sourceHalfSplitReconstructs rangeData =
  trans
    (sumToCong
      (shellContribution rangeData)
      (λ shell →
        lowerContribution rangeData shell + upperContribution rangeData shell)
      (outputShell rangeData)
      (contributionSplitPointwise rangeData))
    (sumToAdd
      (lowerContribution rangeData)
      (upperContribution rangeData)
      (outputShell rangeData))

lowerContributionBelowReference :
  ∀ {T}
    (rangeData : SourceJ11HalfRangeData T)
    (shell : Nat) →
  lowerContribution rangeData shell ≤ referenceEnergy rangeData shell
lowerContributionBelowReference rangeData shell
  with ℕ._+_ shell shell ≤? outputShell rangeData
... | yes proof = lowerLocalPhysicalBound rangeData shell proof
... | no refutation = referenceEnergyNonnegative rangeData shell

criterionCoefficientNonnegative :
  ∀ {T} (rangeData : SourceJ11HalfRangeData T) →
  0ℚ ≤ Prefix.two * delta rangeData
criterionCoefficientNonnegative rangeData =
  let
    instance
      twoIsNonnegative = nonNegative Prefix.twoNonnegative
      deltaIsNonnegative = nonNegative (deltaNonnegative rangeData)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg Prefix.two (delta rangeData)
  in
  ℚₚ.nonNegative⁻¹ (Prefix.two * delta rangeData)

upperContributionBelowCriterion :
  ∀ {T}
    (rangeData : SourceJ11HalfRangeData T)
    (shell : Nat) →
  upperContribution rangeData shell
  ≤ Prefix.two * delta rangeData * Source.lambda shell
upperContributionBelowCriterion rangeData shell
  with ℕ._+_ shell shell ≤? outputShell rangeData
... | yes proof =
  let
    instance
      coefficientIsNonnegative =
        nonNegative (criterionCoefficientNonnegative rangeData)
      lambdaIsNonnegative =
        nonNegative (Prefix.powTwoNonnegative shell)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (Prefix.two * delta rangeData) (Source.lambda shell)
  in
  ℚₚ.nonNegative⁻¹
    ((Prefix.two * delta rangeData) * Source.lambda shell)
... | no refutation =
  upperLocalCriterionBound rangeData shell refutation

lowerRangeBound :
  ∀ {T} (rangeData : SourceJ11HalfRangeData T) →
  Sum.sumTo (lowerContribution rangeData) (outputShell rangeData)
  ≤ globalEnergy rangeData
lowerRangeBound rangeData =
  ℚₚ.≤-trans
    (Sum.sumToMonotone
      (lowerContribution rangeData)
      (referenceEnergy rangeData)
      (outputShell rangeData)
      (lowerContributionBelowReference rangeData))
    (totalReferenceEnergyBound rangeData)

dyadicMassAgreement :
  (cutoff : Nat) →
  Sum.sumTo Source.lambda cutoff ≡ Source.dyadicPrefixMass cutoff
dyadicMassAgreement zero = refl
dyadicMassAgreement (suc cutoff)
  rewrite dyadicMassAgreement cutoff = refl

upperRangeBound :
  ∀ {T} (rangeData : SourceJ11HalfRangeData T) →
  Sum.sumTo (upperContribution rangeData) (outputShell rangeData)
  ≤ (Int.+ 4 / 1)
      * delta rangeData * Source.lambda (outputShell rangeData)
upperRangeBound rangeData =
  let
    coefficient = Prefix.two * delta rangeData
    lambdaQ = Source.lambda (outputShell rangeData)

    pointwise :
      Sum.sumTo (upperContribution rangeData) (outputShell rangeData)
      ≤ Sum.sumTo
          (λ shell → coefficient * Source.lambda shell)
          (outputShell rangeData)
    pointwise =
      Sum.sumToMonotone
        (upperContribution rangeData)
        (λ shell → coefficient * Source.lambda shell)
        (outputShell rangeData)
        (upperContributionBelowCriterion rangeData)

    factor :
      Sum.sumTo
        (λ shell → coefficient * Source.lambda shell)
        (outputShell rangeData)
      ≡ coefficient * Source.dyadicPrefixMass (outputShell rangeData)
    factor =
      trans
        (Sum.scaleSum coefficient Source.lambda (outputShell rangeData))
        (cong
          (coefficient *_)
          (dyadicMassAgreement (outputShell rangeData)))

    massScaled :
      coefficient * Source.dyadicPrefixMass (outputShell rangeData)
      ≤ coefficient * (Prefix.two * lambdaQ)
    massScaled =
      let
        instance
          coefficientIsNonnegative =
            nonNegative (criterionCoefficientNonnegative rangeData)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        coefficient
        (Source.dyadicPrefixMassBelowTwiceTop (outputShell rangeData))

    targetMeaning :
      coefficient * (Prefix.two * lambdaQ)
      ≡ (Int.+ 4 / 1) * delta rangeData * lambdaQ
    targetMeaning = solve (delta rangeData ∷ lambdaQ ∷ [])

    factorToTarget :
      Sum.sumTo
        (λ shell → coefficient * Source.lambda shell)
        (outputShell rangeData)
      ≤ (Int.+ 4 / 1) * delta rangeData * lambdaQ
    factorToTarget =
      subst
        (λ lower →
          lower ≤ (Int.+ 4 / 1) * delta rangeData * lambdaQ)
        (sym factor)
        (subst
          (λ upper →
            coefficient * Source.dyadicPrefixMass (outputShell rangeData)
            ≤ upper)
          targetMeaning
          massScaled)
  in
  ℚₚ.≤-trans pointwise factorToTarget

sourceJ11Squared :
  ∀ {T} → SourceJ11HalfRangeData T → ℚ
sourceJ11Squared rangeData =
  Time.weightedTimeSum
    (times rangeData)
    (timeWeight rangeData)
    (λ time →
      L2.square
        (Sum.sumTo
          (Source.sourceAmplitude
            (normalizedAmplitude rangeData time))
          (outputShell rangeData)))

sourceJ11ToTotalShellContribution :
  ∀ {T} (rangeData : SourceJ11HalfRangeData T) →
  sourceJ11Squared rangeData
  ≤ (Prefix.two * Source.lambda (outputShell rangeData))
      * Sum.sumTo (shellContribution rangeData) (outputShell rangeData)
sourceJ11ToTotalShellContribution rangeData =
  let
    scale = Prefix.two * Source.lambda (outputShell rangeData)

    pointwise :
      sourceJ11Squared rangeData
      ≤ Time.weightedTimeSum
          (times rangeData)
          (timeWeight rangeData)
          (λ time →
            scale
            * Sum.sumTo
                (Source.sourceSquareEnergy
                  (normalizedAmplitude rangeData time))
                (outputShell rangeData))
    pointwise =
      Time.weightedTimeSumMonotone
        (times rangeData)
        (timeWeight rangeData)
        (λ time →
          L2.square
            (Sum.sumTo
              (Source.sourceAmplitude
                (normalizedAmplitude rangeData time))
              (outputShell rangeData)))
        (λ time →
          scale
          * Sum.sumTo
              (Source.sourceSquareEnergy
                (normalizedAmplitude rangeData time))
              (outputShell rangeData))
        (timeWeightNonnegative rangeData)
        (λ time →
          Source.sourceWeightedJ11SquareBound
            (normalizedAmplitude rangeData time)
            (outputShell rangeData))

    scaleOut :
      Time.weightedTimeSum
        (times rangeData)
        (timeWeight rangeData)
        (λ time →
          scale
          * Sum.sumTo
              (Source.sourceSquareEnergy
                (normalizedAmplitude rangeData time))
              (outputShell rangeData))
      ≡ scale
        * Time.weightedTimeSum
            (times rangeData)
            (timeWeight rangeData)
            (λ time →
              Sum.sumTo
                (Source.sourceSquareEnergy
                  (normalizedAmplitude rangeData time))
                (outputShell rangeData))
    scaleOut =
      weightedTimeSumScale
        (times rangeData)
        (timeWeight rangeData)
        (λ time →
          Sum.sumTo
            (Source.sourceSquareEnergy
              (normalizedAmplitude rangeData time))
            (outputShell rangeData))
        scale

    fubini :
      Time.weightedTimeSum
        (times rangeData)
        (timeWeight rangeData)
        (λ time →
          Sum.sumTo
            (Source.sourceSquareEnergy
              (normalizedAmplitude rangeData time))
            (outputShell rangeData))
      ≡ Sum.sumTo (shellContribution rangeData) (outputShell rangeData)
    fubini =
      weightedTimeShellFubini
        (times rangeData)
        (timeWeight rangeData)
        (λ time shell →
          Source.sourceSquareEnergy
            (normalizedAmplitude rangeData time) shell)
        (outputShell rangeData)
  in
  subst
    (λ upper → sourceJ11Squared rangeData ≤ upper)
    (trans scaleOut (cong (scale *_) fubini))
    pointwise

sourceJ11HalfRangeBound :
  ∀ {T} (rangeData : SourceJ11HalfRangeData T) →
  sourceJ11Squared rangeData
  ≤ (Int.+ 10 / 1) * delta rangeData
      * L2.square (Source.lambda (outputShell rangeData))
sourceJ11HalfRangeBound rangeData =
  let
    lambdaQ = Source.lambda (outputShell rangeData)
    total = Sum.sumTo (shellContribution rangeData) (outputShell rangeData)
    low = Sum.sumTo (lowerContribution rangeData) (outputShell rangeData)
    upper = Sum.sumTo (upperContribution rangeData) (outputShell rangeData)

    rangeComponents :
      low + upper
      ≤ globalEnergy rangeData
        + (Int.+ 4 / 1) * delta rangeData * lambdaQ
    rangeComponents =
      ℚₚ.+-mono-≤
        (lowerRangeBound rangeData)
        (upperRangeBound rangeData)

    ranges :
      total
      ≤ globalEnergy rangeData
        + (Int.+ 4 / 1) * delta rangeData * lambdaQ
    ranges =
      subst
        (λ left →
          left
          ≤ globalEnergy rangeData
            + (Int.+ 4 / 1) * delta rangeData * lambdaQ)
        (sym (sourceHalfSplitReconstructs rangeData))
        rangeComponents

    absorbedRanges :
      globalEnergy rangeData
        + (Int.+ 4 / 1) * delta rangeData * lambdaQ
      ≤ (Int.+ 5 / 1) * delta rangeData * lambdaQ
    absorbedRanges =
      subst
        (λ upperBound →
          globalEnergy rangeData
            + (Int.+ 4 / 1) * delta rangeData * lambdaQ
          ≤ upperBound)
        (solve (delta rangeData ∷ lambdaQ ∷ []))
        (ℚₚ.+-mono-≤
          (highShellEnergyAbsorption rangeData)
          ℚₚ.≤-refl)

    totalBound :
      total ≤ (Int.+ 5 / 1) * delta rangeData * lambdaQ
    totalBound = ℚₚ.≤-trans ranges absorbedRanges

    scale = Prefix.two * lambdaQ
    scaleNonnegative : 0ℚ ≤ scale
    scaleNonnegative =
      let
        instance
          twoIsNonnegative = nonNegative Prefix.twoNonnegative
          lambdaIsNonnegative =
            nonNegative (Prefix.powTwoNonnegative (outputShell rangeData))
          productIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg Prefix.two lambdaQ
      in
      ℚₚ.nonNegative⁻¹ scale

    scaled :
      scale * total
      ≤ scale * ((Int.+ 5 / 1) * delta rangeData * lambdaQ)
    scaled =
      let
        instance
          scaleIsNonnegative = nonNegative scaleNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg scale totalBound

    targetMeaning :
      scale * ((Int.+ 5 / 1) * delta rangeData * lambdaQ)
      ≡ (Int.+ 10 / 1) * delta rangeData * L2.square lambdaQ
    targetMeaning = solve (delta rangeData ∷ lambdaQ ∷ [])
  in
  ℚₚ.≤-trans
    (sourceJ11ToTotalShellContribution rangeData)
    (subst
      (λ upperBound → scale * total ≤ upperBound)
      targetMeaning
      scaled)
