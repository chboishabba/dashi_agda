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
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
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
shellContribution data shell =
  Time.weightedTimeSum
    (times data)
    (timeWeight data)
    (λ time →
      Source.sourceSquareEnergy
        (normalizedAmplitude data time) shell)

lowerContribution :
  ∀ {T} → SourceJ11HalfRangeData T → Nat → ℚ
lowerContribution data shell
  with ℕ._+_ shell shell ≤? outputShell data
... | yes proof = shellContribution data shell
... | no refutation = 0ℚ

upperContribution :
  ∀ {T} → SourceJ11HalfRangeData T → Nat → ℚ
upperContribution data shell
  with ℕ._+_ shell shell ≤? outputShell data
... | yes proof = 0ℚ
... | no refutation = shellContribution data shell

contributionSplitPointwise :
  ∀ {T}
    (data : SourceJ11HalfRangeData T)
    (shell : Nat) →
  shellContribution data shell
  ≡ lowerContribution data shell + upperContribution data shell
contributionSplitPointwise data shell
  with ℕ._+_ shell shell ≤? outputShell data
... | yes proof = solve (shellContribution data shell ∷ [])
... | no refutation = solve (shellContribution data shell ∷ [])

sourceHalfSplitReconstructs :
  ∀ {T} (data : SourceJ11HalfRangeData T) →
  Sum.sumTo (shellContribution data) (outputShell data)
  ≡ Sum.sumTo (lowerContribution data) (outputShell data)
    + Sum.sumTo (upperContribution data) (outputShell data)
sourceHalfSplitReconstructs data =
  trans
    (sumToCong
      (shellContribution data)
      (λ shell → lowerContribution data shell + upperContribution data shell)
      (outputShell data)
      (contributionSplitPointwise data))
    (sumToAdd
      (lowerContribution data)
      (upperContribution data)
      (outputShell data))

lowerContributionBelowReference :
  ∀ {T}
    (data : SourceJ11HalfRangeData T)
    (shell : Nat) →
  lowerContribution data shell ≤ referenceEnergy data shell
lowerContributionBelowReference data shell
  with ℕ._+_ shell shell ≤? outputShell data
... | yes proof = lowerLocalPhysicalBound data shell proof
... | no refutation = referenceEnergyNonnegative data shell

criterionCoefficientNonnegative :
  ∀ {T} (data : SourceJ11HalfRangeData T) →
  0ℚ ≤ Prefix.two * delta data
criterionCoefficientNonnegative data =
  let
    instance
      twoIsNonnegative = nonNegative Prefix.twoNonnegative
      deltaIsNonnegative = nonNegative (deltaNonnegative data)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg Prefix.two (delta data)
  in
  ℚₚ.nonNegative⁻¹ (Prefix.two * delta data)

upperContributionBelowCriterion :
  ∀ {T}
    (data : SourceJ11HalfRangeData T)
    (shell : Nat) →
  upperContribution data shell
  ≤ Prefix.two * delta data * Source.lambda shell
upperContributionBelowCriterion data shell
  with ℕ._+_ shell shell ≤? outputShell data
... | yes proof =
  let
    instance
      coefficientIsNonnegative =
        nonNegative (criterionCoefficientNonnegative data)
      lambdaIsNonnegative =
        nonNegative (Prefix.powTwoNonnegative shell)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (Prefix.two * delta data) (Source.lambda shell)
  in
  ℚₚ.nonNegative⁻¹
    ((Prefix.two * delta data) * Source.lambda shell)
... | no refutation = upperLocalCriterionBound data shell refutation

lowerRangeBound :
  ∀ {T} (data : SourceJ11HalfRangeData T) →
  Sum.sumTo (lowerContribution data) (outputShell data)
  ≤ globalEnergy data
lowerRangeBound data =
  ℚₚ.≤-trans
    (Sum.sumToMonotone
      (lowerContribution data)
      (referenceEnergy data)
      (outputShell data)
      (lowerContributionBelowReference data))
    (totalReferenceEnergyBound data)

dyadicMassAgreement :
  (cutoff : Nat) →
  Sum.sumTo Source.lambda cutoff ≡ Source.dyadicPrefixMass cutoff
dyadicMassAgreement zero = refl
dyadicMassAgreement (suc cutoff)
  rewrite dyadicMassAgreement cutoff = refl

upperRangeBound :
  ∀ {T} (data : SourceJ11HalfRangeData T) →
  Sum.sumTo (upperContribution data) (outputShell data)
  ≤ (Int.+ 4 / 1) * delta data * Source.lambda (outputShell data)
upperRangeBound data =
  let
    coefficient = Prefix.two * delta data
    lambdaQ = Source.lambda (outputShell data)

    pointwise :
      Sum.sumTo (upperContribution data) (outputShell data)
      ≤ Sum.sumTo
          (λ shell → coefficient * Source.lambda shell)
          (outputShell data)
    pointwise =
      Sum.sumToMonotone
        (upperContribution data)
        (λ shell → coefficient * Source.lambda shell)
        (outputShell data)
        (upperContributionBelowCriterion data)

    factor :
      Sum.sumTo
        (λ shell → coefficient * Source.lambda shell)
        (outputShell data)
      ≡ coefficient * Source.dyadicPrefixMass (outputShell data)
    factor =
      trans
        (Sum.scaleSum coefficient Source.lambda (outputShell data))
        (cong (coefficient *_) (dyadicMassAgreement (outputShell data)))

    massScaled :
      coefficient * Source.dyadicPrefixMass (outputShell data)
      ≤ coefficient * (Prefix.two * lambdaQ)
    massScaled =
      let instance coefficientIsNonnegative =
        nonNegative (criterionCoefficientNonnegative data)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        coefficient
        (Source.dyadicPrefixMassBelowTwiceTop (outputShell data))

    targetMeaning :
      coefficient * (Prefix.two * lambdaQ)
      ≡ (Int.+ 4 / 1) * delta data * lambdaQ
    targetMeaning = solve (delta data ∷ lambdaQ ∷ [])

    factorToTarget :
      Sum.sumTo
        (λ shell → coefficient * Source.lambda shell)
        (outputShell data)
      ≤ (Int.+ 4 / 1) * delta data * lambdaQ
    factorToTarget =
      subst
        (λ lower →
          lower ≤ (Int.+ 4 / 1) * delta data * lambdaQ)
        (sym factor)
        (subst
          (λ upper →
            coefficient * Source.dyadicPrefixMass (outputShell data)
            ≤ upper)
          targetMeaning
          massScaled)
  in
  ℚₚ.≤-trans pointwise factorToTarget

sourceJ11Squared :
  ∀ {T} → SourceJ11HalfRangeData T → ℚ
sourceJ11Squared data =
  Time.weightedTimeSum
    (times data)
    (timeWeight data)
    (λ time →
      L2.square
        (Sum.sumTo
          (Source.sourceAmplitude
            (normalizedAmplitude data time))
          (outputShell data)))

sourceJ11ToTotalShellContribution :
  ∀ {T} (data : SourceJ11HalfRangeData T) →
  sourceJ11Squared data
  ≤ (Prefix.two * Source.lambda (outputShell data))
      * Sum.sumTo (shellContribution data) (outputShell data)
sourceJ11ToTotalShellContribution data =
  let
    scale = Prefix.two * Source.lambda (outputShell data)

    pointwise :
      sourceJ11Squared data
      ≤ Time.weightedTimeSum
          (times data)
          (timeWeight data)
          (λ time →
            scale
            * Sum.sumTo
                (Source.sourceSquareEnergy
                  (normalizedAmplitude data time))
                (outputShell data))
    pointwise =
      Time.weightedTimeSumMonotone
        (times data)
        (timeWeight data)
        (λ time →
          L2.square
            (Sum.sumTo
              (Source.sourceAmplitude
                (normalizedAmplitude data time))
              (outputShell data)))
        (λ time →
          scale
          * Sum.sumTo
              (Source.sourceSquareEnergy
                (normalizedAmplitude data time))
              (outputShell data))
        (timeWeightNonnegative data)
        (λ time →
          Source.sourceWeightedJ11SquareBound
            (normalizedAmplitude data time)
            (outputShell data))

    scaleOut :
      Time.weightedTimeSum
        (times data)
        (timeWeight data)
        (λ time →
          scale
          * Sum.sumTo
              (Source.sourceSquareEnergy
                (normalizedAmplitude data time))
              (outputShell data))
      ≡ scale
        * Time.weightedTimeSum
            (times data)
            (timeWeight data)
            (λ time →
              Sum.sumTo
                (Source.sourceSquareEnergy
                  (normalizedAmplitude data time))
                (outputShell data))
    scaleOut =
      weightedTimeSumScale
        (times data)
        (timeWeight data)
        (λ time →
          Sum.sumTo
            (Source.sourceSquareEnergy
              (normalizedAmplitude data time))
            (outputShell data))
        scale

    fubini :
      Time.weightedTimeSum
        (times data)
        (timeWeight data)
        (λ time →
          Sum.sumTo
            (Source.sourceSquareEnergy
              (normalizedAmplitude data time))
            (outputShell data))
      ≡ Sum.sumTo (shellContribution data) (outputShell data)
    fubini =
      weightedTimeShellFubini
        (times data)
        (timeWeight data)
        (λ time shell →
          Source.sourceSquareEnergy
            (normalizedAmplitude data time) shell)
        (outputShell data)
  in
  subst
    (λ upper → sourceJ11Squared data ≤ upper)
    (trans scaleOut (cong (scale *_) fubini))
    pointwise

sourceJ11HalfRangeBound :
  ∀ {T} (data : SourceJ11HalfRangeData T) →
  sourceJ11Squared data
  ≤ (Int.+ 10 / 1) * delta data
      * L2.square (Source.lambda (outputShell data))
sourceJ11HalfRangeBound data =
  let
    lambdaQ = Source.lambda (outputShell data)
    total = Sum.sumTo (shellContribution data) (outputShell data)
    low = Sum.sumTo (lowerContribution data) (outputShell data)
    upper = Sum.sumTo (upperContribution data) (outputShell data)

    rangeComponents :
      low + upper
      ≤ globalEnergy data
        + (Int.+ 4 / 1) * delta data * lambdaQ
    rangeComponents =
      ℚₚ.+-mono-≤ (lowerRangeBound data) (upperRangeBound data)

    ranges :
      total
      ≤ globalEnergy data
        + (Int.+ 4 / 1) * delta data * lambdaQ
    ranges =
      subst
        (λ left →
          left
          ≤ globalEnergy data
            + (Int.+ 4 / 1) * delta data * lambdaQ)
        (sym (sourceHalfSplitReconstructs data))
        rangeComponents

    absorbedRanges :
      globalEnergy data
        + (Int.+ 4 / 1) * delta data * lambdaQ
      ≤ (Int.+ 5 / 1) * delta data * lambdaQ
    absorbedRanges =
      subst
        (λ upperBound →
          globalEnergy data
            + (Int.+ 4 / 1) * delta data * lambdaQ
          ≤ upperBound)
        (solve (delta data ∷ lambdaQ ∷ []))
        (ℚₚ.+-mono-≤
          (highShellEnergyAbsorption data)
          ℚₚ.≤-refl)

    totalBound :
      total ≤ (Int.+ 5 / 1) * delta data * lambdaQ
    totalBound = ℚₚ.≤-trans ranges absorbedRanges

    scale = Prefix.two * lambdaQ
    scaleNonnegative : 0ℚ ≤ scale
    scaleNonnegative =
      let
        instance
          twoIsNonnegative = nonNegative Prefix.twoNonnegative
          lambdaIsNonnegative =
            nonNegative (Prefix.powTwoNonnegative (outputShell data))
          productIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg Prefix.two lambdaQ
      in
      ℚₚ.nonNegative⁻¹ scale

    scaled :
      scale * total
      ≤ scale * ((Int.+ 5 / 1) * delta data * lambdaQ)
    scaled =
      let instance scaleIsNonnegative = nonNegative scaleNonnegative
      in ℚₚ.*-monoˡ-≤-nonNeg scale totalBound

    targetMeaning :
      scale * ((Int.+ 5 / 1) * delta data * lambdaQ)
      ≡ (Int.+ 10 / 1) * delta data * L2.square lambdaQ
    targetMeaning = solve (delta data ∷ lambdaQ ∷ [])
  in
  ℚₚ.≤-trans
    (sourceJ11ToTotalShellContribution data)
    (subst
      (λ upperBound → scale * total ≤ upperBound)
      targetMeaning
      scaled)
