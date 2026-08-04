module DASHI.Physics.Closure.NSTriadKNLuoSourceJ11HalfRangeExact where

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
-- Implement the actual lower/upper r=q/2 split in (4.7)--(4.9), starting
-- from a finite nonnegative time window and the source amplitude
-- lambda_r^(5/2)||u_r||_2.  Weighted shell Jensen is applied pointwise in
-- time, finite time/shell Fubini is proved, and the exact classifier 2r<=q
-- separates the resulting lambda_r^4 energy sum.
--
-- Local physical estimates are supplied only at their natural leaves:
-- lower-half contributions are bounded by the corresponding energy shell,
-- while upper-half contributions are bounded by 2 delta lambda_r.  The code
-- derives the complete high-shell estimate
--
--   J11^2 <= 10 delta lambda_q^2
--
-- from the total energy bound, dyadic prefix summation, and
-- E <= delta lambda_q.  No lower/upper aggregate or final J11 bound is a
-- field of the input package.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
import Data.Nat.Base as Nat
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

weightedTimeSum :
  ∀ {Time : Set} →
  List Time → (Time → ℚ) → (Time → ℚ) → ℚ
weightedTimeSum [] weight value = 0ℚ
weightedTimeSum (time ∷ times) weight value =
  weight time * value time + weightedTimeSum times weight value

weightedTimeSumMonotone :
  ∀ {Time : Set}
    (times : List Time)
    (weight lower upper : Time → ℚ) →
  ((time : Time) → 0ℚ ≤ weight time) →
  ((time : Time) → lower time ≤ upper time) →
  weightedTimeSum times weight lower
  ≤ weightedTimeSum times weight upper
weightedTimeSumMonotone [] weight lower upper weightNonnegative pointwise =
  ℚₚ.≤-refl
weightedTimeSumMonotone
  (time ∷ times) weight lower upper weightNonnegative pointwise =
  ℚₚ.+-mono-≤
    (let instance timeWeightIsNonnegative =
       nonNegative (weightNonnegative time)
     in
     ℚₚ.*-monoˡ-≤-nonNeg (weight time) (pointwise time))
    (weightedTimeSumMonotone
      times weight lower upper weightNonnegative pointwise)

weightedTimeSumAdd :
  ∀ {Time : Set}
    (times : List Time)
    (weight left right : Time → ℚ) →
  weightedTimeSum times weight (λ time → left time + right time)
  ≡ weightedTimeSum times weight left
    + weightedTimeSum times weight right
weightedTimeSumAdd [] weight left right = solve []
weightedTimeSumAdd (time ∷ times) weight left right
  rewrite weightedTimeSumAdd times weight left right =
  solve
    ( weight time
    ∷ left time
    ∷ right time
    ∷ weightedTimeSum times weight left
    ∷ weightedTimeSum times weight right
    ∷ []
    )

weightedTimeSumScale :
  ∀ {Time : Set}
    (times : List Time)
    (weight value : Time → ℚ)
    (scale : ℚ) →
  weightedTimeSum times weight (λ time → scale * value time)
  ≡ scale * weightedTimeSum times weight value
weightedTimeSumScale [] weight value scale = solve (scale ∷ [])
weightedTimeSumScale (time ∷ times) weight value scale
  rewrite weightedTimeSumScale times weight value scale =
  solve
    ( scale
    ∷ weight time
    ∷ value time
    ∷ weightedTimeSum times weight value
    ∷ []
    )

weightedTimeShellFubini :
  ∀ {Time : Set}
    (times : List Time)
    (weight : Time → ℚ)
    (value : Time → Nat → ℚ)
    (cutoff : Nat) →
  weightedTimeSum times weight
    (λ time → Sum.sumTo (value time) cutoff)
  ≡ Sum.sumTo
      (λ shell →
        weightedTimeSum times weight (λ time → value time shell))
      cutoff
weightedTimeShellFubini times weight value zero = refl
weightedTimeShellFubini times weight value (suc cutoff)
  rewrite weightedTimeSumAdd
            times weight
            (λ time → value time (suc cutoff))
            (λ time → Sum.sumTo (value time) cutoff)
        | weightedTimeShellFubini times weight value cutoff = refl

record SourceJ11HalfRangeData (Time : Set) : Set₁ where
  field
    outputShell : Nat
    times : List Time
    timeWeight : Time → ℚ
    normalizedAmplitude : Time → Nat → ℚ

    timeWeightNonnegative :
      (time : Time) → 0ℚ ≤ timeWeight time

    referenceEnergy : Nat → ℚ
    globalEnergy delta : ℚ

    referenceEnergyNonnegative :
      (shell : Nat) → 0ℚ ≤ referenceEnergy shell
    deltaNonnegative : 0ℚ ≤ delta

    lowerLocalPhysicalBound :
      (shell : Nat) →
      Nat._+_ shell shell Nat.≤ outputShell →
      weightedTimeSum times timeWeight
        (λ time →
          Source.sourceSquareEnergy
            (normalizedAmplitude time) shell)
      ≤ referenceEnergy shell

    upperLocalCriterionBound :
      (shell : Nat) →
      (Nat._+_ shell shell Nat.≤ outputShell → Nat.⊥) →
      weightedTimeSum times timeWeight
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
  ∀ {Time} → SourceJ11HalfRangeData Time → Nat → ℚ
shellContribution data shell =
  weightedTimeSum
    (times data)
    (timeWeight data)
    (λ time →
      Source.sourceSquareEnergy
        (normalizedAmplitude data time) shell)

shellContributionNonnegative :
  ∀ {Time}
    (data : SourceJ11HalfRangeData Time)
    (shell : Nat) →
  0ℚ ≤ shellContribution data shell
shellContributionNonnegative data shell =
  go (times data)
  where
  go :
    (remaining : List Time) →
    0ℚ ≤ weightedTimeSum remaining (timeWeight data)
      (λ time →
        Source.sourceSquareEnergy
          (normalizedAmplitude data time) shell)
  go [] = ℚₚ.≤-refl
  go (time ∷ remaining) =
    L2.addNonnegative
      (let
        instance
          weightIsNonnegative =
            nonNegative (timeWeightNonnegative data time)
          energyIsNonnegative =
            nonNegative
              (Source.sourceSquareEnergyNonnegative
                (normalizedAmplitude data time) shell)
          productIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (timeWeight data time)
              (Source.sourceSquareEnergy
                (normalizedAmplitude data time) shell)
       in
       ℚₚ.nonNegative⁻¹
         ( timeWeight data time
         * Source.sourceSquareEnergy
             (normalizedAmplitude data time) shell))
      (go remaining)

lowerContribution :
  ∀ {Time} → SourceJ11HalfRangeData Time → Nat → ℚ
lowerContribution data shell
  with Nat._+_ shell shell ≤? outputShell data
... | yes proof = shellContribution data shell
... | no refutation = 0ℚ

upperContribution :
  ∀ {Time} → SourceJ11HalfRangeData Time → Nat → ℚ
upperContribution data shell
  with Nat._+_ shell shell ≤? outputShell data
... | yes proof = 0ℚ
... | no refutation = shellContribution data shell

contributionSplitPointwise :
  ∀ {Time}
    (data : SourceJ11HalfRangeData Time)
    (shell : Nat) →
  shellContribution data shell
  ≡ lowerContribution data shell + upperContribution data shell
contributionSplitPointwise data shell
  with Nat._+_ shell shell ≤? outputShell data
... | yes proof = solve (shellContribution data shell ∷ [])
... | no refutation = solve (shellContribution data shell ∷ [])

sumToCong :
  (left right : Nat → ℚ) →
  (cutoff : Nat) →
  ((shell : Nat) → left shell ≡ right shell) →
  Sum.sumTo left cutoff ≡ Sum.sumTo right cutoff
sumToCong left right zero pointwise = pointwise zero
sumToCong left right (suc cutoff) pointwise
  rewrite pointwise (suc cutoff)
        | sumToCong left right cutoff pointwise = refl

sourceHalfSplitReconstructs :
  ∀ {Time} (data : SourceJ11HalfRangeData Time) →
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
  where
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

lowerContributionBelowReference :
  ∀ {Time}
    (data : SourceJ11HalfRangeData Time)
    (shell : Nat) →
  lowerContribution data shell ≤ referenceEnergy data shell
lowerContributionBelowReference data shell
  with Nat._+_ shell shell ≤? outputShell data
... | yes proof = lowerLocalPhysicalBound data shell proof
... | no refutation = referenceEnergyNonnegative data shell

upperContributionBelowCriterion :
  ∀ {Time}
    (data : SourceJ11HalfRangeData Time)
    (shell : Nat) →
  upperContribution data shell
  ≤ Prefix.two * delta data * Source.lambda shell
upperContributionBelowCriterion data shell
  with Nat._+_ shell shell ≤? outputShell data
... | yes proof =
  let
    coefficientNonnegative :
      0ℚ ≤ Prefix.two * delta data
    coefficientNonnegative =
      let
        instance
          twoIsNonnegative = nonNegative Prefix.twoNonnegative
          deltaIsNonnegative = nonNegative (deltaNonnegative data)
          productIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg Prefix.two (delta data)
      in
      ℚₚ.nonNegative⁻¹ (Prefix.two * delta data)
  in
  let
    instance
      coefficientIsNonnegative = nonNegative coefficientNonnegative
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
  ∀ {Time} (data : SourceJ11HalfRangeData Time) →
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
  ∀ {Time} (data : SourceJ11HalfRangeData Time) →
  Sum.sumTo (upperContribution data) (outputShell data)
  ≤ (Int.+ 4 / 1) * delta data * Source.lambda (outputShell data)
upperRangeBound data =
  let
    coefficient = Prefix.two * delta data

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

    coefficientNonnegative : 0ℚ ≤ coefficient
    coefficientNonnegative =
      let
        instance
          twoIsNonnegative = nonNegative Prefix.twoNonnegative
          deltaIsNonnegative = nonNegative (deltaNonnegative data)
          productIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg Prefix.two (delta data)
      in
      ℚₚ.nonNegative⁻¹ coefficient

    massScaled :
      coefficient * Source.dyadicPrefixMass (outputShell data)
      ≤ coefficient * (Prefix.two * Source.lambda (outputShell data))
    massScaled =
      let instance coefficientIsNonnegative =
        nonNegative coefficientNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        coefficient
        (Source.dyadicPrefixMassBelowTwiceTop (outputShell data))

    targetMeaning :
      coefficient * (Prefix.two * Source.lambda (outputShell data))
      ≡ (Int.+ 4 / 1) * delta data
          * Source.lambda (outputShell data)
    targetMeaning =
      solve (delta data ∷ Source.lambda (outputShell data) ∷ [])
  in
  ℚₚ.≤-trans pointwise
    (subst
      (λ lower →
        lower
        ≤ (Int.+ 4 / 1) * delta data
            * Source.lambda (outputShell data))
      (sym factor)
      (subst
        (λ upper →
          coefficient * Source.dyadicPrefixMass (outputShell data)
          ≤ upper)
        targetMeaning
        massScaled))

sourceJ11Squared :
  ∀ {Time} → SourceJ11HalfRangeData Time → ℚ
sourceJ11Squared data =
  weightedTimeSum
    (times data)
    (timeWeight data)
    (λ time →
      L2.square
        (Sum.sumTo
          (Source.sourceAmplitude
            (normalizedAmplitude data time))
          (outputShell data)))

sourceJ11ToTotalShellContribution :
  ∀ {Time} (data : SourceJ11HalfRangeData Time) →
  sourceJ11Squared data
  ≤ (Prefix.two * Source.lambda (outputShell data))
      * Sum.sumTo (shellContribution data) (outputShell data)
sourceJ11ToTotalShellContribution data =
  let
    scale = Prefix.two * Source.lambda (outputShell data)

    pointwise :
      sourceJ11Squared data
      ≤ weightedTimeSum
          (times data)
          (timeWeight data)
          (λ time →
            scale
            * Sum.sumTo
                (Source.sourceSquareEnergy
                  (normalizedAmplitude data time))
                (outputShell data))
    pointwise =
      weightedTimeSumMonotone
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
      weightedTimeSum
        (times data)
        (timeWeight data)
        (λ time →
          scale
          * Sum.sumTo
              (Source.sourceSquareEnergy
                (normalizedAmplitude data time))
              (outputShell data))
      ≡ scale
        * weightedTimeSum
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
      weightedTimeSum
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
  ∀ {Time} (data : SourceJ11HalfRangeData Time) →
  sourceJ11Squared data
  ≤ (Int.+ 10 / 1) * delta data
      * L2.square (Source.lambda (outputShell data))
sourceJ11HalfRangeBound data =
  let
    low = Sum.sumTo (lowerContribution data) (outputShell data)
    upper = Sum.sumTo (upperContribution data) (outputShell data)
    lambdaQ = Source.lambda (outputShell data)

    ranges :
      Sum.sumTo (shellContribution data) (outputShell data)
      ≤ globalEnergy data
        + (Int.+ 4 / 1) * delta data * lambdaQ
    ranges =
      subst
        (λ left →
          left
          ≤ globalEnergy data
            + (Int.+ 4 / 1) * delta data * lambdaQ)
        (sym (sourceHalfSplitReconstructs data))
        (ℚₚ.+-mono-≤
          (lowerRangeBound data)
          (upperRangeBound data))

    absorbedRanges :
      globalEnergy data
        + (Int.+ 4 / 1) * delta data * lambdaQ
      ≤ (Int.+ 5 / 1) * delta data * lambdaQ
    absorbedRanges =
      subst
        (λ upper →
          globalEnergy data
            + (Int.+ 4 / 1) * delta data * lambdaQ
          ≤ upper)
        (solve (delta data ∷ lambdaQ ∷ []))
        (ℚₚ.+-mono-≤
          (highShellEnergyAbsorption data)
          ℚₚ.≤-refl)

    totalBound :
      Sum.sumTo (shellContribution data) (outputShell data)
      ≤ (Int.+ 5 / 1) * delta data * lambdaQ
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
      scale * Sum.sumTo (shellContribution data) (outputShell data)
      ≤ scale * ((Int.+ 5 / 1) * delta data * lambdaQ)
    scaled =
      let instance scaleIsNonnegative = nonNegative scaleNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg scale totalBound

    targetMeaning :
      scale * ((Int.+ 5 / 1) * delta data * lambdaQ)
      ≡ (Int.+ 10 / 1) * delta data * L2.square lambdaQ
    targetMeaning = solve (delta data ∷ lambdaQ ∷ [])
  in
  ℚₚ.≤-trans
    (sourceJ11ToTotalShellContribution data)
    (subst
      (λ upper →
        scale * Sum.sumTo (shellContribution data) (outputShell data)
        ≤ upper)
      targetMeaning
      scaled)
