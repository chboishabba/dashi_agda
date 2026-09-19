{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteNormalizedWeightDobrushinExact where

------------------------------------------------------------------------
-- NORMALISING TWO FINITE POSITIVE WEIGHTS COSTS AT MOST A FACTOR TWO
--
-- Let u,v >= 0 be finite raw weights, with masses U,V, and let a,b >= 0
-- satisfy
--
--   a U = 1,     b V = 1.
--
-- The corresponding probability rows are p=a u and q=b v.  The elementary
-- identity
--
--   (a-b)V = a(V-U)
--
-- makes the normalisation correction depend on the SAME raw L1 perturbation:
--
--   ||p-q||_1 <= 2 a ||u-v||_1.
--
-- No division theorem is used.  This is the finite normalisation-stability
-- bridge needed to turn a pointwise/raw Boltzmann perturbation estimate into
-- the Dobrushin row distance of the actual normalised conditional kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteDobrushinReopeningExact as Dobrushin
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact as Abs
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm


absoluteDifferenceSymmetric : ∀ left right →
  ∣ left - right ∣ ≡ ∣ right - left ∣
absoluteDifferenceSymmetric left right =
  let
    reverseIsNegative :
      right - left ≡ - (left - right)
    reverseIsNegative = ℚRing.solve-∀ left right
  in
  trans
    (sym (ℚP.∣-p∣≡∣p∣ (left - right)))
    (cong ∣_∣ (sym reverseIsNegative))

record NormalizedFiniteWeightPair (State : Set) : Set₁ where
  field
    states : List State
    leftRaw rightRaw : State → ℚ
    leftNormalizer rightNormalizer : ℚ

    leftRawNonnegative : ∀ state → 0ℚ ≤ leftRaw state
    rightRawNonnegative : ∀ state → 0ℚ ≤ rightRaw state
    leftNormalizerNonnegative : 0ℚ ≤ leftNormalizer
    rightNormalizerNonnegative : 0ℚ ≤ rightNormalizer

    leftNormalized :
      leftNormalizer * Sums.sumRational states leftRaw ≡ 1ℚ
    rightNormalized :
      rightNormalizer * Sums.sumRational states rightRaw ≡ 1ℚ

open NormalizedFiniteWeightPair public

leftMass :
  ∀ {State} → NormalizedFiniteWeightPair State → ℚ
leftMass dataSet = Sums.sumRational (states dataSet) (leftRaw dataSet)

rightMass :
  ∀ {State} → NormalizedFiniteWeightPair State → ℚ
rightMass dataSet = Sums.sumRational (states dataSet) (rightRaw dataSet)

leftRow :
  ∀ {State} → NormalizedFiniteWeightPair State → State → ℚ
leftRow dataSet state =
  leftNormalizer dataSet * leftRaw dataSet state

rightRow :
  ∀ {State} → NormalizedFiniteWeightPair State → State → ℚ
rightRow dataSet state =
  rightNormalizer dataSet * rightRaw dataSet state

rawL1Difference :
  ∀ {State} → NormalizedFiniteWeightPair State → ℚ
rawL1Difference dataSet =
  Dobrushin.rowL1Difference
    (states dataSet)
    (leftRaw dataSet)
    (rightRaw dataSet)

normalizedRowL1Difference :
  ∀ {State} → NormalizedFiniteWeightPair State → ℚ
normalizedRowL1Difference dataSet =
  Dobrushin.rowL1Difference
    (states dataSet)
    (leftRow dataSet)
    (rightRow dataSet)

massDifferenceBelowRawL1 :
  ∀ {State} (dataSet : NormalizedFiniteWeightPair State) →
  ∣ rightMass dataSet - leftMass dataSet ∣
  ≤ rawL1Difference dataSet
massDifferenceBelowRawL1 dataSet =
  let
    sumDifference :
      rightMass dataSet - leftMass dataSet
      ≡ Sums.sumRational (states dataSet)
          (λ state → rightRaw dataSet state - leftRaw dataSet state)
    sumDifference =
      trans
        (cong
          (λ selected → selected - leftMass dataSet)
          (sym
            (Sums.sumRationalCong
              (states dataSet)
              (rightRaw dataSet)
              (λ state → rightRaw dataSet state)
              (λ _ → refl))))
        (differenceSum (states dataSet))
      where
      differenceSum :
        ∀ values →
        Sums.sumRational values (rightRaw dataSet)
          - Sums.sumRational values (leftRaw dataSet)
        ≡ Sums.sumRational values
            (λ state → rightRaw dataSet state - leftRaw dataSet state)
      differenceSum [] = ℚRing.solve []
      differenceSum (state ∷ values)
        rewrite differenceSum values =
        ℚRing.solve-∀
          (rightRaw dataSet state)
          (leftRaw dataSet state)
          (Sums.sumRational values (rightRaw dataSet))
          (Sums.sumRational values (leftRaw dataSet))

    absSum :
      ∣ Sums.sumRational (states dataSet)
          (λ state → rightRaw dataSet state - leftRaw dataSet state) ∣
      ≤ Sums.sumRational (states dataSet)
          (λ state → ∣ rightRaw dataSet state - leftRaw dataSet state ∣)
    absSum =
      Dobrushin.sumAbsUpper
        (states dataSet)
        (λ state → rightRaw dataSet state - leftRaw dataSet state)

    orient :
      Sums.sumRational (states dataSet)
          (λ state → ∣ rightRaw dataSet state - leftRaw dataSet state ∣)
      ≡ rawL1Difference dataSet
    orient =
      Sums.sumRationalCong
        (states dataSet) _ _
        (λ state → absoluteDifferenceSymmetric
          (rightRaw dataSet state)
          (leftRaw dataSet state))
  in
  subst
    (λ lower → lower ≤ rawL1Difference dataSet)
    (cong ∣_∣ sumDifference)
    (subst
      (λ upper →
        ∣ Sums.sumRational (states dataSet)
            (λ state → rightRaw dataSet state - leftRaw dataSet state) ∣
        ≤ upper)
      orient
      absSum)

normalizerCorrectionIdentity :
  ∀ {State} (dataSet : NormalizedFiniteWeightPair State) →
  (leftNormalizer dataSet - rightNormalizer dataSet) * rightMass dataSet
  ≡ leftNormalizer dataSet * (rightMass dataSet - leftMass dataSet)
normalizerCorrectionIdentity dataSet =
  let
    a = leftNormalizer dataSet
    b = rightNormalizer dataSet
    U = leftMass dataSet
    V = rightMass dataSet
    aU : a * U ≡ 1ℚ
    aU = leftNormalized dataSet
    bV : b * V ≡ 1ℚ
    bV = rightNormalized dataSet
  in
  trans
    (ℚRing.solve-∀ a b V :
      (a - b) * V ≡ a * V - b * V)
    (trans
      (cong (λ selected → a * V - selected) bV)
      (trans
        (cong (λ selected → a * V - selected) (sym aU))
        (ℚRing.solve-∀ a U V :
          a * V - a * U ≡ a * (V - U)))))

normalizerCorrectionBelowRawL1 :
  ∀ {State} (dataSet : NormalizedFiniteWeightPair State) →
  ∣ leftNormalizer dataSet - rightNormalizer dataSet ∣
    * rightMass dataSet
  ≤ leftNormalizer dataSet * rawL1Difference dataSet
normalizerCorrectionBelowRawL1 dataSet =
  let
    rightMassNN : 0ℚ ≤ rightMass dataSet
    rightMassNN =
      sumNN (states dataSet)
      where
      sumNN : ∀ values →
        0ℚ ≤ Sums.sumRational values (rightRaw dataSet)
      sumNN [] = ℚP.≤-refl
      sumNN (state ∷ values) =
        subst
          (λ lower →
            lower ≤ rightRaw dataSet state
              + Sums.sumRational values (rightRaw dataSet))
          (sym (ℚP.+-identityˡ 0ℚ))
          (ℚP.+-mono-≤
            (rightRawNonnegative dataSet state)
            (sumNN values))

    correctionAbsExact :
      ∣ leftNormalizer dataSet - rightNormalizer dataSet ∣
        * rightMass dataSet
      ≡
      ∣
        (leftNormalizer dataSet - rightNormalizer dataSet)
          * rightMass dataSet
      ∣
    correctionAbsExact =
      trans
        (cong
          (∣ leftNormalizer dataSet - rightNormalizer dataSet ∣ *_)
          (sym (ℚP.∣p∣≡p rightMassNN)))
        (sym
          (ℚP.∣p*q∣≡∣p∣*∣q∣
            (leftNormalizer dataSet - rightNormalizer dataSet)
            (rightMass dataSet)))

    normalizedIdentityAbs :
      ∣
        (leftNormalizer dataSet - rightNormalizer dataSet)
          * rightMass dataSet
      ∣
      ≡
      ∣ leftNormalizer dataSet
          * (rightMass dataSet - leftMass dataSet) ∣
    normalizedIdentityAbs =
      cong ∣_∣ (normalizerCorrectionIdentity dataSet)

    scaledMassDifference :
      ∣ leftNormalizer dataSet
          * (rightMass dataSet - leftMass dataSet) ∣
      ≤ leftNormalizer dataSet * rawL1Difference dataSet
    scaledMassDifference =
      subst
        (λ lower →
          lower ≤ leftNormalizer dataSet * rawL1Difference dataSet)
        (sym
          (trans
            (ℚP.∣p*q∣≡∣p∣*∣q∣
              (leftNormalizer dataSet)
              (rightMass dataSet - leftMass dataSet))
            (cong
              (_* ∣ rightMass dataSet - leftMass dataSet ∣)
              (ℚP.∣p∣≡p (leftNormalizerNonnegative dataSet)))))
        (Norm.scaleNonnegative
          (leftNormalizer dataSet)
          (leftNormalizerNonnegative dataSet)
          (massDifferenceBelowRawL1 dataSet))
  in
  subst
    (λ lower →
      lower ≤ leftNormalizer dataSet * rawL1Difference dataSet)
    correctionAbsExact
    (subst
      (λ lower →
        lower ≤ leftNormalizer dataSet * rawL1Difference dataSet)
      normalizedIdentityAbs
      scaledMassDifference)

pointwiseNormalizedDifference :
  ∀ {State} (dataSet : NormalizedFiniteWeightPair State) state →
  leftRow dataSet state - rightRow dataSet state
  ≡
  leftNormalizer dataSet
    * (leftRaw dataSet state - rightRaw dataSet state)
  + (leftNormalizer dataSet - rightNormalizer dataSet)
    * rightRaw dataSet state
pointwiseNormalizedDifference dataSet state =
  ℚRing.solve-∀
    (leftNormalizer dataSet)
    (rightNormalizer dataSet)
    (leftRaw dataSet state)
    (rightRaw dataSet state)

normalizedRowL1BelowTwiceRawL1 :
  ∀ {State} (dataSet : NormalizedFiniteWeightPair State) →
  normalizedRowL1Difference dataSet
  ≤
  (1ℚ + 1ℚ)
    * (leftNormalizer dataSet * rawL1Difference dataSet)
normalizedRowL1BelowTwiceRawL1 dataSet =
  let
    a = leftNormalizer dataSet
    d = rawL1Difference dataSet

    first :
      normalizedRowL1Difference dataSet
      ≤
      Sums.sumRational (states dataSet)
        (λ state →
          ∣ a * (leftRaw dataSet state - rightRaw dataSet state) ∣
          +
          ∣ (a - rightNormalizer dataSet)
              * rightRaw dataSet state ∣)
    first =
      Dobrushin.sumMono
        (states dataSet)
        (λ state →
          ∣ leftRow dataSet state - rightRow dataSet state ∣)
        (λ state →
          ∣ a * (leftRaw dataSet state - rightRaw dataSet state) ∣
          + ∣ (a - rightNormalizer dataSet)
              * rightRaw dataSet state ∣)
        (λ state →
          subst
            (λ selected →
              ∣ selected ∣
              ≤
              ∣ a * (leftRaw dataSet state - rightRaw dataSet state) ∣
              + ∣ (a - rightNormalizer dataSet)
                  * rightRaw dataSet state ∣)
            (pointwiseNormalizedDifference dataSet state)
            (ℚP.∣p+q∣≤∣p∣+∣q∣
              (a * (leftRaw dataSet state - rightRaw dataSet state))
              ((a - rightNormalizer dataSet)
                * rightRaw dataSet state)))

    split :
      Sums.sumRational (states dataSet)
        (λ state →
          ∣ a * (leftRaw dataSet state - rightRaw dataSet state) ∣
          +
          ∣ (a - rightNormalizer dataSet)
              * rightRaw dataSet state ∣)
      ≡
      Sums.sumRational (states dataSet)
        (λ state →
          ∣ a * (leftRaw dataSet state - rightRaw dataSet state) ∣)
      +
      Sums.sumRational (states dataSet)
        (λ state →
          ∣ (a - rightNormalizer dataSet)
              * rightRaw dataSet state ∣)
    split =
      splitSum (states dataSet)
      where
      splitSum : ∀ values →
        Sums.sumRational values
          (λ state →
            ∣ a * (leftRaw dataSet state - rightRaw dataSet state) ∣
            + ∣ (a - rightNormalizer dataSet)
                * rightRaw dataSet state ∣)
        ≡
        Sums.sumRational values
          (λ state →
            ∣ a * (leftRaw dataSet state - rightRaw dataSet state) ∣)
        +
        Sums.sumRational values
          (λ state →
            ∣ (a - rightNormalizer dataSet)
                * rightRaw dataSet state ∣)
      splitSum [] = ℚRing.solve []
      splitSum (state ∷ values)
        rewrite splitSum values =
        ℚRing.solve-∀
          ∣ a * (leftRaw dataSet state - rightRaw dataSet state) ∣
          ∣ (a - rightNormalizer dataSet)
              * rightRaw dataSet state ∣
          (Sums.sumRational values
            (λ selected →
              ∣ a * (leftRaw dataSet selected - rightRaw dataSet selected) ∣))
          (Sums.sumRational values
            (λ selected →
              ∣ (a - rightNormalizer dataSet)
                  * rightRaw dataSet selected ∣))

    rawScaledExact :
      Sums.sumRational (states dataSet)
        (λ state →
          ∣ a * (leftRaw dataSet state - rightRaw dataSet state) ∣)
      ≡ a * d
    rawScaledExact =
      trans
        (Sums.sumRationalCong
          (states dataSet) _ _
          (λ state →
            trans
              (ℚP.∣p*q∣≡∣p∣*∣q∣
                a (leftRaw dataSet state - rightRaw dataSet state))
              (cong
                (_* ∣ leftRaw dataSet state - rightRaw dataSet state ∣)
                (ℚP.∣p∣≡p (leftNormalizerNonnegative dataSet)))))
        (Sums.sumRationalScale
          a
          (states dataSet)
          (λ state →
            ∣ leftRaw dataSet state - rightRaw dataSet state ∣))

    correctionScaledExact :
      Sums.sumRational (states dataSet)
        (λ state →
          ∣ (a - rightNormalizer dataSet)
              * rightRaw dataSet state ∣)
      ≡
      ∣ a - rightNormalizer dataSet ∣ * rightMass dataSet
    correctionScaledExact =
      trans
        (Sums.sumRationalCong
          (states dataSet) _ _
          (λ state →
            trans
              (ℚP.∣p*q∣≡∣p∣*∣q∣
                (a - rightNormalizer dataSet)
                (rightRaw dataSet state))
              (cong
                (∣ a - rightNormalizer dataSet ∣ *_)
                (ℚP.∣p∣≡p
                  (rightRawNonnegative dataSet state)))))
        (Sums.sumRationalScale
          ∣ a - rightNormalizer dataSet ∣
          (states dataSet)
          (rightRaw dataSet))

    second :
      Sums.sumRational (states dataSet)
        (λ state →
          ∣ a * (leftRaw dataSet state - rightRaw dataSet state) ∣)
      +
      Sums.sumRational (states dataSet)
        (λ state →
          ∣ (a - rightNormalizer dataSet)
              * rightRaw dataSet state ∣)
      ≤ a * d + a * d
    second =
      subst
        (λ left →
          left
          ≤ a * d + a * d)
        (sym
          (cong₂ _+_ rawScaledExact correctionScaledExact))
        (ℚP.+-mono-≤
          ℚP.≤-refl
          (normalizerCorrectionBelowRawL1 dataSet))
      where
      cong₂ : ∀ {A B C : Set} {x x' : A} {y y' : B} →
        (f : A → B → C) → x ≡ x' → y ≡ y' →
        f x y ≡ f x' y'
      cong₂ f refl refl = refl

    twiceExact :
      a * d + a * d ≡ (1ℚ + 1ℚ) * (a * d)
    twiceExact = ℚRing.solve-∀ a d
  in
  ℚP.≤-trans first
    (subst
      (λ upper →
        Sums.sumRational (states dataSet)
          (λ state →
            ∣ a * (leftRaw dataSet state - rightRaw dataSet state) ∣
            + ∣ (a - rightNormalizer dataSet)
                * rightRaw dataSet state ∣)
        ≤ upper)
      (trans split (trans (cong₂ _+_ rawScaledExact correctionScaledExact)
        twiceExact))
      ℚP.≤-refl)
  where
  cong₂ : ∀ {A B C : Set} {x x' : A} {y y' : B} →
    (f : A → B → C) → x ≡ x' → y ≡ y' →
    f x y ≡ f x' y'
  cong₂ f refl refl = refl


record RelativeRawWeightPerturbation
    {State : Set}
    (dataSet : NormalizedFiniteWeightPair State) : Set₁ where
  field
    epsilon : ℚ
    epsilonNonnegative : 0ℚ ≤ epsilon
    pointwiseRelativeDifference : ∀ state →
      ∣ leftRaw dataSet state - rightRaw dataSet state ∣
      ≤ epsilon * leftRaw dataSet state

open RelativeRawWeightPerturbation public

rawL1BelowRelativeMass :
  ∀ {State}
    {dataSet : NormalizedFiniteWeightPair State}
    (relative : RelativeRawWeightPerturbation dataSet) →
  rawL1Difference dataSet
  ≤ epsilon relative * leftMass dataSet
rawL1BelowRelativeMass {dataSet = dataSet} relative =
  let
    summed =
      Dobrushin.sumMono
        (states dataSet)
        (λ state →
          ∣ leftRaw dataSet state - rightRaw dataSet state ∣)
        (λ state → epsilon relative * leftRaw dataSet state)
        (pointwiseRelativeDifference relative)
    factor =
      Sums.sumRationalScale
        (epsilon relative)
        (states dataSet)
        (leftRaw dataSet)
  in
  subst
    (λ upper → rawL1Difference dataSet ≤ upper)
    factor
    summed

leftNormalizedScaleCancelsMass :
  ∀ {State} (dataSet : NormalizedFiniteWeightPair State) epsilonValue →
  leftNormalizer dataSet * (epsilonValue * leftMass dataSet)
  ≡ epsilonValue
leftNormalizedScaleCancelsMass dataSet epsilonValue =
  trans
    (ℚRing.solve-∀
      (leftNormalizer dataSet)
      epsilonValue
      (leftMass dataSet) :
      leftNormalizer dataSet * (epsilonValue * leftMass dataSet)
      ≡ epsilonValue * (leftNormalizer dataSet * leftMass dataSet))
    (trans
      (cong (epsilonValue *_) (leftNormalized dataSet))
      (ℚP.*-identityʳ epsilonValue)))

normalizedRowL1BelowTwiceRelativePerturbation :
  ∀ {State}
    {dataSet : NormalizedFiniteWeightPair State}
    (relative : RelativeRawWeightPerturbation dataSet) →
  normalizedRowL1Difference dataSet
  ≤ (1ℚ + 1ℚ) * epsilon relative
normalizedRowL1BelowTwiceRelativePerturbation
    {dataSet = dataSet} relative =
  let
    rawBound =
      rawL1BelowRelativeMass relative

    scaledRaw :
      leftNormalizer dataSet * rawL1Difference dataSet
      ≤ epsilon relative
    scaledRaw =
      subst
        (λ upper →
          leftNormalizer dataSet * rawL1Difference dataSet
          ≤ upper)
        (leftNormalizedScaleCancelsMass dataSet (epsilon relative))
        (Norm.scaleNonnegative
          (leftNormalizer dataSet)
          (leftNormalizerNonnegative dataSet)
          rawBound)

    twoNN : 0ℚ ≤ 1ℚ + 1ℚ
    twoNN = ℚP.+-mono-≤ ℚP.0≤1 ℚP.0≤1

    scaledTwo =
      Norm.scaleNonnegative
        (1ℚ + 1ℚ)
        twoNN
        scaledRaw
  in
  ℚP.≤-trans
    (normalizedRowL1BelowTwiceRawL1 dataSet)
    scaledTwo

finiteNormalizedWeightDobrushinLevel : ProofLevel
finiteNormalizedWeightDobrushinLevel = machineChecked
