{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayR445WeightedExteriorInfluenceFiniteExact where

------------------------------------------------------------------------
-- SOURCE / STATUS
--
-- Finite generic R445 conditional-mixture compiler reconstructed from
-- Docs/physics/YMClayR445WeightedExteriorInfluenceMaxCut20261114.md:10-51
-- and scripts/check_ym_r445_weighted_exterior_influence.py.  This is only the
-- finite probability inequality (I)/(III); it does NOT prove a Wilson kernel
-- bound, an exterior coupling bound, D1, D2, or any Clay endpoint.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteDobrushinReopeningExact as Dob
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Rows
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact as Bound
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

sumDifferenceExact :
  ∀ {A : Set} (values : List A) (f g : A → ℚ) →
  Sums.sumRational values f - Sums.sumRational values g
  ≡ Sums.sumRational values (λ value → f value - g value)
sumDifferenceExact [] f g = ℚRing.solve []
sumDifferenceExact (value ∷ values) f g
  rewrite sym (sumDifferenceExact values f g) =
  ℚRing.solve-∀
    (f value)
    (g value)
    (Sums.sumRational values f)
    (Sums.sumRational values g)

sameWeightObservableDifferenceSumExact :
  ∀ {A : Set} (values : List A) (weight f g : A → ℚ) →
  Sums.sumRational values (λ value → weight value * f value)
  - Sums.sumRational values (λ value → weight value * g value)
  ≡ Sums.sumRational values
      (λ value → weight value * (f value - g value))
sameWeightObservableDifferenceSumExact [] weight f g = ℚRing.solve []
sameWeightObservableDifferenceSumExact (value ∷ values) weight f g
  rewrite sym (sameWeightObservableDifferenceSumExact values weight f g) =
  ℚRing.solve-∀
    (weight value)
    (f value)
    (g value)
    (Sums.sumRational values (λ selected → weight selected * f selected))
    (Sums.sumRational values (λ selected → weight selected * g selected))

subtractTriangleAlgebra : ∀ left middle right : ℚ →
  (left - middle) + (middle - right) ≡ left - right
subtractTriangleAlgebra = ℚRing.solve-∀

weightedAbsDifferenceSumUpper :
  ∀ {A : Set} (values : List A) (weight f g : A → ℚ) →
  (∀ value → 0ℚ ≤ weight value) →
  ∣ Sums.sumRational values
      (λ value → weight value * (f value - g value)) ∣
  ≤ Sums.sumRational values
      (λ value → weight value * ∣ f value - g value ∣)
weightedAbsDifferenceSumUpper values weight f g weightNN =
  ℚP.≤-trans
    (Dob.sumAbsUpper values
      (λ value → weight value * (f value - g value)))
    (Dob.sumMono values _ _
      (λ value →
        subst
          (λ upper →
            ∣ weight value * (f value - g value) ∣ ≤ upper)
          (cong
            (λ absWeight → absWeight * ∣ f value - g value ∣)
            (ℚP.0≤p⇒∣p∣≡p (weightNN value)))
          (Bound.absoluteProductBound
            {left = weight value}
            {right = f value - g value}
            {leftBound = ∣ weight value ∣}
            {rightBound = ∣ f value - g value ∣}
            ℚP.≤-refl
            ℚP.≤-refl
            (ℚP.0≤∣p∣ (weight value))
            (ℚP.0≤∣p∣ (f value - g value)))))

record FiniteExteriorCoupling (X Y Coupling : Set) : Set₁ where
  field
    xs : List X
    ys : List Y
    couplings : List Coupling
    leftWorld : Coupling → Y
    rightWorld : Coupling → Y
    p : Y → ℚ
    couplingWeight : Coupling → ℚ
    kernelP : X → Y → ℚ
    kernelQ : X → Y → ℚ
    localKernelBudget : Y → ℚ
    pairKernelBudget : Coupling → ℚ
    pNonnegative : ∀ y → 0ℚ ≤ p y
    couplingWeightNonnegative : ∀ pair → 0ℚ ≤ couplingWeight pair
    leftMarginalExpectation : ∀ observable →
      Sums.sumRational ys (λ y → p y * observable y)
      ≡ Sums.sumRational couplings
          (λ pair → couplingWeight pair * observable (leftWorld pair))

open FiniteExteriorCoupling public

kernelPDistance :
  ∀ {X Y Coupling : Set} → FiniteExteriorCoupling X Y Coupling → Y → ℚ
kernelPDistance dataSet y =
  Sums.sumRational (xs dataSet)
    (λ x → ∣ kernelP dataSet x y - kernelQ dataSet x y ∣)

kernelQDistance :
  ∀ {X Y Coupling : Set} → FiniteExteriorCoupling X Y Coupling → Coupling → ℚ
kernelQDistance dataSet pair =
  Sums.sumRational (xs dataSet)
    (λ x →
      ∣ kernelQ dataSet x (leftWorld dataSet pair)
        - kernelQ dataSet x (rightWorld dataSet pair) ∣)

kernelPDistanceNonnegative :
  ∀ {X Y Coupling : Set} (dataSet : FiniteExteriorCoupling X Y Coupling) y →
  0ℚ ≤ kernelPDistance dataSet y
kernelPDistanceNonnegative dataSet y =
  Dob.rowL1DifferenceNonnegative
    (xs dataSet)
    (λ x → kernelP dataSet x y)
    (λ x → kernelQ dataSet x y)

kernelQDistanceNonnegative :
  ∀ {X Y Coupling : Set} (dataSet : FiniteExteriorCoupling X Y Coupling) pair →
  0ℚ ≤ kernelQDistance dataSet pair
kernelQDistanceNonnegative dataSet pair =
  Dob.rowL1DifferenceNonnegative
    (xs dataSet)
    (λ x → kernelQ dataSet x (leftWorld dataSet pair))
    (λ x → kernelQ dataSet x (rightWorld dataSet pair))

kernelPPartBound :
  ∀ {X Y Coupling : Set} (dataSet : FiniteExteriorCoupling X Y Coupling) →
  (∀ y → kernelPDistance dataSet y ≤ localKernelBudget dataSet y) →
  ∣
    Sums.sumRational (xs dataSet)
      (λ x → Sums.sumRational (ys dataSet)
        (λ y → p dataSet y * kernelP dataSet x y))
    - Sums.sumRational (xs dataSet)
      (λ x → Sums.sumRational (ys dataSet)
        (λ y → p dataSet y * kernelQ dataSet x y))
  ∣
  ≤ Sums.sumRational (ys dataSet)
      (λ y → p dataSet y * localKernelBudget dataSet y)
kernelPPartBound dataSet kernelBudget =
  let
    Xs = xs dataSet
    Ys = ys dataSet

    firstExact :
      Sums.sumRational Xs
        (λ x → Sums.sumRational Ys
          (λ y → p dataSet y * kernelP dataSet x y))
      - Sums.sumRational Xs
        (λ x → Sums.sumRational Ys
          (λ y → p dataSet y * kernelQ dataSet x y))
      ≡ Sums.sumRational Xs
        (λ x → Sums.sumRational Ys
          (λ y → p dataSet y
            * (kernelP dataSet x y - kernelQ dataSet x y)))
    firstExact =
      trans
        (sumDifferenceExact Xs
          (λ x → Sums.sumRational Ys
            (λ y → p dataSet y * kernelP dataSet x y))
          (λ x → Sums.sumRational Ys
            (λ y → p dataSet y * kernelQ dataSet x y)))
        (Sums.sumRationalCong Xs _ _
          (λ x →
            sameWeightObservableDifferenceSumExact
              Ys (p dataSet) (kernelP dataSet x) (kernelQ dataSet x)))

    firstTriangle :
      ∣
        Sums.sumRational Xs
          (λ x → Sums.sumRational Ys
            (λ y → p dataSet y * kernelP dataSet x y))
        - Sums.sumRational Xs
          (λ x → Sums.sumRational Ys
            (λ y → p dataSet y * kernelQ dataSet x y))
      ∣
      ≤ Sums.sumRational Xs
        (λ x → ∣ Sums.sumRational Ys
          (λ y → p dataSet y
            * (kernelP dataSet x y - kernelQ dataSet x y)) ∣)
    firstTriangle =
      subst
        (λ lower →
          ∣ lower ∣ ≤ Sums.sumRational Xs
            (λ x → ∣ Sums.sumRational Ys
              (λ y → p dataSet y
                * (kernelP dataSet x y - kernelQ dataSet x y)) ∣))
        (sym firstExact)
        (Dob.sumAbsUpper Xs
          (λ x → Sums.sumRational Ys
            (λ y → p dataSet y
              * (kernelP dataSet x y - kernelQ dataSet x y))))

    firstAbs :
      Sums.sumRational Xs
        (λ x → ∣ Sums.sumRational Ys
          (λ y → p dataSet y
            * (kernelP dataSet x y - kernelQ dataSet x y)) ∣)
      ≤ Sums.sumRational Xs
        (λ x → Sums.sumRational Ys
          (λ y → p dataSet y
            * ∣ kernelP dataSet x y - kernelQ dataSet x y ∣))
    firstAbs =
      Dob.sumMono Xs _ _
        (λ x →
          weightedAbsDifferenceSumUpper
            Ys (p dataSet) (kernelP dataSet x) (kernelQ dataSet x)
            (pNonnegative dataSet))

    firstSwap :
      Sums.sumRational Xs
        (λ x → Sums.sumRational Ys
          (λ y → p dataSet y
            * ∣ kernelP dataSet x y - kernelQ dataSet x y ∣))
      ≡ Sums.sumRational Ys
        (λ y → p dataSet y
          * Sums.sumRational Xs
            (λ x → ∣ kernelP dataSet x y - kernelQ dataSet x y ∣))
    firstSwap =
      trans
        (Rows.sumSwap Ys Xs
          (λ y x → p dataSet y
            * ∣ kernelP dataSet x y - kernelQ dataSet x y ∣))
        (Sums.sumRationalCong Ys _ _
          (λ y →
            Sums.sumRationalScale (p dataSet y) Xs
              (λ x → ∣ kernelP dataSet x y - kernelQ dataSet x y ∣)))

    firstBudget :
      Sums.sumRational Ys
        (λ y → p dataSet y
          * Sums.sumRational Xs
            (λ x → ∣ kernelP dataSet x y - kernelQ dataSet x y ∣))
      ≤ Sums.sumRational Ys
        (λ y → p dataSet y * localKernelBudget dataSet y)
    firstBudget =
      Dob.sumMono Ys _ _
        (λ y →
          Norm.scaleNonnegative
            (p dataSet y)
            (pNonnegative dataSet y)
            (kernelBudget y))
  in
  ℚP.≤-trans
    firstTriangle
    (ℚP.≤-trans
      firstAbs
      (subst
        (λ lower →
          lower ≤ Sums.sumRational Ys
            (λ y → p dataSet y * localKernelBudget dataSet y))
        (sym firstSwap)
        firstBudget))

kernelQPartBound :
  ∀ {X Y Coupling : Set} (dataSet : FiniteExteriorCoupling X Y Coupling) →
  (∀ pair → kernelQDistance dataSet pair ≤ pairKernelBudget dataSet pair) →
  ∣
    Sums.sumRational (xs dataSet)
      (λ x → Sums.sumRational (ys dataSet)
        (λ y → p dataSet y * kernelQ dataSet x y))
    - Sums.sumRational (xs dataSet)
      (λ x → Sums.sumRational (couplings dataSet)
        (λ pair → couplingWeight dataSet pair
          * kernelQ dataSet x (rightWorld dataSet pair)))
  ∣
  ≤ Sums.sumRational (couplings dataSet)
      (λ pair → couplingWeight dataSet pair
        * pairKernelBudget dataSet pair)
kernelQPartBound dataSet kernelBudget =
  let
    Xs = xs dataSet
    Ys = ys dataSet
    Zs = couplings dataSet

    secondExact :
      Sums.sumRational Xs
        (λ x → Sums.sumRational Ys
          (λ y → p dataSet y * kernelQ dataSet x y))
      - Sums.sumRational Xs
        (λ x → Sums.sumRational Zs
          (λ pair → couplingWeight dataSet pair
            * kernelQ dataSet x (rightWorld dataSet pair)))
      ≡ Sums.sumRational Xs
        (λ x → Sums.sumRational Zs
          (λ pair → couplingWeight dataSet pair
            * (kernelQ dataSet x (leftWorld dataSet pair)
              - kernelQ dataSet x (rightWorld dataSet pair))))
    secondExact =
      trans
        (sumDifferenceExact Xs
          (λ x → Sums.sumRational Ys
            (λ y → p dataSet y * kernelQ dataSet x y))
          (λ x → Sums.sumRational Zs
            (λ pair → couplingWeight dataSet pair
              * kernelQ dataSet x (rightWorld dataSet pair))))
        (Sums.sumRationalCong Xs _ _
          (λ x →
            trans
              (cong
                (λ replaced → replaced
                  - Sums.sumRational Zs
                    (λ pair → couplingWeight dataSet pair
                      * kernelQ dataSet x (rightWorld dataSet pair)))
                (leftMarginalExpectation dataSet
                  (λ y → kernelQ dataSet x y)))
              (sameWeightObservableDifferenceSumExact
                Zs (couplingWeight dataSet)
                (λ pair → kernelQ dataSet x (leftWorld dataSet pair))
                (λ pair → kernelQ dataSet x (rightWorld dataSet pair)))))

    secondTriangle :
      ∣
        Sums.sumRational Xs
          (λ x → Sums.sumRational Ys
            (λ y → p dataSet y * kernelQ dataSet x y))
        - Sums.sumRational Xs
          (λ x → Sums.sumRational Zs
            (λ pair → couplingWeight dataSet pair
              * kernelQ dataSet x (rightWorld dataSet pair)))
      ∣
      ≤ Sums.sumRational Xs
        (λ x → ∣ Sums.sumRational Zs
          (λ pair → couplingWeight dataSet pair
            * (kernelQ dataSet x (leftWorld dataSet pair)
              - kernelQ dataSet x (rightWorld dataSet pair))) ∣)
    secondTriangle =
      subst
        (λ lower →
          ∣ lower ∣ ≤ Sums.sumRational Xs
            (λ x → ∣ Sums.sumRational Zs
              (λ pair → couplingWeight dataSet pair
                * (kernelQ dataSet x (leftWorld dataSet pair)
                  - kernelQ dataSet x (rightWorld dataSet pair))) ∣))
        (sym secondExact)
        (Dob.sumAbsUpper Xs
          (λ x → Sums.sumRational Zs
            (λ pair → couplingWeight dataSet pair
              * (kernelQ dataSet x (leftWorld dataSet pair)
                - kernelQ dataSet x (rightWorld dataSet pair)))))

    secondAbs :
      Sums.sumRational Xs
        (λ x → ∣ Sums.sumRational Zs
          (λ pair → couplingWeight dataSet pair
            * (kernelQ dataSet x (leftWorld dataSet pair)
              - kernelQ dataSet x (rightWorld dataSet pair))) ∣)
      ≤ Sums.sumRational Xs
        (λ x → Sums.sumRational Zs
          (λ pair → couplingWeight dataSet pair
            * ∣ kernelQ dataSet x (leftWorld dataSet pair)
              - kernelQ dataSet x (rightWorld dataSet pair) ∣))
    secondAbs =
      Dob.sumMono Xs _ _
        (λ x →
          weightedAbsDifferenceSumUpper
            Zs (couplingWeight dataSet)
            (λ pair → kernelQ dataSet x (leftWorld dataSet pair))
            (λ pair → kernelQ dataSet x (rightWorld dataSet pair))
            (couplingWeightNonnegative dataSet))

    secondSwap :
      Sums.sumRational Xs
        (λ x → Sums.sumRational Zs
          (λ pair → couplingWeight dataSet pair
            * ∣ kernelQ dataSet x (leftWorld dataSet pair)
              - kernelQ dataSet x (rightWorld dataSet pair) ∣))
      ≡ Sums.sumRational Zs
        (λ pair → couplingWeight dataSet pair
          * Sums.sumRational Xs
            (λ x → ∣ kernelQ dataSet x (leftWorld dataSet pair)
              - kernelQ dataSet x (rightWorld dataSet pair) ∣))
    secondSwap =
      trans
        (Rows.sumSwap Zs Xs
          (λ pair x → couplingWeight dataSet pair
            * ∣ kernelQ dataSet x (leftWorld dataSet pair)
              - kernelQ dataSet x (rightWorld dataSet pair) ∣))
        (Sums.sumRationalCong Zs _ _
          (λ pair →
            Sums.sumRationalScale (couplingWeight dataSet pair) Xs
              (λ x → ∣ kernelQ dataSet x (leftWorld dataSet pair)
                - kernelQ dataSet x (rightWorld dataSet pair) ∣)))

    secondBudget :
      Sums.sumRational Zs
        (λ pair → couplingWeight dataSet pair
          * Sums.sumRational Xs
            (λ x → ∣ kernelQ dataSet x (leftWorld dataSet pair)
              - kernelQ dataSet x (rightWorld dataSet pair) ∣))
      ≤ Sums.sumRational Zs
        (λ pair → couplingWeight dataSet pair
          * pairKernelBudget dataSet pair)
    secondBudget =
      Dob.sumMono Zs _ _
        (λ pair →
          Norm.scaleNonnegative
            (couplingWeight dataSet pair)
            (couplingWeightNonnegative dataSet pair)
            (kernelBudget pair))
  in
  ℚP.≤-trans
    secondTriangle
    (ℚP.≤-trans
      secondAbs
      (subst
        (λ lower →
          lower ≤ Sums.sumRational Zs
            (λ pair → couplingWeight dataSet pair
              * pairKernelBudget dataSet pair))
        (sym secondSwap)
        secondBudget))

weightedExteriorInfluenceBound :
  ∀ {X Y Coupling : Set} (dataSet : FiniteExteriorCoupling X Y Coupling) →
  (∀ y → kernelPDistance dataSet y ≤ localKernelBudget dataSet y) →
  (∀ pair → kernelQDistance dataSet pair ≤ pairKernelBudget dataSet pair) →
  ∣
    Sums.sumRational (xs dataSet)
      (λ x → Sums.sumRational (ys dataSet)
        (λ y → p dataSet y * kernelP dataSet x y))
    - Sums.sumRational (xs dataSet)
      (λ x → Sums.sumRational (couplings dataSet)
        (λ pair → couplingWeight dataSet pair
          * kernelQ dataSet x (rightWorld dataSet pair)))
  ∣
  ≤ Sums.sumRational (ys dataSet)
      (λ y → p dataSet y * localKernelBudget dataSet y)
    + Sums.sumRational (couplings dataSet)
      (λ pair → couplingWeight dataSet pair
        * pairKernelBudget dataSet pair)
weightedExteriorInfluenceBound dataSet kernelBudget pairBudget =
  let
    leftValue =
      Sums.sumRational (xs dataSet)
        (λ x → Sums.sumRational (ys dataSet)
          (λ y → p dataSet y * kernelP dataSet x y))
    middleValue =
      Sums.sumRational (xs dataSet)
        (λ x → Sums.sumRational (ys dataSet)
          (λ y → p dataSet y * kernelQ dataSet x y))
    rightValue =
      Sums.sumRational (xs dataSet)
        (λ x → Sums.sumRational (couplings dataSet)
          (λ pair → couplingWeight dataSet pair
            * kernelQ dataSet x (rightWorld dataSet pair)))

    triangle :
      ∣ leftValue - rightValue ∣
      ≤ ∣ leftValue - middleValue ∣ + ∣ middleValue - rightValue ∣
    triangle =
      subst
        (λ lower →
          ∣ lower ∣ ≤ ∣ leftValue - middleValue ∣
            + ∣ middleValue - rightValue ∣)
        (subtractTriangleAlgebra leftValue middleValue rightValue)
        (ℚP.∣p+q∣≤∣p∣+∣q∣
          (leftValue - middleValue)
          (middleValue - rightValue))
  in
  ℚP.≤-trans
    triangle
    (ℚP.+-mono-≤
      (kernelPPartBound dataSet kernelBudget)
      (kernelQPartBound dataSet pairBudget))

finiteWeightedExteriorInfluenceLevel : ProofLevel
finiteWeightedExteriorInfluenceLevel = machineChecked
