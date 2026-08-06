module DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionScalarYoungExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
-- arXiv:2204.12737.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field".
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Close the signed scalar seam left after the exact atom-norm calculation.
-- For nonnegative n,m and a rational quaternion z satisfying
--
--                       N(z) = n m,
--
-- prove without square roots that
--
--                    -q0(z) <= (n+m)/2.
--
-- The proof uses q0(z)^2 <= N(z), the polynomial AM--GM identity
--
--   ((n+m)/2)^2 - nm = (n-m)^2/4 >= 0,
--
-- and reflection of the square order on nonnegative rationals.  Applying this
-- to the exact norms of the four diagonal and twelve ordered cross atoms proves
-- every named Wilson scalar is below its literal local Young budget.  Summing
-- the actual recursive product-rule order gives the concrete plaquette bound
--
--           sum of sixteen Wilson scalars <= 4 sum_i N(X_i).
--
-- Combined with the separately proved edge--plaquette incidence, this is the
-- local analytic producer of the Shen--Zhu--Zhu coefficient 8(d-1); it is not a
-- supplied Hessian-bound receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_; _/_
  ; NonNegative; NonZero; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionAtomNormExact as Atom
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralAtomGeneratedProductBridgeExact as Generated
import DASHI.Physics.YangMills.BalabanStrongCouplingSixteenAtomIncidenceBudgetExact as Budget

------------------------------------------------------------------------
-- Square-root-free scalar and AM--GM lemmas.
------------------------------------------------------------------------

nonnegativeSquareReflectsOrder :
  ∀ x bound →
  0ℚ ≤ x → 0ℚ ≤ bound →
  x * x ≤ bound * bound →
  x ≤ bound
nonnegativeSquareReflectsOrder x bound xNonnegative boundNonnegative squares
  with ℚP.≤-total x bound
... | inj₁ x≤bound = x≤bound
... | inj₂ bound≤x with ℚP._≡?_ x 0ℚ
...   | yes xZero =
  subst (λ selected → selected ≤ bound) (sym xZero) boundNonnegative
...   | no xNonzero =
  let
    instance
      xNN : NonNegative x
      xNN = ℚ.nonNegative xNonnegative

      boundNN : NonNegative bound
      boundNN = ℚ.nonNegative boundNonnegative

      xNZ : NonZero x
      xNZ = ℚ.≢-nonZero xNonzero

      xPositive : Positive x
      xPositive = ℚP.nonNeg∧nonZero⇒pos x

    boundSquareBelowBoundX : bound * bound ≤ bound * x
    boundSquareBelowBoundX =
      ℚP.*-monoˡ-≤-nonNeg bound bound≤x

    xSquareBelowBoundX : x * x ≤ bound * x
    xSquareBelowBoundX =
      ℚP.≤-trans squares boundSquareBelowBoundX
  in
  ℚP.*-cancelʳ-≤-pos x xSquareBelowBoundX

average : ℚ → ℚ → ℚ
average left right = (+ 1 / 2) * (left + right)

averageNonnegative :
  ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right →
  0ℚ ≤ average left right
averageNonnegative left right leftNN rightNN =
  Norm.scaleNonnegative
    (+ 1 / 2)
    (ℚP.nonNegative⁻¹ (+ 1 / 2))
    (FiniteL2.addNonnegative leftNN rightNN)

productBelowAverageSquare :
  ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right →
  left * right ≤ average left right * average left right
productBelowAverageSquare left right leftNN rightNN =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ selected → 0ℚ ≤ selected)
      (ℚRing.solve-∀ left right)
      (Norm.scaleNonnegative
        (+ 1 / 4)
        (ℚP.nonNegative⁻¹ (+ 1 / 4))
        (FiniteL2.squareNonnegative (left - right))))

negativeScalarSquareBelowNormSq :
  ∀ value →
  (- Q.q0 value) * (- Q.q0 value) ≤ Norm.normSq value
negativeScalarSquareBelowNormSq value =
  subst
    (λ selected → selected ≤ Norm.normSq value)
    (ℚRing.solve-∀ (Q.q0 value))
    (Norm.scalarPartSquareBelowNormSq value)

negativeScalarBelowYoung :
  ∀ value left right →
  Norm.normSq value ≡ left * right →
  0ℚ ≤ left → 0ℚ ≤ right →
  - Q.q0 value ≤ average left right
negativeScalarBelowYoung value left right normExact leftNN rightNN =
  let
    scalar = - Q.q0 value
    localBudget = average left right

    budgetNN : 0ℚ ≤ localBudget
    budgetNN = averageNonnegative left right leftNN rightNN

    scalarSquareBelowProduct : scalar * scalar ≤ left * right
    scalarSquareBelowProduct =
      subst
        (λ selected → scalar * scalar ≤ selected)
        normExact
        (negativeScalarSquareBelowNormSq value)

    scalarSquareBelowBudgetSquare :
      scalar * scalar ≤ localBudget * localBudget
    scalarSquareBelowBudgetSquare =
      ℚP.≤-trans scalarSquareBelowProduct
        (productBelowAverageSquare left right leftNN rightNN)
  in
  caseScalarSign scalar localBudget budgetNN scalarSquareBelowBudgetSquare
  where
  caseScalarSign :
    ∀ scalar localBudget →
    0ℚ ≤ localBudget →
    scalar * scalar ≤ localBudget * localBudget →
    scalar ≤ localBudget
  caseScalarSign scalar localBudget budgetNN squareBound
    with ℚP.≤-total scalar 0ℚ
  ... | inj₁ scalar≤zero = ℚP.≤-trans scalar≤zero budgetNN
  ... | inj₂ zero≤scalar =
    nonnegativeSquareReflectsOrder
      scalar localBudget zero≤scalar budgetNN squareBound

------------------------------------------------------------------------
-- Charges attached to every named placement.
------------------------------------------------------------------------

placementLeftCharge :
  Placement.PlaquetteSecondVariationPlacement4 →
  ℚ → ℚ → ℚ → ℚ → ℚ
placementLeftCharge Placement.secondAt0 n0 n1 n2 n3 = n0
placementLeftCharge Placement.secondAt1 n0 n1 n2 n3 = n1
placementLeftCharge Placement.secondAt2 n0 n1 n2 n3 = n2
placementLeftCharge Placement.secondAt3 n0 n1 n2 n3 = n3
placementLeftCharge (Placement.firstFirst Placement.ordered01) n0 n1 n2 n3 = n0
placementLeftCharge (Placement.firstFirst Placement.ordered10) n0 n1 n2 n3 = n1
placementLeftCharge (Placement.firstFirst Placement.ordered02) n0 n1 n2 n3 = n0
placementLeftCharge (Placement.firstFirst Placement.ordered20) n0 n1 n2 n3 = n2
placementLeftCharge (Placement.firstFirst Placement.ordered03) n0 n1 n2 n3 = n0
placementLeftCharge (Placement.firstFirst Placement.ordered30) n0 n1 n2 n3 = n3
placementLeftCharge (Placement.firstFirst Placement.ordered12) n0 n1 n2 n3 = n1
placementLeftCharge (Placement.firstFirst Placement.ordered21) n0 n1 n2 n3 = n2
placementLeftCharge (Placement.firstFirst Placement.ordered13) n0 n1 n2 n3 = n1
placementLeftCharge (Placement.firstFirst Placement.ordered31) n0 n1 n2 n3 = n3
placementLeftCharge (Placement.firstFirst Placement.ordered23) n0 n1 n2 n3 = n2
placementLeftCharge (Placement.firstFirst Placement.ordered32) n0 n1 n2 n3 = n3

placementRightCharge :
  Placement.PlaquetteSecondVariationPlacement4 →
  ℚ → ℚ → ℚ → ℚ → ℚ
placementRightCharge Placement.secondAt0 n0 n1 n2 n3 = n0
placementRightCharge Placement.secondAt1 n0 n1 n2 n3 = n1
placementRightCharge Placement.secondAt2 n0 n1 n2 n3 = n2
placementRightCharge Placement.secondAt3 n0 n1 n2 n3 = n3
placementRightCharge (Placement.firstFirst Placement.ordered01) n0 n1 n2 n3 = n1
placementRightCharge (Placement.firstFirst Placement.ordered10) n0 n1 n2 n3 = n0
placementRightCharge (Placement.firstFirst Placement.ordered02) n0 n1 n2 n3 = n2
placementRightCharge (Placement.firstFirst Placement.ordered20) n0 n1 n2 n3 = n0
placementRightCharge (Placement.firstFirst Placement.ordered03) n0 n1 n2 n3 = n3
placementRightCharge (Placement.firstFirst Placement.ordered30) n0 n1 n2 n3 = n0
placementRightCharge (Placement.firstFirst Placement.ordered12) n0 n1 n2 n3 = n2
placementRightCharge (Placement.firstFirst Placement.ordered21) n0 n1 n2 n3 = n1
placementRightCharge (Placement.firstFirst Placement.ordered13) n0 n1 n2 n3 = n3
placementRightCharge (Placement.firstFirst Placement.ordered31) n0 n1 n2 n3 = n1
placementRightCharge (Placement.firstFirst Placement.ordered23) n0 n1 n2 n3 = n3
placementRightCharge (Placement.firstFirst Placement.ordered32) n0 n1 n2 n3 = n2

placementNormWeightIsChargeProduct :
  ∀ placement n0 n1 n2 n3 →
  Atom.placementNormWeight placement n0 n1 n2 n3
  ≡ placementLeftCharge placement n0 n1 n2 n3
    * placementRightCharge placement n0 n1 n2 n3
placementNormWeightIsChargeProduct Placement.secondAt0 n0 n1 n2 n3 = refl
placementNormWeightIsChargeProduct Placement.secondAt1 n0 n1 n2 n3 = refl
placementNormWeightIsChargeProduct Placement.secondAt2 n0 n1 n2 n3 = refl
placementNormWeightIsChargeProduct Placement.secondAt3 n0 n1 n2 n3 = refl
placementNormWeightIsChargeProduct (Placement.firstFirst Placement.ordered01) n0 n1 n2 n3 = refl
placementNormWeightIsChargeProduct (Placement.firstFirst Placement.ordered10) n0 n1 n2 n3 = refl
placementNormWeightIsChargeProduct (Placement.firstFirst Placement.ordered02) n0 n1 n2 n3 = refl
placementNormWeightIsChargeProduct (Placement.firstFirst Placement.ordered20) n0 n1 n2 n3 = refl
placementNormWeightIsChargeProduct (Placement.firstFirst Placement.ordered03) n0 n1 n2 n3 = refl
placementNormWeightIsChargeProduct (Placement.firstFirst Placement.ordered30) n0 n1 n2 n3 = refl
placementNormWeightIsChargeProduct (Placement.firstFirst Placement.ordered12) n0 n1 n2 n3 = refl
placementNormWeightIsChargeProduct (Placement.firstFirst Placement.ordered21) n0 n1 n2 n3 = refl
placementNormWeightIsChargeProduct (Placement.firstFirst Placement.ordered13) n0 n1 n2 n3 = refl
placementNormWeightIsChargeProduct (Placement.firstFirst Placement.ordered31) n0 n1 n2 n3 = refl
placementNormWeightIsChargeProduct (Placement.firstFirst Placement.ordered23) n0 n1 n2 n3 = refl
placementNormWeightIsChargeProduct (Placement.firstFirst Placement.ordered32) n0 n1 n2 n3 = refl

placementYoungBudgetIsChargeAverage :
  ∀ placement n0 n1 n2 n3 →
  Budget.placementYoungBudget placement n0 n1 n2 n3
  ≡ average
      (placementLeftCharge placement n0 n1 n2 n3)
      (placementRightCharge placement n0 n1 n2 n3)
placementYoungBudgetIsChargeAverage Placement.secondAt0 n0 n1 n2 n3 = ℚRing.solve-∀ n0
placementYoungBudgetIsChargeAverage Placement.secondAt1 n0 n1 n2 n3 = ℚRing.solve-∀ n1
placementYoungBudgetIsChargeAverage Placement.secondAt2 n0 n1 n2 n3 = ℚRing.solve-∀ n2
placementYoungBudgetIsChargeAverage Placement.secondAt3 n0 n1 n2 n3 = ℚRing.solve-∀ n3
placementYoungBudgetIsChargeAverage (Placement.firstFirst Placement.ordered01) n0 n1 n2 n3 = refl
placementYoungBudgetIsChargeAverage (Placement.firstFirst Placement.ordered10) n0 n1 n2 n3 = refl
placementYoungBudgetIsChargeAverage (Placement.firstFirst Placement.ordered02) n0 n1 n2 n3 = refl
placementYoungBudgetIsChargeAverage (Placement.firstFirst Placement.ordered20) n0 n1 n2 n3 = refl
placementYoungBudgetIsChargeAverage (Placement.firstFirst Placement.ordered03) n0 n1 n2 n3 = refl
placementYoungBudgetIsChargeAverage (Placement.firstFirst Placement.ordered30) n0 n1 n2 n3 = refl
placementYoungBudgetIsChargeAverage (Placement.firstFirst Placement.ordered12) n0 n1 n2 n3 = refl
placementYoungBudgetIsChargeAverage (Placement.firstFirst Placement.ordered21) n0 n1 n2 n3 = refl
placementYoungBudgetIsChargeAverage (Placement.firstFirst Placement.ordered13) n0 n1 n2 n3 = refl
placementYoungBudgetIsChargeAverage (Placement.firstFirst Placement.ordered31) n0 n1 n2 n3 = refl
placementYoungBudgetIsChargeAverage (Placement.firstFirst Placement.ordered23) n0 n1 n2 n3 = refl
placementYoungBudgetIsChargeAverage (Placement.firstFirst Placement.ordered32) n0 n1 n2 n3 = refl

profileInsertionNormNonnegative :
  ∀ jet (profile : Atom.UnitJetNormProfile jet) →
  0ℚ ≤ Atom.insertionNormSq profile
profileInsertionNormNonnegative jet profile =
  subst
    (λ selected → 0ℚ ≤ selected)
    (Atom.firstNormSqExact profile)
    (Norm.normSqNonnegative (Q.factorFirst jet))

placementChargeNonnegative :
  ∀ placement jet0 jet1 jet2 jet3
    (profile0 : Atom.UnitJetNormProfile jet0)
    (profile1 : Atom.UnitJetNormProfile jet1)
    (profile2 : Atom.UnitJetNormProfile jet2)
    (profile3 : Atom.UnitJetNormProfile jet3) →
  0ℚ ≤ placementLeftCharge placement
      (Atom.insertionNormSq profile0) (Atom.insertionNormSq profile1)
      (Atom.insertionNormSq profile2) (Atom.insertionNormSq profile3)
  × 0ℚ ≤ placementRightCharge placement
      (Atom.insertionNormSq profile0) (Atom.insertionNormSq profile1)
      (Atom.insertionNormSq profile2) (Atom.insertionNormSq profile3)
placementChargeNonnegative Placement.secondAt0 jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet0 p0 , profileInsertionNormNonnegative jet0 p0
placementChargeNonnegative Placement.secondAt1 jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet1 p1 , profileInsertionNormNonnegative jet1 p1
placementChargeNonnegative Placement.secondAt2 jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet2 p2 , profileInsertionNormNonnegative jet2 p2
placementChargeNonnegative Placement.secondAt3 jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet3 p3 , profileInsertionNormNonnegative jet3 p3
placementChargeNonnegative (Placement.firstFirst Placement.ordered01) jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet0 p0 , profileInsertionNormNonnegative jet1 p1
placementChargeNonnegative (Placement.firstFirst Placement.ordered10) jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet1 p1 , profileInsertionNormNonnegative jet0 p0
placementChargeNonnegative (Placement.firstFirst Placement.ordered02) jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet0 p0 , profileInsertionNormNonnegative jet2 p2
placementChargeNonnegative (Placement.firstFirst Placement.ordered20) jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet2 p2 , profileInsertionNormNonnegative jet0 p0
placementChargeNonnegative (Placement.firstFirst Placement.ordered03) jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet0 p0 , profileInsertionNormNonnegative jet3 p3
placementChargeNonnegative (Placement.firstFirst Placement.ordered30) jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet3 p3 , profileInsertionNormNonnegative jet0 p0
placementChargeNonnegative (Placement.firstFirst Placement.ordered12) jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet1 p1 , profileInsertionNormNonnegative jet2 p2
placementChargeNonnegative (Placement.firstFirst Placement.ordered21) jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet2 p2 , profileInsertionNormNonnegative jet1 p1
placementChargeNonnegative (Placement.firstFirst Placement.ordered13) jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet1 p1 , profileInsertionNormNonnegative jet3 p3
placementChargeNonnegative (Placement.firstFirst Placement.ordered31) jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet3 p3 , profileInsertionNormNonnegative jet1 p1
placementChargeNonnegative (Placement.firstFirst Placement.ordered23) jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet2 p2 , profileInsertionNormNonnegative jet3 p3
placementChargeNonnegative (Placement.firstFirst Placement.ordered32) jet0 jet1 jet2 jet3 p0 p1 p2 p3 =
  profileInsertionNormNonnegative jet3 p3 , profileInsertionNormNonnegative jet2 p2

placementWilsonScalarBelowYoungBudget :
  ∀ jet0 jet1 jet2 jet3
    (profile0 : Atom.UnitJetNormProfile jet0)
    (profile1 : Atom.UnitJetNormProfile jet1)
    (profile2 : Atom.UnitJetNormProfile jet2)
    (profile3 : Atom.UnitJetNormProfile jet3)
    placement →
  - Q.q0 (Atom.placementAtom jet0 jet1 jet2 jet3 placement)
  ≤ Budget.placementYoungBudget placement
      (Atom.insertionNormSq profile0) (Atom.insertionNormSq profile1)
      (Atom.insertionNormSq profile2) (Atom.insertionNormSq profile3)
placementWilsonScalarBelowYoungBudget
    jet0 jet1 jet2 jet3 profile0 profile1 profile2 profile3 placement =
  let
    n0 = Atom.insertionNormSq profile0
    n1 = Atom.insertionNormSq profile1
    n2 = Atom.insertionNormSq profile2
    n3 = Atom.insertionNormSq profile3
    left = placementLeftCharge placement n0 n1 n2 n3
    right = placementRightCharge placement n0 n1 n2 n3
    atom = Atom.placementAtom jet0 jet1 jet2 jet3 placement

    atomNormProduct : Norm.normSq atom ≡ left * right
    atomNormProduct =
      trans
        (Atom.placementAtomNormSqExact
          jet0 jet1 jet2 jet3 profile0 profile1 profile2 profile3 placement)
        (placementNormWeightIsChargeProduct placement n0 n1 n2 n3)

    chargesNN =
      placementChargeNonnegative
        placement jet0 jet1 jet2 jet3 profile0 profile1 profile2 profile3

    scalarBelowAverage : - Q.q0 atom ≤ average left right
    scalarBelowAverage =
      negativeScalarBelowYoung atom left right atomNormProduct
        (Data.Product.Base.proj₁ chargesNN)
        (Data.Product.Base.proj₂ chargesNN)
  in
  subst
    (λ selected → - Q.q0 atom ≤ selected)
    (sym (placementYoungBudgetIsChargeAverage placement n0 n1 n2 n3))
    scalarBelowAverage

sumPlacementScalars :
  Q.QuaternionFactorJet → Q.QuaternionFactorJet →
  Q.QuaternionFactorJet → Q.QuaternionFactorJet →
  List Placement.PlaquetteSecondVariationPlacement4 → ℚ
sumPlacementScalars jet0 jet1 jet2 jet3 [] = 0ℚ
sumPlacementScalars jet0 jet1 jet2 jet3 (placement ∷ placements) =
  - Q.q0 (Atom.placementAtom jet0 jet1 jet2 jet3 placement)
    + sumPlacementScalars jet0 jet1 jet2 jet3 placements

sumPlacementBudgets :
  ℚ → ℚ → ℚ → ℚ →
  List Placement.PlaquetteSecondVariationPlacement4 → ℚ
sumPlacementBudgets n0 n1 n2 n3 [] = 0ℚ
sumPlacementBudgets n0 n1 n2 n3 (placement ∷ placements) =
  Budget.placementYoungBudget placement n0 n1 n2 n3
    + sumPlacementBudgets n0 n1 n2 n3 placements

placementScalarSumBelowBudget :
  ∀ jet0 jet1 jet2 jet3
    (profile0 : Atom.UnitJetNormProfile jet0)
    (profile1 : Atom.UnitJetNormProfile jet1)
    (profile2 : Atom.UnitJetNormProfile jet2)
    (profile3 : Atom.UnitJetNormProfile jet3)
    placements →
  sumPlacementScalars jet0 jet1 jet2 jet3 placements
  ≤ sumPlacementBudgets
      (Atom.insertionNormSq profile0) (Atom.insertionNormSq profile1)
      (Atom.insertionNormSq profile2) (Atom.insertionNormSq profile3)
      placements
placementScalarSumBelowBudget
    jet0 jet1 jet2 jet3 profile0 profile1 profile2 profile3 [] =
  ℚP.≤-refl
placementScalarSumBelowBudget
    jet0 jet1 jet2 jet3 profile0 profile1 profile2 profile3
    (placement ∷ placements) =
  ℚP.+-mono-≤
    (placementWilsonScalarBelowYoungBudget
      jet0 jet1 jet2 jet3 profile0 profile1 profile2 profile3 placement)
    (placementScalarSumBelowBudget
      jet0 jet1 jet2 jet3 profile0 profile1 profile2 profile3 placements)

recursiveWilsonScalarSumBelowFourCharges :
  ∀ jet0 jet1 jet2 jet3
    (profile0 : Atom.UnitJetNormProfile jet0)
    (profile1 : Atom.UnitJetNormProfile jet1)
    (profile2 : Atom.UnitJetNormProfile jet2)
    (profile3 : Atom.UnitJetNormProfile jet3) →
  sumPlacementScalars
    jet0 jet1 jet2 jet3 Generated.recursivePlacementOrder4
  ≤ (+ 4 / 1)
      * Budget.localInsertionCharge
          (Atom.insertionNormSq profile0) (Atom.insertionNormSq profile1)
          (Atom.insertionNormSq profile2) (Atom.insertionNormSq profile3)
recursiveWilsonScalarSumBelowFourCharges
    jet0 jet1 jet2 jet3 profile0 profile1 profile2 profile3 =
  let
    base = placementScalarSumBelowBudget
      jet0 jet1 jet2 jet3 profile0 profile1 profile2 profile3
      Generated.recursivePlacementOrder4
  in
  subst
    (λ selected →
      sumPlacementScalars
        jet0 jet1 jet2 jet3 Generated.recursivePlacementOrder4
      ≤ selected)
    (Budget.recursiveSixteenPlacementBudgetExact
      (Atom.insertionNormSq profile0) (Atom.insertionNormSq profile1)
      (Atom.insertionNormSq profile2) (Atom.insertionNormSq profile3))
    base
