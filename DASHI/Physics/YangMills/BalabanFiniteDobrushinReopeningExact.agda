{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteDobrushinReopeningExact where

------------------------------------------------------------------------
-- FINITE DOBRUSHIN / OSCILLATION BRIDGE
--
-- For two rows p,q on one finite carrier and an observable |f| <= A,
--
--   | sum_y p(y) f(y) - sum_y q(y) f(y) |
--      <= A sum_y |p(y)-q(y)|.
--
-- Thus an L1 row-difference estimate for the actual finite reopening kernel is
-- exactly the good-region influence estimate needed to localise transported
-- observables.  This theorem is finite rational algebra only; no measure or
-- functional-inequality authority is imported.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; ∣_∣; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact as Bound

sumAbsUpper :
  ∀ {A : Set} (values : List A) (term : A → ℚ) →
  ∣ Sums.sumRational values term ∣
  ≤ Sums.sumRational values (λ value → ∣ term value ∣)
sumAbsUpper [] term = ℚP.≤-refl
sumAbsUpper (value ∷ values) term =
  ℚP.≤-trans
    (ℚP.∣p+q∣≤∣p∣+∣q∣
      (term value)
      (Sums.sumRational values term))
    (ℚP.+-mono-≤
      ℚP.≤-refl
      (sumAbsUpper values term))

sumMono :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≤ right value) →
  Sums.sumRational values left ≤ Sums.sumRational values right
sumMono [] left right pointwise = ℚP.≤-refl
sumMono (value ∷ values) left right pointwise =
  ℚP.+-mono-≤
    (pointwise value)
    (sumMono values left right pointwise)

weightedDifferenceSumExact :
  ∀ {State : Set}
    (states : List State)
    (leftWeight rightWeight observable : State → ℚ) →
  Sums.sumRational states
      (λ state → leftWeight state * observable state)
  - Sums.sumRational states
      (λ state → rightWeight state * observable state)
  ≡ Sums.sumRational states
      (λ state →
        (leftWeight state - rightWeight state) * observable state)
weightedDifferenceSumExact [] leftWeight rightWeight observable =
  ℚRing.solve []
weightedDifferenceSumExact
    (state ∷ states) leftWeight rightWeight observable
    rewrite weightedDifferenceSumExact
      states leftWeight rightWeight observable =
  ℚRing.solve-∀
    (leftWeight state)
    (rightWeight state)
    (observable state)
    (Sums.sumRational states
      (λ selected → leftWeight selected * observable selected))
    (Sums.sumRational states
      (λ selected → rightWeight selected * observable selected))

rowL1Difference :
  ∀ {State : Set} →
  List State → (State → ℚ) → (State → ℚ) → ℚ
rowL1Difference states leftWeight rightWeight =
  Sums.sumRational states
    (λ state → ∣ leftWeight state - rightWeight state ∣)

rowL1DifferenceNonnegative :
  ∀ {State : Set} states leftWeight rightWeight →
  0ℚ ≤ rowL1Difference {State} states leftWeight rightWeight
rowL1DifferenceNonnegative [] leftWeight rightWeight = ℚP.≤-refl
rowL1DifferenceNonnegative (state ∷ states) leftWeight rightWeight =
  subst
    (λ lower →
      lower ≤
        ∣ leftWeight state - rightWeight state ∣
        + rowL1Difference states leftWeight rightWeight)
    (sym (ℚP.+-identityˡ 0ℚ))
    (ℚP.+-mono-≤
      (ℚP.0≤∣p∣ (leftWeight state - rightWeight state))
      (rowL1DifferenceNonnegative states leftWeight rightWeight))

finiteExpectationRowDifferenceBound :
  ∀ {State : Set}
    (states : List State)
    (leftWeight rightWeight observable : State → ℚ)
    majorant →
  0ℚ ≤ majorant →
  (∀ state → ∣ observable state ∣ ≤ majorant) →
  ∣
    Sums.sumRational states
      (λ state → leftWeight state * observable state)
    -
    Sums.sumRational states
      (λ state → rightWeight state * observable state)
  ∣
  ≤ majorant * rowL1Difference states leftWeight rightWeight
finiteExpectationRowDifferenceBound
    states leftWeight rightWeight observable majorant majorantNN bounded =
  let
    exact :
      Sums.sumRational states
        (λ state → leftWeight state * observable state)
      -
      Sums.sumRational states
        (λ state → rightWeight state * observable state)
      ≡
      Sums.sumRational states
        (λ state →
          (leftWeight state - rightWeight state) * observable state)
    exact =
      weightedDifferenceSumExact
        states leftWeight rightWeight observable

    triangle :
      ∣ Sums.sumRational states
          (λ state →
            (leftWeight state - rightWeight state) * observable state) ∣
      ≤
      Sums.sumRational states
        (λ state →
          ∣ (leftWeight state - rightWeight state) * observable state ∣)
    triangle =
      sumAbsUpper states
        (λ state →
          (leftWeight state - rightWeight state) * observable state)

    pointwise :
      Sums.sumRational states
        (λ state →
          ∣ (leftWeight state - rightWeight state) * observable state ∣)
      ≤
      Sums.sumRational states
        (λ state →
          majorant * ∣ leftWeight state - rightWeight state ∣)
    pointwise =
      sumMono states _ _
        (λ state →
          subst
            (λ upper →
              ∣
                (leftWeight state - rightWeight state)
                * observable state
              ∣
              ≤ upper)
            (ℚP.*-comm
              ∣ leftWeight state - rightWeight state ∣
              majorant)
            (Bound.absoluteProductBound
              {left = leftWeight state - rightWeight state}
              {right = observable state}
              {leftBound = ∣ leftWeight state - rightWeight state ∣}
              {rightBound = majorant}
              ℚP.≤-refl
              (bounded state)
              (ℚP.0≤∣p∣ (leftWeight state - rightWeight state))
              majorantNN))

    factor :
      Sums.sumRational states
        (λ state →
          majorant * ∣ leftWeight state - rightWeight state ∣)
      ≡ majorant * rowL1Difference states leftWeight rightWeight
    factor =
      Sums.sumRationalScale
        majorant states
        (λ state → ∣ leftWeight state - rightWeight state ∣)
  in
  subst
    (λ lower →
      ∣ lower ∣
      ≤ majorant * rowL1Difference states leftWeight rightWeight)
    (sym exact)
    (ℚP.≤-trans triangle
      (subst
        (λ upper →
          Sums.sumRational states
            (λ state →
              ∣
                (leftWeight state - rightWeight state)
                * observable state
              ∣)
          ≤ upper)
        factor
        pointwise))

record FiniteDobrushinKernel (Fine Coarse : Set) : Set₁ where
  field
    fineStates : List Fine
    kernel : Coarse → Fine → ℚ

open FiniteDobrushinKernel public

transport :
  ∀ {Fine Coarse} →
  FiniteDobrushinKernel Fine Coarse →
  (Fine → ℚ) → Coarse → ℚ
transport dataSet observable coarse =
  Sums.sumRational (fineStates dataSet)
    (λ fine → kernel dataSet coarse fine * observable fine)

rowDistance :
  ∀ {Fine Coarse} →
  FiniteDobrushinKernel Fine Coarse →
  Coarse → Coarse → ℚ
rowDistance dataSet left right =
  rowL1Difference
    (fineStates dataSet)
    (kernel dataSet left)
    (kernel dataSet right)

transportOscillationBelowRowDistance :
  ∀ {Fine Coarse}
    (dataSet : FiniteDobrushinKernel Fine Coarse)
    (observable : Fine → ℚ)
    majorant →
  0ℚ ≤ majorant →
  (∀ fine → ∣ observable fine ∣ ≤ majorant) →
  ∀ left right →
  ∣ transport dataSet observable left
    - transport dataSet observable right ∣
  ≤ majorant * rowDistance dataSet left right
transportOscillationBelowRowDistance dataSet observable majorant majorantNN bounded
    left right =
  finiteExpectationRowDifferenceBound
    (fineStates dataSet)
    (kernel dataSet left)
    (kernel dataSet right)
    observable
    majorant
    majorantNN
    bounded

record DobrushinRowEnvelope
    {Fine Coarse : Set}
    (dataSet : FiniteDobrushinKernel Fine Coarse)
    (Distance : Coarse → Coarse → Set) : Set₁ where
  field
    envelope : ∀ {left right} → Distance left right → ℚ
    rowDistanceBelowEnvelope : ∀ {left right}
      (distance : Distance left right) →
      rowDistance dataSet left right ≤ envelope distance

open DobrushinRowEnvelope public

transportOscillationBelowEnvelope :
  ∀ {Fine Coarse}
    {dataSet : FiniteDobrushinKernel Fine Coarse}
    {Distance : Coarse → Coarse → Set}
    (rowEnvelope : DobrushinRowEnvelope dataSet Distance)
    (observable : Fine → ℚ)
    majorant →
  0ℚ ≤ majorant →
  (∀ fine → ∣ observable fine ∣ ≤ majorant) →
  ∀ {left right} (distance : Distance left right) →
  ∣ transport dataSet observable left
    - transport dataSet observable right ∣
  ≤ majorant * envelope rowEnvelope distance
transportOscillationBelowEnvelope
    {dataSet = dataSet}
    rowEnvelope observable majorant majorantNN bounded distance =
  let
    base =
      transportOscillationBelowRowDistance
        dataSet observable majorant majorantNN bounded _ _

    rowBound = rowDistanceBelowEnvelope rowEnvelope distance

    instance
      majorantNonnegative : NonNegative majorant
      majorantNonnegative = nonNegative majorantNN
  in
  ℚP.≤-trans base
    (ℚP.*-monoˡ-≤-nonNeg majorant rowBound)

finiteDobrushinExpectationDifferenceLevel : ProofLevel
finiteDobrushinExpectationDifferenceLevel = machineChecked

finiteDobrushinOscillationTransportLevel : ProofLevel
finiteDobrushinOscillationTransportLevel = machineChecked
