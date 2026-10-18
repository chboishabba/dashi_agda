{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact where

------------------------------------------------------------------------
-- SCALAR-GENERIC CYLINDER EXPECTATION LIMIT
--
-- Same theorem as the older rational-only owner, but on the actual scalar
-- carrier used by the physical finite/Haar lane.  No rationalization of the
-- continuum measure is required.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record ScalarCylinderLimitAlgebra (Scalar : Set) : Set₁ where
  field
    zero one : Scalar
    add multiply : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    Converges : (Nat → Scalar) → Scalar → Set

    convergenceUnique :
      ∀ sequence left right →
      Converges sequence left →
      Converges sequence right →
      left ≡ right

    convergencePointwiseCongruent :
      ∀ left right target →
      (∀ n → left n ≡ right n) →
      Converges right target →
      Converges left target

    constantConverges :
      ∀ value → Converges (λ _ → value) value

    addConverges :
      ∀ left right leftLimit rightLimit →
      Converges left leftLimit →
      Converges right rightLimit →
      Converges
        (λ n → add (left n) (right n))
        (add leftLimit rightLimit)

    multiplyConstantConverges :
      ∀ scalar sequence target →
      Converges sequence target →
      Converges
        (λ n → multiply scalar (sequence n))
        (multiply scalar target)

    nonnegativeClosedUnderLimit :
      ∀ sequence target →
      Converges sequence target →
      (∀ n → LessEqual zero (sequence n)) →
      LessEqual zero target

open ScalarCylinderLimitAlgebra public

record ScalarCylinderExpectationLimitData
    (Observable Scalar : Set)
    (algebra : ScalarCylinderLimitAlgebra Scalar) : Set₁ where
  field
    zeroObservable oneObservable : Observable
    addObservable : Observable → Observable → Observable
    scaleObservable : Scalar → Observable → Observable
    Nonnegative : Observable → Set

    finiteExpectation : Nat → Observable → Scalar
    limitExpectation : Observable → Scalar

    finiteZero : ∀ n →
      finiteExpectation n zeroObservable ≡ zero algebra

    finiteOne : ∀ n →
      finiteExpectation n oneObservable ≡ one algebra

    finiteAdd : ∀ n left right →
      finiteExpectation n (addObservable left right)
      ≡ add algebra
          (finiteExpectation n left)
          (finiteExpectation n right)

    finiteScale : ∀ n scalar observable →
      finiteExpectation n (scaleObservable scalar observable)
      ≡ multiply algebra scalar (finiteExpectation n observable)

    finitePositive : ∀ n observable →
      Nonnegative observable →
      LessEqual algebra
        (zero algebra)
        (finiteExpectation n observable)

    selectedConverges : ∀ observable →
      Converges algebra
        (λ n → finiteExpectation n observable)
        (limitExpectation observable)

open ScalarCylinderExpectationLimitData public

limitZero :
  ∀ {Observable Scalar algebra}
    (dataSet :
      ScalarCylinderExpectationLimitData
        Observable Scalar algebra) →
  limitExpectation dataSet (zeroObservable dataSet)
  ≡ zero algebra
limitZero {algebra = algebra} dataSet =
  convergenceUnique algebra
    (λ n → finiteExpectation dataSet n (zeroObservable dataSet))
    (limitExpectation dataSet (zeroObservable dataSet))
    (zero algebra)
    (selectedConverges dataSet (zeroObservable dataSet))
    (convergencePointwiseCongruent algebra
      (λ n → finiteExpectation dataSet n (zeroObservable dataSet))
      (λ _ → zero algebra)
      (zero algebra)
      (finiteZero dataSet)
      (constantConverges algebra (zero algebra)))

limitOne :
  ∀ {Observable Scalar algebra}
    (dataSet :
      ScalarCylinderExpectationLimitData
        Observable Scalar algebra) →
  limitExpectation dataSet (oneObservable dataSet)
  ≡ one algebra
limitOne {algebra = algebra} dataSet =
  convergenceUnique algebra
    (λ n → finiteExpectation dataSet n (oneObservable dataSet))
    (limitExpectation dataSet (oneObservable dataSet))
    (one algebra)
    (selectedConverges dataSet (oneObservable dataSet))
    (convergencePointwiseCongruent algebra
      (λ n → finiteExpectation dataSet n (oneObservable dataSet))
      (λ _ → one algebra)
      (one algebra)
      (finiteOne dataSet)
      (constantConverges algebra (one algebra)))

limitAdd :
  ∀ {Observable Scalar algebra}
    (dataSet :
      ScalarCylinderExpectationLimitData
        Observable Scalar algebra)
    left right →
  limitExpectation dataSet (addObservable dataSet left right)
  ≡
  add algebra
    (limitExpectation dataSet left)
    (limitExpectation dataSet right)
limitAdd {algebra = algebra} dataSet left right =
  convergenceUnique algebra
    (λ n → finiteExpectation dataSet n
      (addObservable dataSet left right))
    (limitExpectation dataSet
      (addObservable dataSet left right))
    (add algebra
      (limitExpectation dataSet left)
      (limitExpectation dataSet right))
    (selectedConverges dataSet
      (addObservable dataSet left right))
    (convergencePointwiseCongruent algebra
      (λ n → finiteExpectation dataSet n
        (addObservable dataSet left right))
      (λ n →
        add algebra
          (finiteExpectation dataSet n left)
          (finiteExpectation dataSet n right))
      (add algebra
        (limitExpectation dataSet left)
        (limitExpectation dataSet right))
      (λ n → finiteAdd dataSet n left right)
      (addConverges algebra
        (λ n → finiteExpectation dataSet n left)
        (λ n → finiteExpectation dataSet n right)
        (limitExpectation dataSet left)
        (limitExpectation dataSet right)
        (selectedConverges dataSet left)
        (selectedConverges dataSet right)))

limitScale :
  ∀ {Observable Scalar algebra}
    (dataSet :
      ScalarCylinderExpectationLimitData
        Observable Scalar algebra)
    scalar observable →
  limitExpectation dataSet
    (scaleObservable dataSet scalar observable)
  ≡
  multiply algebra scalar
    (limitExpectation dataSet observable)
limitScale {algebra = algebra} dataSet scalar observable =
  convergenceUnique algebra
    (λ n → finiteExpectation dataSet n
      (scaleObservable dataSet scalar observable))
    (limitExpectation dataSet
      (scaleObservable dataSet scalar observable))
    (multiply algebra scalar
      (limitExpectation dataSet observable))
    (selectedConverges dataSet
      (scaleObservable dataSet scalar observable))
    (convergencePointwiseCongruent algebra
      (λ n → finiteExpectation dataSet n
        (scaleObservable dataSet scalar observable))
      (λ n →
        multiply algebra scalar
          (finiteExpectation dataSet n observable))
      (multiply algebra scalar
        (limitExpectation dataSet observable))
      (λ n → finiteScale dataSet n scalar observable)
      (multiplyConstantConverges algebra scalar
        (λ n → finiteExpectation dataSet n observable)
        (limitExpectation dataSet observable)
        (selectedConverges dataSet observable)))

limitPositive :
  ∀ {Observable Scalar algebra}
    (dataSet :
      ScalarCylinderExpectationLimitData
        Observable Scalar algebra)
    observable →
  Nonnegative dataSet observable →
  LessEqual algebra
    (zero algebra)
    (limitExpectation dataSet observable)
limitPositive {algebra = algebra} dataSet observable nonnegative =
  nonnegativeClosedUnderLimit algebra
    (λ n → finiteExpectation dataSet n observable)
    (limitExpectation dataSet observable)
    (selectedConverges dataSet observable)
    (λ n → finitePositive dataSet n observable nonnegative)

scalarCylinderLimitCompilerLevel : ProofLevel
scalarCylinderLimitCompilerLevel = machineChecked
