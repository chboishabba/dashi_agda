{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCylinderExpectationLimitMeasureExact where

------------------------------------------------------------------------
-- A: FINITE CYLINDER EXPECTATIONS -> POSITIVE NORMALIZED LIMIT FUNCTIONAL
--    -> CONTINUUM MEASURE
--
-- The algebraic part is proved here.  The only imported functional-analysis
-- boundary is the standard measure-representation theorem on the selected
-- cylinder algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record CylinderExpectationLimitData (Observable : Set) : Set₁ where
  field
    zero one : Observable
    add : Observable → Observable → Observable
    scale : ℚ → Observable → Observable
    Nonnegative : Observable → Set

    finiteExpectation : Nat → Observable → ℚ
    limitExpectation : Observable → ℚ

    Converges : (Nat → ℚ) → ℚ → Set

    convergenceUnique :
      ∀ sequence left right →
      Converges sequence left → Converges sequence right → left ≡ right

    convergencePointwiseCongruent :
      ∀ left right target →
      (∀ n → left n ≡ right n) →
      Converges right target →
      Converges left target

    constantConverges : ∀ value →
      Converges (λ _ → value) value

    addConverges :
      ∀ left right leftLimit rightLimit →
      Converges left leftLimit →
      Converges right rightLimit →
      Converges (λ n → left n + right n) (leftLimit + rightLimit)

    scaleConverges :
      ∀ scalar sequence target →
      Converges sequence target →
      Converges (λ n → scalar * sequence n) (scalar * target)

    nonnegativeClosedUnderLimit :
      ∀ sequence target →
      Converges sequence target →
      (∀ n → 0ℚ ≤ sequence n) →
      0ℚ ≤ target

    finiteZero : ∀ n → finiteExpectation n zero ≡ 0ℚ
    finiteOne : ∀ n → finiteExpectation n one ≡ 1ℚ
    finiteAdd : ∀ n left right →
      finiteExpectation n (add left right)
      ≡ finiteExpectation n left + finiteExpectation n right
    finiteScale : ∀ n scalar observable →
      finiteExpectation n (scale scalar observable)
      ≡ scalar * finiteExpectation n observable
    finitePositive : ∀ n observable →
      Nonnegative observable →
      0ℚ ≤ finiteExpectation n observable

    selectedConverges : ∀ observable →
      Converges
        (λ n → finiteExpectation n observable)
        (limitExpectation observable)

open CylinderExpectationLimitData public

limitZero :
  ∀ {Observable} (dataSet : CylinderExpectationLimitData Observable) →
  limitExpectation dataSet (zero dataSet) ≡ 0ℚ
limitZero dataSet =
  convergenceUnique dataSet
    (λ n → finiteExpectation dataSet n (zero dataSet))
    (limitExpectation dataSet (zero dataSet))
    0ℚ
    (selectedConverges dataSet (zero dataSet))
    (convergencePointwiseCongruent dataSet
      (λ n → finiteExpectation dataSet n (zero dataSet))
      (λ _ → 0ℚ)
      0ℚ
      (finiteZero dataSet)
      (constantConverges dataSet 0ℚ))

limitOne :
  ∀ {Observable} (dataSet : CylinderExpectationLimitData Observable) →
  limitExpectation dataSet (one dataSet) ≡ 1ℚ
limitOne dataSet =
  convergenceUnique dataSet
    (λ n → finiteExpectation dataSet n (one dataSet))
    (limitExpectation dataSet (one dataSet))
    1ℚ
    (selectedConverges dataSet (one dataSet))
    (convergencePointwiseCongruent dataSet
      (λ n → finiteExpectation dataSet n (one dataSet))
      (λ _ → 1ℚ)
      1ℚ
      (finiteOne dataSet)
      (constantConverges dataSet 1ℚ))

limitAdd :
  ∀ {Observable} (dataSet : CylinderExpectationLimitData Observable)
    left right →
  limitExpectation dataSet (add dataSet left right)
  ≡ limitExpectation dataSet left + limitExpectation dataSet right
limitAdd dataSet left right =
  convergenceUnique dataSet
    (λ n → finiteExpectation dataSet n (add dataSet left right))
    (limitExpectation dataSet (add dataSet left right))
    (limitExpectation dataSet left + limitExpectation dataSet right)
    (selectedConverges dataSet (add dataSet left right))
    (convergencePointwiseCongruent dataSet
      (λ n → finiteExpectation dataSet n (add dataSet left right))
      (λ n →
        finiteExpectation dataSet n left
        + finiteExpectation dataSet n right)
      (limitExpectation dataSet left + limitExpectation dataSet right)
      (λ n → finiteAdd dataSet n left right)
      (addConverges dataSet
        (λ n → finiteExpectation dataSet n left)
        (λ n → finiteExpectation dataSet n right)
        (limitExpectation dataSet left)
        (limitExpectation dataSet right)
        (selectedConverges dataSet left)
        (selectedConverges dataSet right)))

limitScale :
  ∀ {Observable} (dataSet : CylinderExpectationLimitData Observable)
    scalar observable →
  limitExpectation dataSet (scale dataSet scalar observable)
  ≡ scalar * limitExpectation dataSet observable
limitScale dataSet scalar observable =
  convergenceUnique dataSet
    (λ n → finiteExpectation dataSet n (scale dataSet scalar observable))
    (limitExpectation dataSet (scale dataSet scalar observable))
    (scalar * limitExpectation dataSet observable)
    (selectedConverges dataSet (scale dataSet scalar observable))
    (convergencePointwiseCongruent dataSet
      (λ n → finiteExpectation dataSet n (scale dataSet scalar observable))
      (λ n → scalar * finiteExpectation dataSet n observable)
      (scalar * limitExpectation dataSet observable)
      (λ n → finiteScale dataSet n scalar observable)
      (scaleConverges dataSet scalar
        (λ n → finiteExpectation dataSet n observable)
        (limitExpectation dataSet observable)
        (selectedConverges dataSet observable)))

limitPositive :
  ∀ {Observable} (dataSet : CylinderExpectationLimitData Observable)
    observable →
  Nonnegative dataSet observable →
  0ℚ ≤ limitExpectation dataSet observable
limitPositive dataSet observable nonnegative =
  nonnegativeClosedUnderLimit dataSet
    (λ n → finiteExpectation dataSet n observable)
    (limitExpectation dataSet observable)
    (selectedConverges dataSet observable)
    (λ n → finitePositive dataSet n observable nonnegative)

record CylinderMeasureRepresentation
    (Observable Measure : Set)
    (dataSet : CylinderExpectationLimitData Observable) : Set₁ where
  field
    measure : Measure
    expectation : Measure → Observable → ℚ
    represented : ∀ observable →
      expectation measure observable
      ≡ limitExpectation dataSet observable

open CylinderMeasureRepresentation public

record CylinderMeasureRepresentationAuthority
    (Observable Measure : Set) : Set₁ where
  field
    represent :
      (dataSet : CylinderExpectationLimitData Observable) →
      CylinderMeasureRepresentation Observable Measure dataSet

open CylinderMeasureRepresentationAuthority public

limitFunctionalAlgebraLevel : ProofLevel
limitFunctionalAlgebraLevel = machineChecked

cylinderMeasureRepresentationAuthorityLevel : ProofLevel
cylinderMeasureRepresentationAuthorityLevel = standardImported

representedMeasureExpectationIsLimit :
  ∀ {Observable Measure}
    {dataSet : CylinderExpectationLimitData Observable}
    (authority : CylinderMeasureRepresentationAuthority Observable Measure)
    observable →
  let represented = represent authority dataSet in
  expectation represented (measure represented) observable
  ≡ limitExpectation dataSet observable
representedMeasureExpectationIsLimit authority observable =
  represented (represent authority _) observable

representedLimitMeasureNormalized :
  ∀ {Observable Measure}
    {dataSet : CylinderExpectationLimitData Observable}
    (authority : CylinderMeasureRepresentationAuthority Observable Measure) →
  let representedMeasure = represent authority dataSet in
  expectation representedMeasure
    (measure representedMeasure)
    (one dataSet)
  ≡ 1ℚ
representedLimitMeasureNormalized {dataSet = dataSet} authority =
  trans
    (represented (represent authority dataSet) (one dataSet))
    (limitOne dataSet)

representedLimitMeasurePositive :
  ∀ {Observable Measure}
    {dataSet : CylinderExpectationLimitData Observable}
    (authority : CylinderMeasureRepresentationAuthority Observable Measure)
    observable →
  Nonnegative dataSet observable →
  0ℚ ≤
    let representedMeasure = represent authority dataSet in
    expectation representedMeasure
      (measure representedMeasure)
      observable
representedLimitMeasurePositive {dataSet = dataSet} authority observable nonnegative =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (represented (represent authority dataSet) observable))
    (limitPositive dataSet observable nonnegative)

representedCylinderMeasureCompilerLevel : ProofLevel
representedCylinderMeasureCompilerLevel = machineChecked
