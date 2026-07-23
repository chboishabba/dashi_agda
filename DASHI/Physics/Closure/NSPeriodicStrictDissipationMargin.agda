module DASHI.Physics.Closure.NSPeriodicStrictDissipationMargin where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact scalar bookkeeping for the strict Wall-I/Wall-II margin.
--
-- The three nonlinear regions are bounded separately.  If the viscosity
-- budget is exactly their three payments plus a named strict margin, then
-- the complete nonlinear contribution plus that margin is below viscosity.
-- No subtraction, hidden slack variable, or informal "theta < 1" step is
-- used by the assembly theorem.
------------------------------------------------------------------------

record PeriodicStrictDissipationMarginInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    nearTerm farLowTerm farHighTerm : Scalar A
    nearPayment farLowPayment farHighPayment : Scalar A
    strictMargin viscosityBudget : Scalar A

    nearTermBound : _≤_ A nearTerm nearPayment
    farLowTermBound : _≤_ A farLowTerm farLowPayment
    farHighTermBound : _≤_ A farHighTerm farHighPayment

    viscositySplitsPaymentsAndMargin :
      viscosityBudget ≡
      _+_ A
        (_+_ A
          (_+_ A nearPayment farLowPayment)
          farHighPayment)
        strictMargin

    strictMarginNonnegative : _≤_ A (zero A) strictMargin

    StrictMarginPositive : Set
    strictMarginPositive : StrictMarginPositive

open PeriodicStrictDissipationMarginInputs public

addZeroRightForMargin :
  (A : AbsorptionArithmetic) →
  (a : Scalar A) →
  _+_ A a (zero A) ≡ a
addZeroRightForMargin A a =
  trans
    (addCommutative A a (zero A))
    (addZeroLeft A a)

periodicNonlinearComponentsBelowPayments :
  ∀ {A : AbsorptionArithmetic} →
  (M : PeriodicStrictDissipationMarginInputs A) →
  _≤_ A
    (_+_ A
      (_+_ A (nearTerm M) (farLowTerm M))
      (farHighTerm M))
    (_+_ A
      (_+_ A (nearPayment M) (farLowPayment M))
      (farHighPayment M))
periodicNonlinearComponentsBelowPayments {A = A} M =
  ≤-trans A
    (additionMonotoneRight A nearLow)
    (additionMonotoneLeft A (farHighTermBound M))
  where
  nearStep :
    _≤_ A
      (_+_ A (nearTerm M) (farLowTerm M))
      (_+_ A (nearPayment M) (farLowTerm M))
  nearStep = additionMonotoneRight A (nearTermBound M)

  lowStep :
    _≤_ A
      (_+_ A (nearPayment M) (farLowTerm M))
      (_+_ A (nearPayment M) (farLowPayment M))
  lowStep = additionMonotoneLeft A (farLowTermBound M)

  nearLow :
    _≤_ A
      (_+_ A (nearTerm M) (farLowTerm M))
      (_+_ A (nearPayment M) (farLowPayment M))
  nearLow = ≤-trans A nearStep lowStep

periodicNonlinearPlusStrictMarginBelowViscosity :
  ∀ {A : AbsorptionArithmetic} →
  (M : PeriodicStrictDissipationMarginInputs A) →
  _≤_ A
    (_+_ A
      (_+_ A
        (_+_ A (nearTerm M) (farLowTerm M))
        (farHighTerm M))
      (strictMargin M))
    (viscosityBudget M)
periodicNonlinearPlusStrictMarginBelowViscosity {A = A} M =
  subst
    (λ rhs →
      _≤_ A
        (_+_ A
          (_+_ A
            (_+_ A (nearTerm M) (farLowTerm M))
            (farHighTerm M))
          (strictMargin M))
        rhs)
    (sym (viscositySplitsPaymentsAndMargin M))
    (additionMonotoneRight A
      (periodicNonlinearComponentsBelowPayments M))

periodicNonlinearBelowNonlinearPlusMargin :
  ∀ {A : AbsorptionArithmetic} →
  (M : PeriodicStrictDissipationMarginInputs A) →
  _≤_ A
    (_+_ A
      (_+_ A (nearTerm M) (farLowTerm M))
      (farHighTerm M))
    (_+_ A
      (_+_ A
        (_+_ A (nearTerm M) (farLowTerm M))
        (farHighTerm M))
      (strictMargin M))
periodicNonlinearBelowNonlinearPlusMargin {A = A} M =
  subst
    (λ lhs →
      _≤_ A lhs
        (_+_ A
          (_+_ A
            (_+_ A (nearTerm M) (farLowTerm M))
            (farHighTerm M))
          (strictMargin M)))
    (addZeroRightForMargin A
      (_+_ A
        (_+_ A (nearTerm M) (farLowTerm M))
        (farHighTerm M)))
    (additionMonotoneLeft A (strictMarginNonnegative M))

periodicNonlinearBelowViscosity :
  ∀ {A : AbsorptionArithmetic} →
  (M : PeriodicStrictDissipationMarginInputs A) →
  _≤_ A
    (_+_ A
      (_+_ A (nearTerm M) (farLowTerm M))
      (farHighTerm M))
    (viscosityBudget M)
periodicNonlinearBelowViscosity {A = A} M =
  ≤-trans A
    (periodicNonlinearBelowNonlinearPlusMargin M)
    (periodicNonlinearPlusStrictMarginBelowViscosity M)

periodicStrictMarginWitness :
  ∀ {A : AbsorptionArithmetic} →
  (M : PeriodicStrictDissipationMarginInputs A) →
  StrictMarginPositive M
periodicStrictMarginWitness = strictMarginPositive

------------------------------------------------------------------------
-- Status: the margin algebra is checked.  Constructing the concrete three
-- cutoff-uniform payments and a genuinely positive margin remains analytic.
------------------------------------------------------------------------

strictDissipationMarginAssemblyLevel : ProofLevel
strictDissipationMarginAssemblyLevel = machineChecked
