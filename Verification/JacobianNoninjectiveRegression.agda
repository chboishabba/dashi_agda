module Verification.JacobianNoninjectiveRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

-- The exact sparse-polynomial expansion and rational evaluations are executed
-- by scripts/check_jacobian_noninjective_example.py.  The logical implication
-- collision => noninjective is now proved separately in
-- DASHI.Algebra.Jacobian.CollisionImpliesNonInjective.

record ExactJacobianDiagnosticReceipt : Set where
  constructor receipt
  field
    ambientDimension : Nat
    determinantConstant : String
    determinantIdentityOK : Bool
    distinctWitnessCount : Nat
    commonImage : String
    fibreWitnessesOK : Bool
    sparsePolynomialKernelChecked : Bool
    exactEvaluationKernelChecked : Bool
    collisionImplicationKernelProved : Bool
    counterexamplePromotionRecorded : Bool
    dimensionTwoResolved : Bool

open ExactJacobianDiagnosticReceipt public

jacobianNoninjectiveExampleReceipt : ExactJacobianDiagnosticReceipt
jacobianNoninjectiveExampleReceipt =
  receipt
    3
    "-2"
    true
    3
    "(-1/4,0,0)"
    true
    false
    false
    true
    true
    false

kernelLogicalPromotionIsTrue :
  collisionImplicationKernelProved jacobianNoninjectiveExampleReceipt ≡ true
kernelLogicalPromotionIsTrue = refl

sparseExpansionRemainsExternal :
  sparsePolynomialKernelChecked jacobianNoninjectiveExampleReceipt ≡ false
sparseExpansionRemainsExternal = refl

dimensionTwoRemainsOpen :
  dimensionTwoResolved jacobianNoninjectiveExampleReceipt ≡ false
dimensionTwoRemainsOpen = refl
