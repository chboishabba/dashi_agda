module DASHI.Algebra.RamifiedLocalValuationSharpnessExact where

------------------------------------------------------------------------
-- GENERIC RAMIFIED LOCAL VALUATION SHARPNESS
--
-- This module isolates the algebraic content used in Dwork's local sharpness
-- argument once the genuine p-adic analytic factorization has been supplied.
--
-- If
--
--   coefficient = unit * branch^e,
--   v(unit) = 0,
--   v(branch) = 1,
--
-- and the valuation is multiplicative, then
--
--   v(coefficient) = e.
--
-- The theorem is deliberately generic: it does NOT assert that ramification
-- alone manufactures the factorization.  A domain adapter must provide the
-- source-native unit, local branch and coefficient factorization.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import DASHI.Core.Prelude
open import Data.Nat using (_+_; suc)
import Data.Nat.Properties as NatP

record MultiplicativeNatValuation {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  field
    one : A
    mul : A → A → A
    valuation : A → Nat
    valuationOne : valuation one ≡ 0
    valuationMul :
      (x y : A) → valuation (mul x y) ≡ valuation x + valuation y

open MultiplicativeNatValuation public

pow :
  {ℓ : Level} {A : Set ℓ} →
  MultiplicativeNatValuation A → A → Nat → A
pow V x 0 = one V
pow V x (suc n) = mul V x (pow V x n)

powValuation :
  {ℓ : Level} {A : Set ℓ} →
  (V : MultiplicativeNatValuation A) →
  (x : A) → (n : Nat) →
  valuation V (pow V x n) ≡ n * valuation V x
powValuation V x 0 = valuationOne V
powValuation V x (suc n)
  rewrite valuationMul V x (pow V x n)
        | powValuation V x n = refl

unitDepthOneBranchPowerDepth :
  {ℓ : Level} {A : Set ℓ} →
  (V : MultiplicativeNatValuation A) →
  (branch : A) →
  valuation V branch ≡ 1 →
  (e : Nat) →
  valuation V (pow V branch e) ≡ e
unitDepthOneBranchPowerDepth V branch branchDepth e =
  trans
    (powValuation V branch e)
    (trans
      (cong (λ d → e * d) branchDepth)
      (NatP.*-identityʳ e))

record RamifiedSharpCoefficient
    {ℓ : Level} {A : Set ℓ}
    (V : MultiplicativeNatValuation A)
    (ramificationIndex : Nat) : Set ℓ where
  field
    localUnit : A
    localBranch : A
    coefficient : A

    localUnitDepthZero : valuation V localUnit ≡ 0
    localBranchDepthOne : valuation V localBranch ≡ 1

    coefficientFactorization :
      coefficient
      ≡ mul V localUnit (pow V localBranch ramificationIndex)

open RamifiedSharpCoefficient public

ramifiedSharpCoefficientValuation :
  {ℓ : Level} {A : Set ℓ} →
  (V : MultiplicativeNatValuation A) →
  (e : Nat) →
  (S : RamifiedSharpCoefficient V e) →
  valuation V (coefficient S) ≡ e
ramifiedSharpCoefficientValuation V e S =
  trans
    (cong (valuation V) (coefficientFactorization S))
    (trans
      (valuationMul V (localUnit S) (pow V (localBranch S) e))
      (trans
        (cong
          (λ d → d + valuation V (pow V (localBranch S) e))
          (localUnitDepthZero S))
        (unitDepthOneBranchPowerDepth
          V (localBranch S) (localBranchDepthOne S) e)))

record RamifiedLocalValuationSharpnessBoundary : Set where
  field
    multiplicativeValuationAbstracted : Bool
    branchPowerValuationDerived : Bool
    zeroDepthUnitRequired : Bool
    depthOneLocalBranchRequired : Bool
    coefficientFactorizationRequired : Bool
    exactRamifiedDepthDerived : Bool
    ramificationAloneClaimedSufficient : Bool
    padicAnalyticFactorizationConstructedHere : Bool

canonicalRamifiedLocalValuationSharpnessBoundary :
  RamifiedLocalValuationSharpnessBoundary
canonicalRamifiedLocalValuationSharpnessBoundary = record
  { multiplicativeValuationAbstracted = true
  ; branchPowerValuationDerived = true
  ; zeroDepthUnitRequired = true
  ; depthOneLocalBranchRequired = true
  ; coefficientFactorizationRequired = true
  ; exactRamifiedDepthDerived = true
  ; ramificationAloneClaimedSufficient = false
  ; padicAnalyticFactorizationConstructedHere = false
  }
