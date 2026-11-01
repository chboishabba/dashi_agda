module DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopPhiConvergenceExact where

------------------------------------------------------------------------
-- FINAL BISHOP LIMIT FOR THE BALANCED-FRACTRAN FIBONACCI RATIOS
--
-- Earlier owners prove, for the actual Bishop ratio sequence r_n,
--
--   (r_n - phi_B)(r_n - psi_B)  ~=  D_n,
--   D_n -> 0,
--   1/2 < r_n - psi_B.
--
-- This file closes the remaining constructive cancellation directly in the
-- vendored Bishop `ConvergesTo` API.  No inverse sequence or new completeness
-- principle is introduced.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (NonZero)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using (_/_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopGoldenRatioCarrierExact as Phi
import DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact as Ratio
import DASHI.Moonshine.GoldenRatioBishopQuadraticFactorisationBidiExact as Factor
import DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopDefectWeldExact as Defect
import DASHI.Moonshine.GoldenRatioBalancedFRACTRANConjugateLowerBoundExact as Lower

------------------------------------------------------------------------
-- 1. Actual same-object error / conjugate / product sequences.
------------------------------------------------------------------------

ratioSequence : Nat → BishopReal.ℝ
ratioSequence = Ratio.balancedFRACTRANBishopRatioSequence

phiError : Nat → BishopReal.ℝ
phiError n = BishopReal._-_ (ratioSequence n) Phi.bishopPhi

conjugateFactor : Nat → BishopReal.ℝ
conjugateFactor n = BishopReal._-_ (ratioSequence n) Factor.bishopPsi

factorProduct : Nat → BishopReal.ℝ
factorProduct n = BishopReal._*_ (phiError n) (conjugateFactor n)

factorProductEqualsDefect :
  (n : Nat) →
  BishopReal._≃_ (factorProduct n) (Defect.macroBishopDefect n)
factorProductEqualsDefect n =
  Factor.bishopPhiPsiFactorisation (ratioSequence n)

factorProductConvergesZero :
  BishopSequence._ConvergesTo_ factorProduct BishopReal.0ℝ
factorProductConvergesZero =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    {xs = Defect.macroBishopDefect}
    {ys = factorProduct}
    (λ n → BishopP.≃-symm (factorProductEqualsDefect n))
    (BishopReal.0ℝ , Defect.macroBishopDefectConvergesZero)

------------------------------------------------------------------------
-- 2. Generic half-separated factor cancellation:
--
--      1/2 < y  ==>  |x| <= 2 |xy|.
------------------------------------------------------------------------

two : BishopReal.ℝ
two = BishopReal._⋆ (+ 2 / 1)

twoNonnegative : BishopReal.NonNegative two
twoNonnegative =
  BishopP.0≤x⇒nonNegx
    (BishopP.p≤q⇒p⋆≤q⋆
      (+ 0 / 1) (+ 2 / 1)
      (ℚP.nonNegative⁻¹ (+ 2 / 1)))

halfSeparatedAbsCancellation :
  (x y : BishopReal.ℝ) →
  BishopReal._<_ Phi.half y →
  BishopReal._≤_
    (BishopReal.∣ x ∣)
    (BishopReal._*_ two (BishopReal.∣ BishopReal._*_ x y ∣))
halfSeparatedAbsCancellation x y halfBelowY =
  let
    absX = BishopReal.∣ x ∣
    absY = BishopReal.∣ y ∣

    absXNN : BishopReal.NonNegative absX
    absXNN = BishopP.nonNeg∣x∣ x

    zeroBelowHalf : BishopReal._<_ BishopReal.0ℝ Phi.half
    zeroBelowHalf = BishopP.posx⇒0<x Lower.halfPositive

    zeroBelowY : BishopReal._<_ BishopReal.0ℝ y
    zeroBelowY = BishopP.<-trans zeroBelowHalf halfBelowY

    yNN : BishopReal.NonNegative y
    yNN = BishopP.pos⇒nonNeg (BishopP.0<x⇒posx zeroBelowY)

    absYIsY : BishopReal._≃_ absY y
    absYIsY = BishopP.nonNegx⇒∣x∣≃x yNN

    halfAbsBelowYAbs :
      BishopReal._≤_
        (BishopReal._*_ Phi.half absX)
        (BishopReal._*_ y absX)
    halfAbsBelowYAbs =
      BishopP.*-monoʳ-≤-nonNeg
        (BishopP.<⇒≤ halfBelowY)
        absXNN

    yAbsToAbsProduct :
      BishopReal._≃_
        (BishopReal._*_ y absX)
        (BishopReal.∣ BishopReal._*_ x y ∣)
    yAbsToAbsProduct =
      let
        rotate :
          BishopReal._≃_
            (BishopReal._*_ y absX)
            (BishopReal._*_ absX y)
        rotate =
          let open BishopP.ℝ-Solver
          in solve 2
            (λ a b → a ⊗ b ⊜ b ⊗ a)
            BishopP.≃-refl y absX

        replaceY :
          BishopReal._≃_
            (BishopReal._*_ absX y)
            (BishopReal._*_ absX absY)
        replaceY =
          BishopP.*-cong BishopP.≃-refl (BishopP.≃-symm absYIsY)
      in
      BishopP.≃-trans
        rotate
        (BishopP.≃-trans
          replaceY
          (BishopP.≃-symm (BishopP.∣x*y∣≃∣x∣*∣y∣ x y)))

    halfAbsBelowAbsProduct :
      BishopReal._≤_
        (BishopReal._*_ Phi.half absX)
        (BishopReal.∣ BishopReal._*_ x y ∣)
    halfAbsBelowAbsProduct =
      BishopP.≤-respʳ-≃ yAbsToAbsProduct halfAbsBelowYAbs

    doubled :
      BishopReal._≤_
        (BishopReal._*_ two (BishopReal._*_ Phi.half absX))
        (BishopReal._*_ two (BishopReal.∣ BishopReal._*_ x y ∣))
    doubled =
      BishopP.*-monoˡ-≤-nonNeg halfAbsBelowAbsProduct twoNonnegative

    twoHalfAbsIsAbs :
      BishopReal._≃_
        (BishopReal._*_ two (BishopReal._*_ Phi.half absX))
        absX
    twoHalfAbsIsAbs =
      let open BishopP.ℝ-Solver
      in solve 1
        (λ a → (Κ (+ 2 / 1) ⊗ (Κ (+ 1 / 2) ⊗ a)) ⊜ a)
        BishopP.≃-refl absX
  in
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm twoHalfAbsIsAbs)
    doubled

------------------------------------------------------------------------
-- 3. Precision doubling identity.
------------------------------------------------------------------------

twoTimesHalfPrecision :
  (k : Nat) → .{{_ : NonZero k}} →
  BishopReal._≃_
    (BishopReal._*_ two (BishopReal._⋆ (+ 1 / (2 * k))))
    (BishopReal._⋆ (+ 1 / k))
twoTimesHalfPrecision k =
  let open BishopP.ℝ-Solver
  in solve 0
    (Κ (+ 2 / 1) ⊗ Κ (+ 1 / (2 * k)) ⊜ Κ (+ 1 / k))
    BishopP.≃-refl

------------------------------------------------------------------------
-- 4. Final convergence r_n -> phi_B.
------------------------------------------------------------------------

balancedFRACTRANRatiosConvergeToBishopPhi :
  BishopSequence._ConvergesTo_ ratioSequence Phi.bishopPhi
balancedFRACTRANRatiosConvergeToBishopPhi =
  let
    BishopSequence.con* product→zero = factorProductConvergesZero
  in
  BishopSequence.con* λ {(suc k-1) →
    let
      k = suc k-1
      precision = 2 * k

      instance
        precisionNonZero : NonZero precision
        precisionNonZero = _

      productWitness = product→zero precision
      Npred = proj₁ productWitness
      productBound = proj₂ productWitness
    in
    Npred , λ n nLarge →
      let
        productMinusZeroIsProduct :
          BishopReal._≃_
            (BishopReal._-_ (factorProduct n) BishopReal.0ℝ)
            (factorProduct n)
        productMinusZeroIsProduct =
          let open BishopP.ℝ-Solver
          in solve 1
            (λ p → p ⊖ Κ (+ 0 / 1) ⊜ p)
            BishopP.≃-refl (factorProduct n)

        productMagnitudeBound :
          BishopReal._≤_
            (BishopReal.∣ factorProduct n ∣)
            (BishopReal._⋆ (+ 1 / precision))
        productMagnitudeBound =
          BishopP.≤-respˡ-≃
            (BishopP.≃-symm
              (BishopP.∣-∣-cong productMinusZeroIsProduct))
            (productBound n nLarge)

        cancelled :
          BishopReal._≤_
            (BishopReal.∣ phiError n ∣)
            (BishopReal._*_ two (BishopReal.∣ factorProduct n ∣))
        cancelled =
          halfSeparatedAbsCancellation
            (phiError n)
            (conjugateFactor n)
            (Lower.halfBelowMacroMinusPsi n)

        scaledProductBound :
          BishopReal._≤_
            (BishopReal._*_ two (BishopReal.∣ factorProduct n ∣))
            (BishopReal._*_ two (BishopReal._⋆ (+ 1 / precision)))
        scaledProductBound =
          BishopP.*-monoˡ-≤-nonNeg productMagnitudeBound twoNonnegative

        toRequestedPrecision :
          BishopReal._≤_
            (BishopReal._*_ two (BishopReal._⋆ (+ 1 / precision)))
            (BishopReal._⋆ (+ 1 / k))
        toRequestedPrecision =
          BishopP.≤-reflexive (twoTimesHalfPrecision k)
      in
      BishopP.≤-trans
        cancelled
        (BishopP.≤-trans scaledProductBound toRequestedPrecision) }

------------------------------------------------------------------------
-- 5. Closure receipt.
------------------------------------------------------------------------

record BishopPhiConvergenceClosure : Set where
  constructor bishop-phi-convergence-closure
  field
    productFactorisationSameObject : Bool
    productConvergesZero : Bool
    conjugateFactorUniformlySeparated : Bool
    halfSeparatedCancellationExact : Bool
    ratioSequenceConvergesToExistingBishopPhi : Bool

canonicalBishopPhiConvergenceClosure : BishopPhiConvergenceClosure
canonicalBishopPhiConvergenceClosure =
  bishop-phi-convergence-closure true true true true true
