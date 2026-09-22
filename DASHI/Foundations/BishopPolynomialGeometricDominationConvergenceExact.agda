module DASHI.Foundations.BishopPolynomialGeometricDominationConvergenceExact where

------------------------------------------------------------------------
-- POLYNOMIAL-GEOMETRIC DOMINATION -> ACTUAL BISHOP SERIES CONVERGENCE
--
-- Reuses two existing ingredients:
--
--   1. Step-V proves a pointwise domination
--
--        w_n <= M * rho^n
--
--      with w_n >= 0, M >= 0 and 0 <= rho < 1.
--
--   2. Bishop's comparison theorem (Sequence.proposition-3-5) turns eventual
--      absolute domination by a convergent majorant into convergence.
--
-- The majorant M*rho^n converges by the same ratio-test argument as the plain
-- geometric series.  Therefore no direct ratio estimate for n^k r^n is needed
-- once Step-V polynomial domination has been constructed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricInductionExact as GeometricLaws
import DASHI.Physics.YangMills.BalabanStepVPolynomialWeightedDominationExact as Polynomial
import DASHI.Physics.YangMills.BalabanStepVBishopFiniteGeometricExact as BishopStepV
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as BishopGeometric
open import DASHI.Physics.YangMills.CompactLieProofLevel

scaledGeometricTerm :
  BishopReal.ℝ →
  BishopReal.ℝ →
  Nat →
  BishopReal.ℝ
scaledGeometricTerm constant ratio n =
  BishopReal._*_
    constant
    (BishopReal.pow ratio n)

record BishopScaledGeometricInputs
    (constant ratio : BishopReal.ℝ) : Set₁ where
  field
    constantNonnegative :
      BishopReal._≤_ BishopReal.0ℝ constant

    ratioInputs :
      BishopGeometric.BishopUnitIntervalRatio ratio

open BishopScaledGeometricInputs public

scaledGeometricNonnegative :
  ∀ {constant ratio} →
  BishopScaledGeometricInputs constant ratio →
  (n : Nat) →
  BishopReal.NonNegative
    (scaledGeometricTerm constant ratio n)
scaledGeometricNonnegative inputs n =
  BishopP.nonNegx,y⇒nonNegx*y
    (BishopP.0≤x⇒nonNegx
      (constantNonnegative inputs))
    (BishopGeometric.ratioPowerNonnegative
      (ratioInputs inputs)
      n)

scaledGeometricAbsIsTerm :
  ∀ {constant ratio} →
  BishopScaledGeometricInputs constant ratio →
  (n : Nat) →
  BishopReal._≃_
    (BishopReal.∣_∣
      (scaledGeometricTerm constant ratio n))
    (scaledGeometricTerm constant ratio n)
scaledGeometricAbsIsTerm inputs n =
  BishopP.nonNegx⇒∣x∣≃x
    (scaledGeometricNonnegative inputs n)

scaledGeometricSuccessor :
  ∀ constant ratio n →
  BishopReal._≃_
    (scaledGeometricTerm constant ratio (suc n))
    (BishopReal._*_
      ratio
      (scaledGeometricTerm constant ratio n))
scaledGeometricSuccessor constant ratio n =
  let open BishopP.ℝ-Solver
  in solve 3
    (λ c r p →
      c ⊗ (p ⊗ r)
      ⊜ r ⊗ (c ⊗ p))
    BishopP.≃-refl
    constant
    ratio
    (BishopReal.pow ratio n)

scaledGeometricSuccessorContractive :
  ∀ {constant ratio} →
  (inputs : BishopScaledGeometricInputs constant ratio) →
  (n : Nat) →
  BishopReal._≤_
    (BishopReal.∣_∣
      (scaledGeometricTerm constant ratio (suc n)))
    (BishopReal._*_
      ratio
      (BishopReal.∣_∣
        (scaledGeometricTerm constant ratio n)))
scaledGeometricSuccessorContractive {constant} {ratio} inputs n =
  BishopP.≤-respˡ-≃
    (BishopP.≃-trans
      (scaledGeometricAbsIsTerm inputs (suc n))
      (scaledGeometricSuccessor constant ratio n))
    (BishopP.≤-respʳ-≃
      (BishopP.*-congˡ ratio
        (BishopP.≃-symm
          (scaledGeometricAbsIsTerm inputs n)))
      BishopP.≤-refl)

scaledGeometricSeriesConvergent :
  ∀ {constant ratio} →
  BishopScaledGeometricInputs constant ratio →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf
      (scaledGeometricTerm constant ratio))
scaledGeometricSeriesConvergent {ratio = ratio} inputs =
  BishopSequence.proposition-3-6-1
    (BishopGeometric.ratioNonnegative (ratioInputs inputs) ,
      BishopGeometric.ratioBelowOne (ratioInputs inputs))
    (zero ,
      λ n _ →
        scaledGeometricSuccessorContractive inputs n)

------------------------------------------------------------------------
-- Step-V domination specialized to the concrete Bishop semiring.
------------------------------------------------------------------------

polynomialSeriesConvergentFromDomination :
  ∀ {ratio polynomialDegree} →
  (inputs :
    Polynomial.PolynomialGeometricDomination
      BishopStepV.bishopOrderedSemiringKernel
      BishopStepV.bishopGeometricSemiringLaws
      ratio
      polynomialDegree) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf
      (Polynomial.weightedTerm inputs))
polynomialSeriesConvergentFromDomination inputs =
  BishopSequence.proposition-3-5
    majorantConverges
    (zero ,
      λ n _ →
        BishopP.≤-respˡ-≃
          (BishopP.nonNegx⇒∣x∣≃x
            (BishopP.0≤x⇒nonNegx
              (Polynomial.weightedTermNonnegative inputs n)))
          (Polynomial.pointwisePolynomialGeometricDomination inputs n))
  where
  constant : BishopReal.ℝ
  constant = Polynomial.dominationConstant inputs

  largerRatio : BishopReal.ℝ
  largerRatio = Polynomial.chosenLargerRatio inputs

  largerRatioInputs :
    BishopGeometric.BishopUnitIntervalRatio largerRatio
  largerRatioInputs = record
    { BishopGeometric.ratioNonnegative =
        StepV.ratioNonnegative
          (Polynomial.largerRatioBound inputs)
    ; BishopGeometric.ratioBelowOne =
        StepV.ratioBelowOne
          (Polynomial.largerRatioBound inputs)
    }

  majorantInputs :
    BishopScaledGeometricInputs constant largerRatio
  majorantInputs = record
    { constantNonnegative =
        Polynomial.dominationConstantNonnegative inputs
    ; ratioInputs = largerRatioInputs
    }

  majorantConverges :
    BishopSequence._isConvergent
      (BishopSequence.SeriesOf
        (scaledGeometricTerm constant largerRatio))
  majorantConverges =
    scaledGeometricSeriesConvergent majorantInputs

------------------------------------------------------------------------
-- Direct-ratio / prefix-tail corollaries can now target actual convergence.
------------------------------------------------------------------------

record BishopPolynomialDominationConvergenceBoundary : Set where
  constructor bishop-polynomial-domination-convergence-boundary
  field
    scaledGeometricConvergencePaid : Bool
    bishopComparisonTheoremReused : Bool
    stepVPointwiseDominationImpliesSeriesConvergence : Bool
    directPolynomialSuccessorRatioStillRequired : Bool

open import Agda.Builtin.Bool using (Bool; true; false)
open BishopPolynomialDominationConvergenceBoundary public

canonicalBishopPolynomialDominationConvergenceBoundary :
  BishopPolynomialDominationConvergenceBoundary
canonicalBishopPolynomialDominationConvergenceBoundary =
  bishop-polynomial-domination-convergence-boundary
    true true true false

bishopScaledGeometricConvergenceLevel : ProofLevel
bishopScaledGeometricConvergenceLevel = machineChecked

bishopPolynomialDominationConvergenceLevel : ProofLevel
bishopPolynomialDominationConvergenceLevel = machineChecked
