module DASHI.Analysis.BishopPolynomialGeometricComparisonExact where

------------------------------------------------------------------------
-- BISHOP ABSOLUTE CONVERGENCE FROM STEP-V POLYNOMIAL/GEOMETRIC DOMINATION
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- The Yang--Mills Step-V lane already owns the finite argument
--
--   polynomially weighted term
--      <= M * (q')^n
--
-- once a direct eventual-ratio payment has been supplied.  Independently,
-- the pinned Murray/Bishop Sequence library already owns:
--
--   proposition-3-6-1 : a strict ratio bound gives series convergence
--   proposition-3-5   : comparison with a convergent majorant gives
--                       convergence.
--
-- This owner welds those two existing surfaces on the literal Bishop-real
-- carrier.  It does NOT construct the remaining application-specific
-- eventual-ratio inequality.  In particular, for Eisenstein degree 4/6 the
-- still-live leaf is the direct-ratio / polynomial-absorption payment.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_; proj₁)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as SeriesExt
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricInductionExact as Geometric
import DASHI.Physics.YangMills.BalabanStepVBishopFiniteGeometricExact as BishopStepV
import DASHI.Physics.YangMills.BalabanStepVPolynomialWeightedDominationExact as Polynomial
import DASHI.Physics.YangMills.BalabanStepVPolynomialPrefixTailDominationExact as PrefixTail
import DASHI.Physics.YangMills.BalabanStepVPolynomialDirectRatioExact as Direct

private
  K : StepV.OrderedSemiringKernel BishopReal.ℝ
  K = BishopStepV.bishopOrderedSemiringKernel

  L : Geometric.GeometricSemiringLaws K
  L = BishopStepV.bishopGeometricSemiringLaws

BishopPolynomialGeometricDomination :
  BishopReal.ℝ → Nat → Set₁
BishopPolynomialGeometricDomination ratio degree =
  Polynomial.PolynomialGeometricDomination K L ratio degree

majorantTerm :
  ∀ {ratio degree} →
  BishopPolynomialGeometricDomination ratio degree →
  Nat → BishopReal.ℝ
majorantTerm inputs index =
  BishopReal._*_
    (Polynomial.dominationConstant inputs)
    (StepV.power K
      (Polynomial.chosenLargerRatio inputs)
      index)

majorantTermNonnegative :
  ∀ {ratio degree}
    (inputs : BishopPolynomialGeometricDomination ratio degree)
    index →
  BishopReal.NonNegative (majorantTerm inputs index)
majorantTermNonnegative inputs index =
  BishopP.nonNegx,y⇒nonNegx*y
    (BishopP.0≤x⇒nonNegx
      (Polynomial.dominationConstantNonnegative inputs))
    (BishopP.0≤x⇒nonNegx
      (Geometric.powerNonnegative
        L
        (StepV.ratioNonnegative
          (Polynomial.largerRatioBound inputs))
        index))

majorantTermAbsEquivalent :
  ∀ {ratio degree}
    (inputs : BishopPolynomialGeometricDomination ratio degree)
    index →
  BishopReal._≃_
    (BishopReal.∣ majorantTerm inputs index ∣)
    (majorantTerm inputs index)
majorantTermAbsEquivalent inputs index =
  BishopP.nonNegx⇒∣x∣≃x
    (majorantTermNonnegative inputs index)

weightedTermAbsEquivalent :
  ∀ {ratio degree}
    (inputs : BishopPolynomialGeometricDomination ratio degree)
    index →
  BishopReal._≃_
    (BishopReal.∣ Polynomial.weightedTerm inputs index ∣)
    (Polynomial.weightedTerm inputs index)
weightedTermAbsEquivalent inputs index =
  BishopP.nonNegx⇒∣x∣≃x
    (BishopP.0≤x⇒nonNegx
      (Polynomial.weightedTermNonnegative inputs index))

majorantSuccessorEquivalent :
  ∀ {ratio degree}
    (inputs : BishopPolynomialGeometricDomination ratio degree)
    index →
  BishopReal._≃_
    (majorantTerm inputs (suc index))
    (BishopReal._*_
      (Polynomial.chosenLargerRatio inputs)
      (majorantTerm inputs index))
majorantSuccessorEquivalent inputs index =
  let open BishopP.ℝ-Solver
  in solve 3
    (λ constant largerRatio previousPower →
      constant ⊗ (largerRatio ⊗ previousPower)
      ⊜
      largerRatio ⊗ (constant ⊗ previousPower))
    BishopP.≃-refl
    (Polynomial.dominationConstant inputs)
    (Polynomial.chosenLargerRatio inputs)
    (StepV.power K
      (Polynomial.chosenLargerRatio inputs)
      index)

majorantSuccessorRatio :
  ∀ {ratio degree}
    (inputs : BishopPolynomialGeometricDomination ratio degree)
    index →
  BishopReal._≤_
    (BishopReal.∣ majorantTerm inputs (suc index) ∣)
    (BishopReal._*_
      (Polynomial.chosenLargerRatio inputs)
      (BishopReal.∣ majorantTerm inputs index ∣))
majorantSuccessorRatio inputs index =
  BishopP.≤-respʳ-≃
    (BishopP.*-cong
      BishopP.≃-refl
      (BishopP.≃-symm
        (majorantTermAbsEquivalent inputs index)))
    (BishopP.≤-respˡ-≃
      (majorantTermAbsEquivalent inputs (suc index))
      (BishopP.≤-reflexive
        (majorantSuccessorEquivalent inputs index)))

bishopGeometricMajorantConvergent :
  ∀ {ratio degree}
    (inputs : BishopPolynomialGeometricDomination ratio degree) →
  BishopReal._<_ BishopReal.0ℝ
    (Polynomial.chosenLargerRatio inputs) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf (majorantTerm inputs))
bishopGeometricMajorantConvergent inputs largerRatioPositive =
  BishopSequence.proposition-3-6-1
    ( largerRatioPositive
    , StepV.ratioBelowOne
        (Polynomial.largerRatioBound inputs)
    )
    (zero , λ index indexPastCutoff →
      majorantSuccessorRatio inputs index)

bishopPolynomialGeometricSeriesConvergent :
  ∀ {ratio degree}
    (inputs : BishopPolynomialGeometricDomination ratio degree) →
  BishopReal._<_ BishopReal.0ℝ
    (Polynomial.chosenLargerRatio inputs) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf
      (Polynomial.weightedTerm inputs))
bishopPolynomialGeometricSeriesConvergent inputs largerRatioPositive =
  BishopSequence.proposition-3-5
    (bishopGeometricMajorantConvergent
      inputs largerRatioPositive)
    (zero , λ index indexPastCutoff →
      BishopP.≤-respˡ-≃
        (weightedTermAbsEquivalent inputs index)
        (Polynomial.pointwisePolynomialGeometricDomination
          inputs index))

bishopPolynomialGeometricAbsoluteConvergent :
  ∀ {ratio degree}
    (inputs : BishopPolynomialGeometricDomination ratio degree) →
  BishopReal._<_ BishopReal.0ℝ
    (Polynomial.chosenLargerRatio inputs) →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (Polynomial.weightedTerm inputs)
bishopPolynomialGeometricAbsoluteConvergent inputs largerRatioPositive =
  let
    weightedConvergent =
      bishopPolynomialGeometricSeriesConvergent
        inputs largerRatioPositive

    weightedLimit = proj₁ weightedConvergent

    partialSumsEquivalent =
      SeriesExt.seriesPartialSumsCongruent
        (weightedTermAbsEquivalent inputs)
  in
  weightedLimit ,
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count-1) →
      BishopP.≃-symm
        (partialSumsEquivalent (suc count-1))})
    weightedConvergent

directRatioDomination :
  ∀ {ratio degree} →
  Direct.PolynomialDirectRatioInputs K L ratio degree →
  BishopPolynomialGeometricDomination ratio degree
directRatioDomination inputs =
  PrefixTail.polynomialGeometricDominationFromPrefixTail
    (Direct.polynomialPrefixTailFromDirectRatio inputs)

bishopAbsoluteConvergenceFromDirectRatio :
  ∀ {ratio degree}
    (inputs : Direct.PolynomialDirectRatioInputs K L ratio degree) →
  BishopReal._<_ BishopReal.0ℝ
    (Direct.chosenLargerRatio inputs) →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (Direct.weightedTerm inputs)
bishopAbsoluteConvergenceFromDirectRatio inputs largerRatioPositive =
  bishopPolynomialGeometricAbsoluteConvergent
    (directRatioDomination inputs)
    largerRatioPositive
