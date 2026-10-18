module DASHI.Analysis.BishopGeometricMajorantSeriesConvergenceExact where

------------------------------------------------------------------------
-- BISHOP GEOMETRIC MAJORANT -> SERIES CONVERGENCE
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- The pinned Murray/Bishop sequence library already owns:
--
--   proposition-3-6-1 : ratio-test convergence
--   proposition-3-5   : comparison-test convergence
--
-- This owner composes them into the exact reusable theorem needed by the
-- Eisenstein, reduced-ghost, partition and similar analytic lanes:
--
--   0 < rho < 1
--   M >= 0
--   |a_n| <= M rho^n
--        ->
--   sum a_n converges.
--
-- No new completeness, quotient, or exponential authority is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

open import DASHI.Physics.YangMills.CompactLieProofLevel

scaledGeometricTerm :
  BishopReal.ℝ →
  BishopReal.ℝ →
  Nat →
  BishopReal.ℝ
scaledGeometricTerm scale ratio index =
  BishopReal._*_
    scale
    (BishopReal.pow ratio index)

ratioNonnegative :
  ∀ {ratio} →
  BishopReal._<_ BishopReal.0ℝ ratio →
  BishopReal.NonNegative ratio
ratioNonnegative ratioPositive =
  BishopP.0≤x⇒nonNegx (BishopP.<⇒≤ ratioPositive)

scaledGeometricTermNonnegative :
  ∀ {scale ratio} →
  BishopReal.NonNegative scale →
  BishopReal._<_ BishopReal.0ℝ ratio →
  ∀ index →
  BishopReal.NonNegative
    (scaledGeometricTerm scale ratio index)
scaledGeometricTermNonnegative scaleNonnegative ratioPositive index =
  BishopP.nonNegx,y⇒nonNegx*y
    scaleNonnegative
    (BishopSequence.nonNegx⇒nonNegxⁿ index
      (ratioNonnegative ratioPositive))

scaledGeometricAbsIsSelf :
  ∀ {scale ratio} →
  BishopReal.NonNegative scale →
  BishopReal._<_ BishopReal.0ℝ ratio →
  ∀ index →
  BishopReal._≃_
    (BishopReal.∣_∣ (scaledGeometricTerm scale ratio index))
    (scaledGeometricTerm scale ratio index)
scaledGeometricAbsIsSelf scaleNonnegative ratioPositive index =
  BishopP.nonNegx⇒∣x∣≃x
    (scaledGeometricTermNonnegative
      scaleNonnegative ratioPositive index)

scaledGeometricSuccessorFactorization :
  ∀ scale ratio index →
  BishopReal._≃_
    (scaledGeometricTerm scale ratio (suc index))
    (BishopReal._*_
      ratio
      (scaledGeometricTerm scale ratio index))
scaledGeometricSuccessorFactorization scale ratio index =
  let
    oldPower = BishopReal.pow ratio index
    open BishopP.ℝ-Solver
  in
  solve 3
    (λ scale′ ratio′ oldPower′ →
      scale′ ⊗ (oldPower′ ⊗ ratio′)
      ⊜ ratio′ ⊗ (scale′ ⊗ oldPower′))
    BishopP.≃-refl
    scale ratio oldPower

scaledGeometricSuccessorRatio :
  ∀ {scale ratio} →
  BishopReal.NonNegative scale →
  (ratioPositive : BishopReal._<_ BishopReal.0ℝ ratio) →
  ∀ index →
  BishopReal._≤_
    (BishopReal.∣_∣
      (scaledGeometricTerm scale ratio (suc index)))
    (BishopReal._*_
      ratio
      (BishopReal.∣_∣
        (scaledGeometricTerm scale ratio index)))
scaledGeometricSuccessorRatio
    {scale} {ratio} scaleNonnegative ratioPositive index =
  BishopP.≤-reflexive
    (BishopP.≃-trans
      (scaledGeometricAbsIsSelf
        scaleNonnegative ratioPositive (suc index))
      (BishopP.≃-trans
        (scaledGeometricSuccessorFactorization
          scale ratio index)
        (BishopP.*-congˡ
          (BishopP.≃-symm
            (scaledGeometricAbsIsSelf
              scaleNonnegative ratioPositive index)))))

scaledGeometricSeriesConvergent :
  ∀ (ratio scale : BishopReal.ℝ) →
  BishopReal._<_ BishopReal.0ℝ ratio →
  BishopReal._<_ ratio BishopReal.1ℝ →
  BishopReal.NonNegative scale →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf
      (scaledGeometricTerm scale ratio))
scaledGeometricSeriesConvergent
    ratio scale ratioPositive ratioBelowOne scaleNonnegative =
  BishopSequence.proposition-3-6-1
    (ratioPositive , ratioBelowOne)
    (zero , λ index indexAtLeastOne →
      scaledGeometricSuccessorRatio
        scaleNonnegative ratioPositive index)

seriesConvergentFromScaledGeometricMajorant :
  ∀ (terms : Nat → BishopReal.ℝ)
    (ratio scale : BishopReal.ℝ) →
  BishopReal._<_ BishopReal.0ℝ ratio →
  BishopReal._<_ ratio BishopReal.1ℝ →
  BishopReal.NonNegative scale →
  (∀ index →
    BishopReal._≤_
      (BishopReal.∣_∣ (terms index))
      (scaledGeometricTerm scale ratio index)) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf terms)
seriesConvergentFromScaledGeometricMajorant
    terms ratio scale ratioPositive ratioBelowOne
    scaleNonnegative pointwiseMajorant =
  BishopSequence.proposition-3-5
    (scaledGeometricSeriesConvergent
      ratio scale ratioPositive ratioBelowOne scaleNonnegative)
    (zero , λ {(suc index) indexAtLeastOne →
      pointwiseMajorant (suc index)})

bishopGeometricMajorantSeriesConvergenceLevel : ProofLevel
bishopGeometricMajorantSeriesConvergenceLevel = conditional
