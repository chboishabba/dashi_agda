module DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact where

------------------------------------------------------------------------
-- FIXED-DEGREE POLYNOMIAL × GEOMETRIC SERIES CONVERGENCE
--
-- SOURCE / ATTRIBUTION
--
-- The pinned Murray/Bishop library supplies the constructive ratio test,
-- strict rational density, reciprocal convergence, natural-power arithmetic,
-- and ordered-ring laws used below.
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- For every fixed natural degree k and every Bishop-real contraction
--
--     0 < r < 1,
--
-- this owner proves convergence of
--
--     sum_n n^k r^n.
--
-- The proof is the standard eventual-ratio argument, but every seam is made
-- explicit and constructive:
--
--   1. density constructs r < rho < 1;
--   2. r(1 + 1/(n+1))^k -> r, hence eventually < rho;
--   3. the canonical Bishop nat-real / reciprocal bridge identifies this
--      factor with the exact successor ratio of (n+1)^k r^(n+1);
--   4. Bishop proposition-3-6-1 closes convergence.
--
-- This is degree-parametric.  Eisenstein degrees 4 and 6 are specializations,
-- not separate analytic assumptions.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat.Base as Nat using (_≤_; s≤s)
open import Data.Rational.Unnormalised as ℚ using (0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopPolynomialSuccessorFactorLimitExact as Limit
import DASHI.Analysis.BishopStrictRatioInterpolationExact as Interpolate
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Reciprocal
import DASHI.Mathematics.NumberTheory.FiniteNatRationalEmbeddingExact as NatEmbed

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Canonical weighted term.
------------------------------------------------------------------------

polynomialGeometricTerm :
  BishopReal.ℝ →
  Nat →
  Nat →
  BishopReal.ℝ
polynomialGeometricTerm ratio degree index =
  BishopReal._*_
    (BishopReal.pow (NatReal.natReal index) degree)
    (BishopReal.pow ratio index)

successorFactor :
  BishopReal.ℝ →
  Nat →
  Nat →
  BishopReal.ℝ
successorFactor = Limit.polynomialSuccessorFactor

------------------------------------------------------------------------
-- Exact positive-natural successor scale:
--
--   (n+1) * (1 + 1/(n+1)) = n+2.
------------------------------------------------------------------------

positiveNatTimesOnePlusReciprocal :
  ∀ index →
  BishopReal._≃_
    (BishopReal._*_
      (NatReal.natReal (suc index))
      (Limit.onePlusReciprocal index))
    (NatReal.natReal (suc (suc index)))
positiveNatTimesOnePlusReciprocal index =
  let
    n = NatReal.natReal (suc index)
    reciprocal = Basel.reciprocalSequence index
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 2
      (λ n′ reciprocal′ →
        n′ ⊗ (Κ 1ℚᵘ ⊕ reciprocal′)
        ⊜ n′ ⊕ (reciprocal′ ⊗ n′))
      BishopP.≃-refl
      n reciprocal)
    (BishopP.≃-trans
      (BishopP.+-cong
        BishopP.≃-refl
        (Reciprocal.embeddedReciprocalNatCancels index))
      (BishopP.≃-symm
        (NatReal.natRealSuccessor (suc index))))

------------------------------------------------------------------------
-- Natural powers preserve multiplication.
------------------------------------------------------------------------

powerOfProduct :
  ∀ left right degree →
  BishopReal._≃_
    (BishopReal.pow (BishopReal._*_ left right) degree)
    (BishopReal._*_
      (BishopReal.pow left degree)
      (BishopReal.pow right degree))
powerOfProduct left right zero =
  BishopP.≃-symm (BishopP.*-identityˡ BishopReal.1ℝ)
powerOfProduct left right (suc degree) =
  let
    leftPower = BishopReal.pow left degree
    rightPower = BishopReal.pow right degree
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.*-congʳ
      (powerOfProduct left right degree))
    (solve 4
      (λ leftPower′ rightPower′ left′ right′ →
        (leftPower′ ⊗ rightPower′) ⊗ (left′ ⊗ right′)
        ⊜ (leftPower′ ⊗ left′) ⊗ (rightPower′ ⊗ right′))
      BishopP.≃-refl
      leftPower rightPower left right)

positiveNatPowerSuccessor :
  ∀ degree index →
  BishopReal._≃_
    (BishopReal.pow
      (NatReal.natReal (suc (suc index)))
      degree)
    (BishopReal._*_
      (BishopReal.pow (NatReal.natReal (suc index)) degree)
      (BishopReal.pow (Limit.onePlusReciprocal index) degree))
positiveNatPowerSuccessor degree index =
  BishopP.≃-trans
    (BishopP.pow-cong degree
      (BishopP.≃-symm
        (positiveNatTimesOnePlusReciprocal index)))
    (powerOfProduct
      (NatReal.natReal (suc index))
      (Limit.onePlusReciprocal index)
      degree)

------------------------------------------------------------------------
-- Exact weighted successor factorization.
------------------------------------------------------------------------

polynomialGeometricSuccessorFactorization :
  ∀ (ratio : BishopReal.ℝ) degree index →
  BishopReal._≃_
    (polynomialGeometricTerm ratio degree (suc (suc index)))
    (BishopReal._*_
      (successorFactor ratio degree index)
      (polynomialGeometricTerm ratio degree (suc index)))
polynomialGeometricSuccessorFactorization ratio degree index =
  let
    natPower = BishopReal.pow
      (NatReal.natReal (suc index)) degree
    scalePower = BishopReal.pow
      (Limit.onePlusReciprocal index) degree
    ratioPower = BishopReal.pow ratio (suc index)
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.*-congʳ
      (positiveNatPowerSuccessor degree index))
    (solve 4
      (λ natPower′ scalePower′ ratioPower′ ratio′ →
        (natPower′ ⊗ scalePower′) ⊗ (ratioPower′ ⊗ ratio′)
        ⊜ (ratio′ ⊗ scalePower′) ⊗
           (natPower′ ⊗ ratioPower′))
      BishopP.≃-refl
      natPower scalePower ratioPower ratio)

------------------------------------------------------------------------
-- Nonnegativity / absolute values.
------------------------------------------------------------------------

natRealNonnegative :
  ∀ index →
  BishopReal.NonNegative (NatReal.natReal index)
natRealNonnegative index =
  BishopP.0≤x⇒nonNegx
    (BishopP.p≤q⇒p⋆≤q⋆
      0ℚᵘ
      (NatEmbed.natAsRational index)
      (ℚP.nonNegative⁻¹ (NatEmbed.natAsRational index)))

polynomialGeometricTermNonnegative :
  ∀ {ratio} →
  BishopReal._<_ BishopReal.0ℝ ratio →
  ∀ degree index →
  BishopReal.NonNegative
    (polynomialGeometricTerm ratio degree index)
polynomialGeometricTermNonnegative ratioPositive degree index =
  BishopP.nonNegx,y⇒nonNegx*y
    (BishopSequence.nonNegx⇒nonNegxⁿ degree
      (natRealNonnegative index))
    (BishopSequence.nonNegx⇒nonNegxⁿ index
      (BishopP.0≤x⇒nonNegx (BishopP.<⇒≤ ratioPositive)))

polynomialGeometricAbsIsSelf :
  ∀ {ratio} →
  BishopReal._<_ BishopReal.0ℝ ratio →
  ∀ degree index →
  BishopReal._≃_
    (BishopReal.∣_∣
      (polynomialGeometricTerm ratio degree index))
    (polynomialGeometricTerm ratio degree index)
polynomialGeometricAbsIsSelf ratioPositive degree index =
  BishopP.nonNegx⇒∣x∣≃x
    (polynomialGeometricTermNonnegative
      ratioPositive degree index)

------------------------------------------------------------------------
-- Eventual ratio and convergence.
------------------------------------------------------------------------

eventualSuccessorRatio :
  ∀ {ratio larger : BishopReal.ℝ} degree →
  BishopReal._<_ BishopReal.0ℝ ratio →
  BishopReal._<_ ratio larger →
  Σ Nat (λ start →
    ∀ index →
    Nat._≤_ start index →
    BishopReal._≤_
      (BishopReal.∣_∣
        (polynomialGeometricTerm ratio degree (suc (suc index))))
      (BishopReal._*_
        larger
        (BishopReal.∣_∣
          (polynomialGeometricTerm ratio degree (suc index)))))
eventualSuccessorRatio
    {ratio} {larger} degree ratioPositive ratioBelowLarger
  with Limit.polynomialSuccessorFactorEventuallyBelow
    degree ratioBelowLarger
... | start , factorBelow =
  start ,
  λ index indexAtLeastStart →
    let
      oldTerm =
        polynomialGeometricTerm ratio degree (suc index)
      factor =
        successorFactor ratio degree index
      raw :
        BishopReal._≤_
          (BishopReal._*_ factor oldTerm)
          (BishopReal._*_ larger oldTerm)
      raw =
        BishopP.*-monoʳ-≤-nonNeg
          (BishopP.<⇒≤
            (factorBelow index indexAtLeastStart))
          (polynomialGeometricTermNonnegative
            ratioPositive degree (suc index))
    in
    BishopP.≤-respˡ-≃
      (BishopP.≃-trans
        (polynomialGeometricAbsIsSelf
          ratioPositive degree (suc (suc index)))
        (polynomialGeometricSuccessorFactorization
          ratio degree index))
      (BishopP.≤-respʳ-≃
        (BishopP.*-congˡ
          (BishopP.≃-symm
            (polynomialGeometricAbsIsSelf
              ratioPositive degree (suc index))))
        raw)

polynomialGeometricSeriesConvergent :
  ∀ (ratio : BishopReal.ℝ) degree →
  BishopReal._<_ BishopReal.0ℝ ratio →
  BishopReal._<_ ratio BishopReal.1ℝ →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf
      (polynomialGeometricTerm ratio degree))
polynomialGeometricSeriesConvergent
    ratio degree ratioPositive ratioBelowOne
  with Interpolate.interpolateStrictUnitRatio
    ratioPositive ratioBelowOne
... | larger ,
      largerPositive ,
      ratioBelowLarger ,
      largerBelowOne
  with eventualSuccessorRatio
    {ratio = ratio} {larger = larger}
    degree ratioPositive ratioBelowLarger
... | start , successorBound =
  BishopSequence.proposition-3-6-1
    (largerPositive , largerBelowOne)
    (start ,
      λ {(suc index) (s≤s indexAtLeastStart) →
        successorBound index indexAtLeastStart})

bishopPolynomialGeometricSeriesConvergenceLevel : ProofLevel
bishopPolynomialGeometricSeriesConvergenceLevel = conditional
